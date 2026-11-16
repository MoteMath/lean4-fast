/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Sebastian Ullrich, Mac Malone, Siddharth Bhat
-/
module

prelude
public import Lake.Util.Log
public import Std.Sync.Semaphore
import Lake.Util.Proc
import Lake.Util.FilePath
import Lake.Util.IO
import Lake.Util.Url
import Init.Data.String.Search
import Init.Data.String.TakeDrop
import Init.Data.String.Modify
import Init.System.Platform
import Lean.CoreM
import Lean.Compiler.Options

/-! # Common Build Actions
Low level actions to build common Lean artifacts via the Lean toolchain.
-/

open System
open Lean hiding SearchPath

namespace Lake

public def compileLeanIR
  (setupFile irFile cFile : FilePath)
  (leanPath : SearchPath := [])
  (leanir : FilePath := "leanir")
: LogIO Unit := do
  createParentDirs irFile
  createParentDirs cFile
  proc {
    cmd := leanir.toString
    args := #[setupFile.toString, irFile.toString, cFile.toString]
    env := #[("LEAN_PATH", leanPath.toString)]
  }

def isTruthyEnv (val? : Option String) : Bool :=
  match val? with
  | some s =>
    let low := s.trimAscii.copy.toLower
    low == "1" || low == "true" || low == "yes"
  | none => false

def toExternalVerifierPath (verifier p : FilePath) : BaseIO String := do
  let isExe := verifier.toString.toLower.endsWith ".exe"
  if !System.Platform.isWindows && isExe && !p.toString.startsWith "/mnt/" then
    match ← (IO.Process.output { cmd := "wslpath", args := #["-w", p.toString] } |>.toBaseIO) with
    | .ok out =>
      if out.exitCode == 0 then
        return out.stdout.trimAscii.copy
      else
        return p.toString
    | .error _ => return p.toString
  else
    return p.toString

def formatConGpuLoadPaths? (verifier : FilePath) (leanPath : SearchPath) : BaseIO (Option String) := do
  let isExe := verifier.toString.toLower.endsWith ".exe"
  let wslExe := !System.Platform.isWindows && isExe
  let mut parts : Array String := #[]
  for dir in leanPath do
    let skipLinuxStdlib ←
      if wslExe && !dir.toString.startsWith "/mnt/" then
        (dir / "Init.olean").pathExists
      else
        pure false
    if !skipLinuxStdlib then
      parts := parts.push (← toExternalVerifierPath verifier dir)
  if parts.isEmpty then
    return none
  else
    return some (SearchPath.separator.toString.intercalate parts.toList)

public def compileLeanModule
  (leanFile relLeanFile : FilePath)
  (setup : ModuleSetup) (setupFile : FilePath)
  (arts : ModuleArtifacts)
  (leanArgs : Array String := #[])
  (leanPath : SearchPath := [])
  (lean : FilePath := "lean")
  (leanWrapper? : Option FilePath := none)
  (externalVerifier? : Option FilePath := none)
  (spawnSem? : Option Std.Semaphore := none)
  (offloadProc : Bool := true)
: LogIO Unit := do
  let mut args := leanArgs.push leanFile.toString
  if let some oleanFile := arts.olean? then
    createParentDirs oleanFile
    args := args ++ #["-o", oleanFile.toString]
  if let some ileanFile := arts.ilean? then
    createParentDirs ileanFile
    args := args ++ #["-i", ileanFile.toString]
  let opts := setup.options.toOptions
  let postponeCompile := setup.isModule && Compiler.compiler.postponeCompile.get opts
  if !postponeCompile then
    if let some cFile := arts.c? then
      createParentDirs cFile
      args := args ++ #["-c", cFile.toString]
  if let some bcFile := arts.bc? then
    createParentDirs bcFile
    args := args ++ #["-b", bcFile.toString]
  createParentDirs setupFile
  IO.FS.writeFile setupFile (toJson setup).pretty
  args := args ++ #["--setup", setupFile.toString]
  args := args.push "--json"
  let cmd := match leanWrapper? with
    | some w => w.toString
    | none => lean.toString
  let childLeanThreads? := (← IO.getEnv "LAKE_CHILD_LEAN_THREADS").bind fun s =>
    let t := s.trimAscii.copy
    if t.isEmpty then none else some t
  let mut childEnv : Array (String × Option String) := #[
    ("LEAN_PATH", some leanPath.toString),
    ("LEAN_BIN", some lean.toString)
  ]
  if let some t := childLeanThreads? then
    if t == "0" then
      childEnv := childEnv.push ("LEAN_NUM_THREADS", none)
    else
      childEnv := childEnv.push ("LEAN_NUM_THREADS", some t)
  let runCompile (useOffload : Bool) : LogIO Unit := do
    withLogErrorPos do
    let procArgs : IO.Process.SpawnArgs := {
      args
      cmd
      env := childEnv
    }
    let out ←
      if useOffload then
        -- Offload blocking OS pipe reads / waitpid to a dedicated thread so Lake pool workers wait via task_manager::wait_for.
        let outTask ← BaseIO.asTask (prio := .dedicated) <|
          (rawProc procArgs).run (← takeLog)
        match (← (IO.wait outTask : BaseIO _)) with
        | .ok out log =>
          set log
          pure out
        | .error e log =>
          set log
          throw e
      else
        rawProc procArgs
    let outLogPos ← getLogPos
    unless out.stdout.isEmpty do
      let txt ← out.stdout.split '\n' |>.foldM (init := "") fun (txt : String) ln => do
        let ln := ln.copy
        if let .ok (msg : SerialMessage) := Json.parse ln >>= fromJson? then
          unless txt.isEmpty do
            logInfo s!"stdout:\n{txt}"
          let msg := {msg with fileName := mkRelPathString relLeanFile}
          logSerialMessage msg
          return txt
        else if txt.isEmpty && ln.isEmpty then
          return txt
        else
          return txt ++ ln ++ "\n"
      unless txt.isEmpty do
        logInfo s!"stdout:\n{txt}"
    unless out.stderr.isEmpty do
      logInfo s!"stderr:\n{out.stderr.trimAscii}"
    -- Elide the generic "Lean exited with code 1" when Lean already
    -- reported errors (the usual compiler-failure case). Keep it for other
    -- nonzero codes, for code 1 without diagnostics, and for the anomalous
    -- case where Lean logs errors but exits successfully.
    -- See https://github.com/leanprover/lean4/issues/10825
    let hasErrors := (← getLog).takeFrom outLogPos |>.any (·.level matches .error)
    if out.exitCode = 1 && hasErrors then
      failure
    else if out.exitCode ≠ 0 || hasErrors then
      error s!"Lean exited with code {out.exitCode}"
    if let some verifier := externalVerifier? then
      if let some oleanFile := arts.olean? then
        let daemonAddr? := (← IO.getEnv "CON_GPU_DAEMON_ADDR").bind fun s =>
          let t := s.trimAscii.copy
          if t.isEmpty then none else some t
        let batchQueueRaw? ← IO.getEnv "CON_GPU_BATCH_QUEUE"
        let batchQueue := isTruthyEnv batchQueueRaw?
        let bvDecideConGpu? ← IO.getEnv "LEAN_BV_DECIDE_CON_GPU"
        let trustBvAx := isTruthyEnv (← IO.getEnv "LAKE_VERIFY_TRUST_BV_AX")
        let strictVerify := isTruthyEnv (← IO.getEnv "LAKE_VERIFY_STRICT")
        let backendOpt? := (← IO.getEnv "CON_GPU_BACKEND").bind fun s =>
          let low := s.trimAscii.copy.toLower
          if low == "cpu" || low == "gpu" || low == "hybrid" then some low else none
        let oleanArg ← toExternalVerifierPath verifier oleanFile
        let mut verifierArgs : Array String := #["verify", oleanArg]
        if let some addr := daemonAddr? then
          verifierArgs := verifierArgs ++ #["--daemon-addr", addr]
        if trustBvAx then
          verifierArgs := verifierArgs.push "--trust-bv-decide-axioms"
        if batchQueue then
          verifierArgs := verifierArgs.push "--queue"
        if let some b := backendOpt? then
          verifierArgs := verifierArgs ++ #["--backend", b]
        if let some loadPathsStr := ← formatConGpuLoadPaths? verifier leanPath then
          verifierArgs := verifierArgs ++ #["--load-paths", loadPathsStr]
        let verifierEnv : Array (String × Option String) := #[
          ("LEAN_PATH", some leanPath.toString),
          ("CON_GPU_DAEMON_ADDR", daemonAddr?),
          ("CON_GPU_BATCH_QUEUE", batchQueueRaw?),
          ("LEAN_BV_DECIDE_CON_GPU", bvDecideConGpu?)
        ]
        let spawnArgs : IO.Process.SpawnArgs := {
          cmd := verifier.toString
          args := verifierArgs
          env := verifierEnv
        }
        logVerbose (mkCmdLog spawnArgs)
        let runVerif : BaseIO (Except IO.Error IO.Process.Output) := do
          if useOffload then
            let task ← BaseIO.asTask (prio := .dedicated) (IO.Process.output spawnArgs |>.toBaseIO)
            IO.wait task
          else
            IO.Process.output spawnArgs |>.toBaseIO
        match ← runVerif with
        | .error err =>
          removeFileIfExists oleanFile
          error s!"failed to execute external verifier '{verifier}': {err}"
        | .ok vOut =>
          if vOut.exitCode == 0 then
            logOutput vOut logVerbose
          else if vOut.exitCode == 2 then
            logOutput vOut (if strictVerify then logInfo else logWarning)
            if strictVerify then
              removeFileIfExists oleanFile
              error s!"external verifier '{verifier}' declined '{oleanFile}' (exit 2, strict mode)"
            else
              logWarning s!"external verifier '{verifier}' declined '{oleanFile}' (exit 2); keeping '.olean'"
          else
            logOutput vOut logInfo
            removeFileIfExists oleanFile
            let detail := s!"{vOut.stdout.trimAscii}\n{vOut.stderr.trimAscii}".trimAscii.copy
            error s!"external verifier '{verifier}' failed on '{oleanFile}' (exit {vOut.exitCode}){if detail.isEmpty then "" else s!": {detail}"}"
  if let some sem := spawnSem? then
    let p ← (sem.acquire : BaseIO (IO.Promise Unit))
    let log ← takeLog
    let task ← BaseIO.bindTask p.result! fun _ => BaseIO.asTask (prio := .dedicated) do
      try
        (runCompile false).run log
      finally
        (sem.release : BaseIO Unit)
    match (← (IO.wait task : BaseIO _)) with
    | .ok () log => set log
    | .error e log => set log; throw e
  else
    runCompile offloadProc

public def compileO
  (oFile srcFile : FilePath)
  (moreArgs : Array String := #[]) (compiler : FilePath := "cc")
: LogIO Unit := do
  createParentDirs oFile
  proc {
    cmd := compiler.toString
    args := #["-c", "-o", oFile.toString, srcFile.toString] ++ moreArgs
  }

public def mkArgs (basePath : FilePath) (args : Array String) : LogIO (Array String) := do
  -- Use response file to avoid potentially exceeding CLI length limits.
  -- On Windows this is always needed; on macOS/Linux this is needed for large
  -- projects like Mathlib where the number of object files exceeds ARG_MAX.
  let rspFile := basePath.addExtension "rsp"
  let h ← IO.FS.Handle.mk rspFile .write
  args.forM fun arg =>
    -- Escape special characters
    let arg := arg.foldl (init := "") fun s c =>
      if c == '\\' || c == '"' then
        s.push '\\' |>.push c
      else
        s.push c
    h.putStr s!"\"{arg}\"\n"
  return #[s!"@{rspFile}"]

public def compileStaticLib
  (libFile : FilePath) (oFiles : Array FilePath)
  (ar : FilePath := "ar") (thin := false)
: LogIO Unit := do
  createParentDirs libFile
  -- `ar rcs` does not remove old files from the archive, so it must be deleted first
  removeFileIfExists libFile
  let args := #["rcs"]
  let args := if thin then args.push "--thin" else args
  let args := args.push libFile.toString ++ (← mkArgs libFile <| oFiles.map toString)
  proc {cmd := ar.toString, args}

public def compileSharedLib
  (libFile : FilePath) (linkArgs : Array String)
  (linker : FilePath := "cc") (macosxDeploymentTarget? : Option String := none)
: LogIO Unit := do
  createParentDirs libFile
  proc {
    cmd := linker.toString
    args := #["-shared", "-o", libFile.toString] ++ (← mkArgs libFile linkArgs)
    -- See `BuildConfig.macosxDeploymentTarget?` for details
    env := macosxDeploymentTarget?.elim #[] fun ver => #[("MACOSX_DEPLOYMENT_TARGET", some ver)]
  }

public def compileExe
  (binFile : FilePath) (linkArgs : Array String)
  (linker : FilePath := "cc") (macosxDeploymentTarget? : Option String := none)
: LogIO Unit := do
  createParentDirs binFile
  proc {
    cmd := linker.toString
    args := #["-o", binFile.toString] ++ (← mkArgs binFile linkArgs)
    -- See `BuildConfig.macosxDeploymentTarget?` for details
    env :=  macosxDeploymentTarget?.elim #[] fun ver => #[("MACOSX_DEPLOYMENT_TARGET", some ver)]
  }

/-- Download a file using `curl`, clobbering any existing file. -/
public def download
  (url : String) (file : FilePath) (headers : Array String := #[])
: LogIO PUnit := do
  createParentDirs file
  -- No `--clobber` to be compatible with older versions of `curl`.
  removeFileIfExists file
  let args := #["-s", "-S", "-f", "-o", file.toString, "-L", url]
  let args := headers.foldl (init := args) (· ++ #["-H", ·])
  proc (quiet := true) {cmd := ← Internal.getCurl, args}

/-- Unpack an archive `file` using `tar` into the directory `dir`. -/
public def untar (file : FilePath) (dir : FilePath) (gzip := true) : LogIO PUnit := do
  IO.FS.createDirAll dir
  let mut opts := "-xvv"
  if gzip then
    opts := opts.push 'z'
  proc (quiet := true) {
    cmd := "tar",
    args := #[opts, "-f", file.toString, "-C", dir.toString]
  }

/-- Pack a directory `dir` using `tar` into the archive `file`. -/
public def tar
  (dir : FilePath) (file : FilePath)
  (gzip := true) (excludePaths : Array FilePath := #[])
: LogIO PUnit := do
  createParentDirs file
  let mut args := #["-cvv"]
  if gzip then
    args := args.push "-z"
  for path in excludePaths do
    args := args.push s!"--exclude={path}"
  proc (quiet := true) {
    cmd := "tar"
    args := args ++ #["-f", file.toString, "-C", dir.toString, "."]
    -- don't pack `._` files on MacOS
    env := if Platform.isOSX then #[("COPYFILE_DISABLE", "true")] else #[]
  }
