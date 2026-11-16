/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module

prelude
public import Std.Tactic.BVDecide.LRAT.Checker
public import Lean.CoreM
public import Std.Tactic.BVDecide.Syntax
import Lean.Meta.Tactic.BVDecide.LRAT.Trim
import Std.Tactic.BVDecide.LRAT.Parser
import Lean.Meta.Tactic.BVDecide.External
import Init.Data.String.TakeDrop
import Init.Data.String.Modify
import Init.Data.String.Legacy
import Init.System.Platform

/-!
This module contains the logic for loading LRAT proofs into Lean.
-/

namespace Lean.Meta.Tactic.BVDecide

open Std.Sat
open Std.Tactic.BVDecide

instance : ToExpr LRAT.IntAction where
  toExpr action :=
    let beta := mkApp (mkConst ``Array [.zero]) (mkConst ``Int)
    let alpha := mkConst ``Nat
    match action with
    | .addEmpty id hints =>
      mkApp4 (mkConst ``LRAT.Action.addEmpty [.zero, .zero]) beta alpha (toExpr id) (toExpr hints)
    | .addRup id c hints =>
      mkApp5 (mkConst ``LRAT.Action.addRup [.zero, .zero])
        beta
        alpha
        (toExpr id)
        (toExpr c)
        (toExpr hints)
    | .addRat id c pivot rupHints ratHints =>
      mkApp7 (mkConst ``LRAT.Action.addRat [.zero, .zero])
        beta
        alpha
        (toExpr id)
        (toExpr c)
        (toExpr pivot)
        (toExpr rupHints)
        (toExpr ratHints)
    | .del ids =>
      mkApp3 (mkConst ``LRAT.Action.del [.zero, .zero]) beta alpha (toExpr ids)
  toTypeExpr := mkConst ``LRAT.IntAction



/-- An LRAT proof read from a file. This will get parsed using native evaluation. -/
public abbrev LratCert := String

namespace LratCert

public def load (lratPath : System.FilePath) (trimProofs : Bool) : Core.CoreM (Array LRAT.IntAction) := do
  let proofInput ← IO.FS.readBinFile lratPath
  let proof ←
    withTraceNode `Meta.Tactic.sat (fun _ => return s!"Parsing LRAT file") do
      -- lazyPure to prevent compiler lifting
      let proof? ← IO.lazyPure (fun _ => LRAT.parseLRATProof proofInput)
      match proof? with
      | .ok proof => pure proof
      | .error err => throwError "SAT solver produced invalid LRAT: {err}"

  trace[Meta.Tactic.sat] s!"LRAT proof has {proof.size} steps before trimming"

  let proof ←
    if trimProofs then
      withTraceNode `Meta.Tactic.sat (fun _ => return "Trimming LRAT proof") do
        -- lazyPure to prevent compiler lifting
        let trimmed ← IO.lazyPure (fun _ => LRAT.trim proof)
        IO.ofExcept trimmed
    else
      pure proof

  trace[Meta.Tactic.sat] s!"LRAT proof has {proof.size} steps after trimming"
  return proof

public def ofFile (lratPath : System.FilePath) (trimProofs : Bool) : CoreM LratCert := do
  let proof ← LratCert.load lratPath trimProofs

  -- This is necessary because the proof might be in the binary format in which case we cannot
  -- store it as a string in the environment (yet) due to missing support for binary literals.
  let newProof := LRAT.lratProofToString proof
  return newProof

def isConGpuFalse (s : String) : Bool :=
  let low := s.trimAscii.copy.toLower
  low == "0" || low == "false" || low == "no"

def isConGpuTrue (s : String) : Bool :=
  let low := s.trimAscii.copy.toLower
  low == "1" || low == "true" || low == "yes"

def findOnPath (exe : String) : IO (Option System.FilePath) := do
  let some pathEnv ← IO.getEnv "PATH" | return none
  for dir in System.SearchPath.parse pathEnv do
    let cand : System.FilePath := dir / exe
    if ← cand.pathExists then
      return some cand
  return none

def lookupDefaultConGpu : IO System.FilePath := do
  if let some envBin := ← IO.getEnv "CON_GPU_BIN" then
    let t := envBin.trimAscii.copy
    if !t.isEmpty then
      return ⟨t⟩
  if let some appDir := (← IO.appPath).parent then
    let sibling := appDir / "con-gpu" |>.withExtension System.FilePath.exeExtension
    if ← sibling.pathExists then
      return sibling
  let exeName := if System.Platform.isWindows then "con-gpu.exe" else "con-gpu"
  if let some found ← findOnPath exeName then
    return found
  if !System.Platform.isWindows then
    let wslFallback : System.FilePath :=
      "/mnt/c/Users/devin/Desktop/lean/con-gpu/target/release/con-gpu.exe"
    if ← wslFallback.pathExists then
      return wslFallback
  return "con-gpu"

def resolveConGpuBin? : IO (Option System.FilePath) := do
  let bvEnv := (← IO.getEnv "LEAN_BV_DECIDE_CON_GPU").map (·.trimAscii.copy)
  let daemonEnv := (← IO.getEnv "CON_GPU_DAEMON_ADDR").map (·.trimAscii.copy)
  match bvEnv with
  | some "" | none =>
    match daemonEnv with
    | some addr =>
      if addr.isEmpty then return none
      else return some (← lookupDefaultConGpu)
    | none => return none
  | some raw =>
    if isConGpuFalse raw then
      return none
    else if isConGpuTrue raw then
      return some (← lookupDefaultConGpu)
    else
      return some ⟨raw⟩

def toConGpuPath (bin p : System.FilePath) : IO String := do
  if !System.Platform.isWindows && bin.toString.toLower.endsWith ".exe" && !p.toString.startsWith "/mnt/" then
    match ← (IO.Process.output { cmd := "wslpath", args := #["-w", p.toString], stdin := .null } |>.toBaseIO) with
    | .ok out =>
      if out.exitCode == 0 then
        return out.stdout.trimAscii.copy
      else
        return p.toString
    | .error _ => return p.toString
  else
    return p.toString

def readDimacsNumClauses? (cnfPath : System.FilePath) : IO (Option Nat) := do
  let contents ← IO.FS.readFile cnfPath
  for line in contents.splitOn "\n" do
    let s := line.trimAscii.copy
    if s.startsWith "p " then
      let parts := (s.splitOn " ").filter (!·.isEmpty)
      if parts[1]? == some "cnf" then
        if let some nStr := parts[3]? then
          if let some n := nStr.toNat? then
            return some n
  return none

/--
Renumber derived clause IDs in `proof` to a contiguous sequence starting at `numCnf + 1` so
indices match `Std.Tactic.BVDecide.LRAT.Internal.State.add`, and stop once `.addEmpty` is emitted.
-/
def compactLratIds (numCnf : Nat) (proof : Array LRAT.IntAction) :
    Array LRAT.IntAction × Bool := Id.run do
  let mut nextId := numCnf + 1
  let mut idMap : Std.HashMap Nat Nat := {}
  let mut out := Array.mkEmpty proof.size
  let mut changed := false
  let mapId (m : Std.HashMap Nat Nat) (x : Nat) : Nat :=
    if x ≤ numCnf then x else m.getD x x
  for action in proof do
    match action with
    | .addEmpty id hints =>
      if id != nextId then
        changed := true
      let newHints := hints.map (mapId idMap)
      out := out.push (.addEmpty nextId newHints)
      if out.size != proof.size then
        changed := true
      return (out, changed)
    | .addRup id c hints =>
      if id != nextId then
        idMap := idMap.insert id nextId
        changed := true
      let newHints := hints.map (mapId idMap)
      out := out.push (.addRup nextId c newHints)
      nextId := nextId + 1
    | .addRat id c pivot rupHints ratHints =>
      if id != nextId then
        idMap := idMap.insert id nextId
        changed := true
      let newRup := rupHints.map (mapId idMap)
      let newRat := ratHints.map fun (h, hs) => (mapId idMap h, hs.map (mapId idMap))
      out := out.push (.addRat nextId c pivot newRup newRat)
      nextId := nextId + 1
    | .del ids =>
      out := out.push (.del (ids.map (mapId idMap)))
  return (out, changed)

def tryConGpuTrimAndCheck? (cnfPath lratPath : System.FilePath) (trimProofs : Bool)
    (numCnf? : Option Nat := none) : CoreM (Option LratCert) := do
  let some bin ← resolveConGpuBin? | return none
  IO.FS.withTempDir fun tmpDir => do
    let trimmedOut := tmpDir / "trimmed.lrat"
    let cnfArg ← toConGpuPath bin cnfPath
    let lratArg ← toConGpuPath bin lratPath
    let outArg ← toConGpuPath bin trimmedOut
    let mut args := #["trim-check-lrat", cnfArg, lratArg, "--out", outArg]
    if !trimProofs then
      args := args.push "--no-trim"
    if let some backend := ← IO.getEnv "CON_GPU_BACKEND" then
      let b := backend.trimAscii.copy.toLower
      if b == "cpu" || b == "gpu" then
        args := args ++ #["--backend", b]
    if let some addr := ← IO.getEnv "CON_GPU_DAEMON_ADDR" then
      let addr := addr.trimAscii.copy
      if !addr.isEmpty then
        args := args ++ #["--daemon-addr", addr]
    match ← (IO.Process.output { cmd := bin.toString, args, stdin := .null } |>.toBaseIO) with
    | .error err =>
      trace[Meta.Tactic.sat] "con-gpu trim-check-lrat unavailable ({err}); falling back to Lean LRAT checker"
      return none
    | .ok out =>
      if out.exitCode == 0 then
        if ← trimmedOut.pathExists then
          let rawBytes ← IO.FS.readBinFile trimmedOut
          let parsed? ← IO.lazyPure (fun _ => LRAT.parseLRATProof rawBytes)
          match parsed? with
          | .error err =>
            trace[Meta.Tactic.sat] "con-gpu trimmed LRAT failed parse ({err}); falling back to Lean LRAT checker"
            return none
          | .ok proof =>
            let some numCnf ← (match numCnf? with | some n => pure (some n) | none => readDimacsNumClauses? cnfPath)
              | return none
            let (compacted, changed) := compactLratIds numCnf proof
            let cert :=
              if changed then
                LRAT.lratProofToString compacted
              else
                String.fromUTF8! rawBytes
            trace[Meta.Tactic.sat] "con-gpu trim-check-lrat verified and trimmed LRAT certificate"
            return some cert
        else
          trace[Meta.Tactic.sat] "con-gpu trim-check-lrat exited 0 without output file; falling back to Lean LRAT checker"
          return none
      else if out.exitCode == 1 then
        let detail := s!"{out.stdout.trimAscii}\n{out.stderr.trimAscii}".trimAscii.copy
        throwError "con-gpu REJECTED unsound LRAT certificate: {detail}"
      else
        let detail := s!"{out.stdout.trimAscii}\n{out.stderr.trimAscii}".trimAscii.copy
        trace[Meta.Tactic.sat] "con-gpu trim-check-lrat declined (exit {out.exitCode}): {detail}; falling back to Lean LRAT checker"
        return none

public def ofFileWithCnf (cnfPath lratPath : System.FilePath) (trimProofs : Bool)
    (numCnf? : Option Nat := none) : CoreM LratCert := do
  if let some cert ← tryConGpuTrimAndCheck? cnfPath lratPath trimProofs numCnf? then
    return cert
  ofFile lratPath trimProofs

end LratCert

/--
Run an external SAT solver on the `CNF` to obtain an LRAT proof.

This will obtain an `LratCert` if the formula is UNSAT and throw errors otherwise.
-/
public def runExternal (cnf : CNF Nat) (solver : System.FilePath) (lratPath : System.FilePath)
    (trimProofs : Bool) (timeout : Nat) (binaryProofs : Bool) (solverMode : Elab.Tactic.BVDecide.SolverMode) :
    CoreM (Except (Array (Bool × Nat)) LratCert) := do
  IO.FS.withTempFile fun cnfHandle cnfPath => do
    withTraceNode `Meta.Tactic.sat (fun _ => return "Serializing SAT problem to DIMACS file") do
      -- lazyPure to prevent compiler lifting
      cnfHandle.putStr  (← IO.lazyPure (fun _ => cnf.dimacs))
      cnfHandle.flush

    let res ←
      withTraceNode `Meta.Tactic.sat (fun _ => return "Running SAT solver") do
        External.satQuery solver cnfPath lratPath timeout binaryProofs solverMode
    if let .sat assignment := res then
      return .error assignment

    let lratProof ←
      withTraceNode `Meta.Tactic.sat (fun _ => return "Obtaining LRAT certificate") do
        LratCert.ofFileWithCnf cnfPath lratPath trimProofs (some cnf.clauses.size)

    return .ok lratProof


end Lean.Meta.Tactic.BVDecide
