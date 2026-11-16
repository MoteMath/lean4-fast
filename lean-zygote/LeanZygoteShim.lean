import Lean.Parser.Module
import Lean.Elab.Import
import Lean.Elab.Frontend
import Lean.Language.Lean
import Lean.Compiler.LCNF.EmitC
import Lean.Setup
import Lean.Util.Path
import Lean.Data.Json

open Lean System

namespace LeanZygote

@[extern "lean_internal_set_max_memory"]
private opaque setMaxMemory (max : USize) : BaseIO Unit

@[extern "lean_internal_set_max_heartbeat"]
private opaque setMaxHeartbeat (max : USize) : BaseIO Unit

@[extern "lean_internal_set_thread_stack_size"]
private opaque setThreadStackSize (sz : USize) : BaseIO Unit

structure ZygoteSnapshotMeta where
  imports : Array Import
  isModule : Bool
  trustLevel : UInt32
  loadedOLeans : Std.HashMap Name (String × String × Option IO.FS.SystemTime)
  directRoots : Array (Name × String × Option IO.FS.SystemTime)

structure ZygoteSnapshot where
  env : Environment
  level : OLeanLevel
  info : ZygoteSnapshotMeta

private structure MetaTimeDto where
  sec : Int
  nsec : Nat
  deriving ToJson, FromJson

private structure LoadedOLeanDto where
  modName : Name
  rawPath : String
  realPath : String
  mtime? : Option MetaTimeDto
  deriving ToJson, FromJson

private structure DirectRootDto where
  modName : Name
  realPath : String
  mtime? : Option MetaTimeDto
  deriving ToJson, FromJson

private structure SnapshotMetaDto where
  imports : Array Import
  isModule : Bool
  trustLevel : Nat
  loadedOLeans : Array LoadedOLeanDto
  directRoots : Array DirectRootDto
  deriving ToJson, FromJson

private def toMetaTimeDto (mt? : Option IO.FS.SystemTime) : Option MetaTimeDto :=
  mt?.map fun mt => { sec := mt.sec, nsec := mt.nsec.toNat }

private def ofMetaTimeDto (dto? : Option MetaTimeDto) : Option IO.FS.SystemTime :=
  dto?.map fun dto => { sec := dto.sec, nsec := UInt32.ofNat dto.nsec }

private def toSnapshotMetaDto (info : ZygoteSnapshotMeta) : SnapshotMetaDto :=
  let oleanArr := info.loadedOLeans.toArray.map fun (modName, rawPath, realPath, mt?) =>
    { modName, rawPath, realPath, mtime? := toMetaTimeDto mt? }
  let rootArr := info.directRoots.map fun (modName, realPath, mt?) =>
    { modName, realPath, mtime? := toMetaTimeDto mt? }
  { imports := info.imports
    isModule := info.isModule
    trustLevel := info.trustLevel.toNat
    loadedOLeans := oleanArr
    directRoots := rootArr }

private def ofSnapshotMetaDto (dto : SnapshotMetaDto) : ZygoteSnapshotMeta :=
  let oleanMap := dto.loadedOLeans.foldl (init := {}) fun acc e =>
    acc.insert e.modName (e.rawPath, e.realPath, ofMetaTimeDto e.mtime?)
  let rootArr := dto.directRoots.map fun e =>
    (e.modName, e.realPath, ofMetaTimeDto e.mtime?)
  { imports := dto.imports
    isModule := dto.isModule
    trustLevel := UInt32.ofNat dto.trustLevel
    loadedOLeans := oleanMap
    directRoots := rootArr }

private structure ParsedCompileArgs where
  fileName : String
  oleanFileName? : Option FilePath := none
  ileanFileName? : Option FilePath := none
  cFileName? : Option FilePath := none
  setupFileName? : Option FilePath := none
  rootDir? : Option FilePath := none
  trustLevel : UInt32 := 0
  cliModule : Bool := false
  jsonOutput : Bool := false
  printStats : Bool := false
  maxMemoryMb? : Option Nat := none
  timeout? : Option Nat := none
  errorOnKinds : Array Name := #[]
  configOpts : Array (Name × String) := #[]
  deriving Inhabited

private def takeFlagArg (argv : Array String) (i : Nat) (shortPref longPref : String) : Option (String × Nat) :=
  let arg := argv[i]!
  if arg == shortPref || arg == longPref then
    if h : i + 1 < argv.size then
      some (argv[i + 1], i + 2)
    else
      none
  else if arg.startsWith (longPref ++ "=") then
    some ((arg.drop (longPref.length + 1)).copy, i + 1)
  else if shortPref.length == 2 && arg.startsWith shortPref && arg.length > 2 then
    some ((arg.drop 2).copy, i + 1)
  else
    none

private def splitEq (s : String) : Option (Name × String) :=
  let pos := s.find '='
  if h : pos.IsAtEnd then
    none
  else
    let k := s.sliceTo pos |>.copy.toName
    let v := s.sliceFrom (pos.next h) |>.copy
    some (k, v)

private partial def parseCompileArgs (argv : Array String) : Option ParsedCompileArgs := Id.run do
  let mut res : ParsedCompileArgs := { fileName := "" }
  let mut positional : Array String := #[]
  let mut i := 0
  while i < argv.size do
    let arg := argv[i]!
    if arg == "--" then
      for j in (i + 1)...argv.size do
        positional := positional.push argv[j]!
      break
    else if arg == "--json" || arg == "-J" then
      res := { res with jsonOutput := true }
      i := i + 1
    else if arg == "--module" then
      res := { res with cliModule := true }
      i := i + 1
    else if arg == "--stats" then
      res := { res with printStats := true }
      i := i + 1
    else if arg == "-q" || arg == "--quiet" then
      i := i + 1
    else if let some (v, next) := takeFlagArg argv i "-o" "--olean" then
      res := { res with oleanFileName? := some ⟨v⟩ }
      i := next
    else if let some (v, next) := takeFlagArg argv i "-i" "--ilean" then
      res := { res with ileanFileName? := some ⟨v⟩ }
      i := next
    else if let some (v, next) := takeFlagArg argv i "-c" "--c" <|> takeFlagArg argv i "-c" "--cfile" then
      res := { res with cFileName? := some ⟨v⟩ }
      i := next
    else if let some (v, next) := takeFlagArg argv i "" "--setup" then
      res := { res with setupFileName? := some ⟨v⟩ }
      i := next
    else if let some (v, next) := takeFlagArg argv i "-R" "--root" then
      res := { res with rootDir? := some ⟨v⟩ }
      i := next
    else if let some (v, next) := takeFlagArg argv i "-t" "--trust" then
      let some n := v.toNat? | return none
      res := { res with trustLevel := UInt32.ofNat n }
      i := next
    else if let some (v, next) := takeFlagArg argv i "-j" "--threads" then
      let some _ := v.toNat? | return none
      i := next
    else if let some (v, next) := takeFlagArg argv i "-s" "--tstack" then
      let some _ := v.toNat? | return none
      i := next
    else if let some (v, next) := takeFlagArg argv i "-M" "--memory" then
      let some n := v.toNat? | return none
      res := { res with maxMemoryMb? := some n }
      i := next
    else if let some (v, next) := takeFlagArg argv i "-T" "--timeout" then
      let some n := v.toNat? | return none
      res := { res with timeout? := some n }
      i := next
    else if let some (v, next) := takeFlagArg argv i "-E" "--errorOnKind" then
      res := { res with errorOnKinds := res.errorOnKinds.push v.toName }
      i := next
    else if let some (v, next) := takeFlagArg argv i "-D" "--define" then
      let some kv := splitEq v | return none
      res := { res with configOpts := res.configOpts.push kv }
      i := next
    else if arg.startsWith "-" then
      return none
    else
      positional := positional.push arg
      i := i + 1
  if positional.size != 1 then
    return none
  return some { res with fileName := positional[0]! }

private def stripLangHeader (contents : String) : Option String :=
  if let some rest := contents.dropPrefix? "#lang" then
    let endLinePos := rest.find '\n'
    let langId := rest.sliceTo endLinePos |>.trimAscii
    if langId == "lean4" then
      some (rest.sliceFrom endLinePos).copy
    else
      none
  else
    some contents

private def resolveRelative (cwd : String) (p : FilePath) : FilePath :=
  if p.isAbsolute || cwd.isEmpty then p else FilePath.mk cwd / p

private def getMtime? (p : FilePath) : IO (Option IO.FS.SystemTime) := do
  try
    let md ← p.metadata
    return some md.modified
  catch _ =>
    return none

private def getRealPathStr (p : FilePath) : IO String := do
  try
    return (← IO.FS.realPath p).toString
  catch _ =>
    return p.toString

private def isStdlibModuleName (m : Name) : Bool :=
  match m.getRoot with
  | `Init | `Std | `Lean => true
  | _ => false

@[export lean_zygote_preload]
def preloadSnapshot (sysroot importsCsv headerFileOpt setupFileOpt : String) (isModuleByte : UInt8) :
    IO ZygoteSnapshot := do
  Lean.initSearchPath ⟨sysroot⟩
  unsafe Lean.enableInitializersExecution
  let mut imports : Array Import := #[]
  let mut isModule := isModuleByte != 0
  let mut trustLevel : UInt32 := 0
  let mut arts : NameMap ImportArtifacts := {}
  let mut opts : Options := {}
  if !setupFileOpt.isEmpty then
    let setup ← ModuleSetup.load ⟨setupFileOpt⟩
    isModule := isModule || setup.isModule
    arts := setup.importArts
    opts := opts.mergeBy (fun _ _ v => v) setup.options.toOptions
    if let some imps := setup.imports? then
      imports := imps
  if !headerFileOpt.isEmpty then
    let raw ← IO.FS.readFile ⟨headerFileOpt⟩
    let some contents := stripLangHeader raw
      | throw <| IO.userError s!"unsupported #lang header in {headerFileOpt}"
    let inputCtx := Parser.mkInputContext contents headerFileOpt
    let (stx, _, headerMsgs) ← Parser.parseHeader inputCtx
    if headerMsgs.hasErrors then
      throw <| IO.userError s!"parse errors in preload header {headerFileOpt}"
    isModule := isModule || Elab.HeaderSyntax.isModule stx
    if imports.isEmpty then
      imports := Elab.HeaderSyntax.imports stx
  if imports.isEmpty && !importsCsv.isEmpty then
    let mut modNames : Array Name := #[]
    for raw in importsCsv.splitOn "," do
      let s := raw.trimAscii.copy
      if !s.isEmpty && s != "none" then
        modNames := modNames.push s.toName
    let needsInit := !modNames.contains `Init.Prelude && !modNames.contains `Init
    if needsInit then
      imports := imports ++ #[{ module := `Init }, { module := `Init, isMeta := true }]
    else if modNames.contains `Init then
      -- Match HeaderSyntax.imports which emits both runtime and meta Init.
      imports := imports ++ #[{ module := `Init }, { module := `Init, isMeta := true }]
    for m in modNames do
      if m != `Init then
        imports := imports.push { module := m, isExported := true }
  if imports.isEmpty then
    imports := #[{ module := `Init }, { module := `Init, isMeta := true }]
  let level : OLeanLevel := if isModule then .exported else .private
  opts := Lean.internal.cmdlineSnapshots.setIfNotSet opts true
  opts := Elab.async.setIfNotSet opts true
  let env ← Lean.importModules (leakEnv := true) (loadExts := true) (level := level)
    imports opts trustLevel #[] arts
  let mut loadedOLeans : Std.HashMap Name (String × String × Option IO.FS.SystemTime) := {}
  for m in env.header.moduleNames do
    let p? ← match arts.find? m |>.bind (·.olean?) with
      | some p => pure (some p)
      | none =>
        try some <$> Lean.findOLean m catch _ => pure none
    if let some p := p? then
      let rp ← getRealPathStr p
      let mt ← getMtime? p
      loadedOLeans := loadedOLeans.insert m (p.toString, rp, mt)
  let mut directRoots : Array (Name × String × Option IO.FS.SystemTime) := #[]
  for imp in imports do
    if let some (_, rp, mt) := loadedOLeans.get? imp.module then
      if !(directRoots.any (·.1 == imp.module)) then
        directRoots := directRoots.push (imp.module, rp, mt)
  let env ← unsafe Runtime.markPersistent env
  return {
    env
    level
    info := { imports, isModule, trustLevel, loadedOLeans, directRoots }
  }

private def snapshotNoneSentinel : UInt32 := 0xFFFFFFFF

private def prepareCleanRequest (cwd : String) (argv : Array String) :
    IO (Option (ParsedCompileArgs × Option ModuleSetup × String)) := do
  let some ca := parseCompileArgs argv | return none
  let setup? ← match ca.setupFileName? with
    | some sf =>
      let p := resolveRelative cwd sf
      try some <$> ModuleSetup.load p catch _ => return none
    | none => pure none
  if let some setup := setup? then
    if !setup.dynlibs.isEmpty || !setup.plugins.isEmpty then
      return none
  let filePath := resolveRelative cwd ⟨ca.fileName⟩
  let raw ← try IO.FS.readFile filePath catch _ => return none
  let some contents := stripLangHeader raw | return none
  return some (ca, setup?, contents)

private def canReuseParsedMeta (info : ZygoteSnapshotMeta) (ca : ParsedCompileArgs)
    (setup? : Option ModuleSetup) (reqIsModule : Bool) (reqImports : Array Import)
    (cwd : String) : IO Bool := do
  if ca.trustLevel != info.trustLevel then
    return false
  if reqIsModule != info.isModule then
    return false
  if reqImports != info.imports then
    return false
  -- Verify preloaded `.olean` files have not changed on disk.
  for (_m, rp, mt?) in info.directRoots do
    let curMt? ← getMtime? ⟨rp⟩
    if curMt? != mt? then
      return false
  if let some setup := setup? then
    for (modName, art) in setup.importArts do
      if let some oleanP := art.olean? then
        let resolved := resolveRelative cwd oleanP
        let some (rawPath, realPath, mt?) := info.loadedOLeans.get? modName | return false
        if resolved.toString != rawPath && resolved.toString != realPath then
          let actualReal ← getRealPathStr resolved
          if actualReal != realPath then
            return false
        if !isStdlibModuleName modName then
          let curMt? ← getMtime? resolved
          if curMt? != mt? then
            return false
  return true

@[export lean_zygote_select_snapshot_meta]
def selectSnapshotMeta (infos : Array ZygoteSnapshotMeta) (cwd _leanPath : String) (argv : Array String) :
    IO UInt32 := do
  if infos.isEmpty then
    return snapshotNoneSentinel
  let some (ca, setup?, contents) ← prepareCleanRequest cwd argv | return snapshotNoneSentinel
  let inputCtx := Parser.mkInputContext contents ca.fileName
  let (stx, _, headerMsgs) ← try Parser.parseHeader inputCtx catch _ => return snapshotNoneSentinel
  if headerMsgs.hasErrors then
    return snapshotNoneSentinel
  let setupIsModule := setup?.any (·.isModule)
  let reqIsModule := ca.cliModule || setupIsModule || Elab.HeaderSyntax.isModule stx
  let reqImports := match setup?.bind (·.imports?) with
    | some imps => imps
    | none => Elab.HeaderSyntax.imports stx
  let mut idx := 0
  for info in infos do
    if ← canReuseParsedMeta info ca setup? reqIsModule reqImports cwd then
      return UInt32.ofNat idx
    idx := idx + 1
  return snapshotNoneSentinel

@[export lean_zygote_select_snapshot]
def selectSnapshot (snaps : Array ZygoteSnapshot) (cwd leanPath : String) (argv : Array String) :
    IO UInt32 :=
  selectSnapshotMeta (snaps.map (·.info)) cwd leanPath argv

@[export lean_zygote_can_reuse]
def canReuseSnapshot (snap : ZygoteSnapshot) (cwd leanPath : String) (argv : Array String) :
    IO UInt8 := do
  let idx ← selectSnapshotMeta #[snap.info] cwd leanPath argv
  return if idx == 0 then 1 else 0

@[export lean_zygote_snapshot_meta_json]
def snapshotMetaJson (snap : ZygoteSnapshot) : String :=
  (toJson (toSnapshotMetaDto snap.info)).compress

@[export lean_zygote_parse_snapshot_metas]
def parseSnapshotMetas (jsons : Array String) : IO (Array ZygoteSnapshotMeta) := do
  let mut out : Array ZygoteSnapshotMeta := #[]
  for raw in jsons do
    let j ← IO.ofExcept (Json.parse raw)
    let dto : SnapshotMetaDto ← IO.ofExcept (fromJson? j)
    out := out.push (ofSnapshotMetaDto dto)
  return out

@[export lean_zygote_can_run_clean]
def canRunClean (cwd _leanPath : String) (argv : Array String) : IO UInt8 := do
  let req? ← prepareCleanRequest cwd argv
  return if req?.isSome then 1 else 0

private def setConfigOption (opts : Options) (name : Name) (val : String) : IO Options := do
  if let some decl := (← getOptionDecls).find? name then
    Language.Lean.setOption opts decl name val
  else
    return opts.set name val

private def runFrontendCommon (sysroot : String) (argv : Array String)
    (snap? : Option ZygoteSnapshot) : IO UInt32 := do
  Lean.initSearchPath ⟨sysroot⟩
  unsafe Lean.enableInitializersExecution
  let some ca := parseCompileArgs argv
    | IO.eprintln "lean-zygote: invalid arguments in worker"; return 1
  if let some memMb := ca.maxMemoryMb? then
    if memMb != 0 then
      setMaxMemory (memMb.toUSize * 1024 * 1024)
  if let some timeout := ca.timeout? then
    if timeout != 0 then
      setMaxHeartbeat (timeout.toUSize * 1000)
  let mut leanOpts : Options := {}
  for (k, v) in ca.configOpts do
    leanOpts ← setConfigOption leanOpts k v
  let setup? ← ca.setupFileName?.mapM ModuleSetup.load
  let contents ← IO.FS.readFile ⟨ca.fileName⟩
  let some contents := stripLangHeader contents
    | IO.eprintln s!"unsupported #lang header in {ca.fileName}"; return 1
  let mainModuleName ←
    if let some setup := setup? then
      pure setup.name
    else
      try Lean.moduleNameOfFileName ⟨ca.fileName⟩ ca.rootDir?
      catch e =>
        if ca.oleanFileName?.isNone && ca.cFileName?.isNone then
          pure `_stdin
        else
          throw e
  if let some snap := snap? then
    Elab.setPreloadedImportHook <| some fun reqImports reqLevel reqTrust reqPlugins _reqArts _reqOpts => do
      if reqImports == snap.info.imports && reqLevel == snap.level && reqTrust == snap.info.trustLevel && reqPlugins.isEmpty then
        return some snap.env
      else
        return none
  let env? ← Elab.runFrontend contents leanOpts ca.fileName mainModuleName
    ca.trustLevel ca.oleanFileName? ca.ileanFileName? ca.jsonOutput ca.errorOnKinds
    #[] ca.printStats setup?
  if let some env := env? then
    if let some cFile := ca.cFileName? then
      if let some parent := cFile.parent then
        IO.FS.createDirAll parent
      let tmp := FilePath.mk s!"{cFile}.zygote.tmp"
      let data ← Compiler.LCNF.emitC mainModuleName
        |>.toIO' { fileName := ca.fileName, fileMap := default } { env }
      IO.FS.writeFile tmp data
      IO.FS.rename tmp cFile
  (← IO.getStdout).flush
  (← IO.getStderr).flush
  return if env?.isSome then 0 else 1

@[export lean_zygote_run_child]
def runChild (snap : ZygoteSnapshot) (sysroot _leanPath : String) (argv : Array String) :
    IO UInt32 :=
  runFrontendCommon sysroot argv (some snap)

@[export lean_zygote_run_clean_child]
def runCleanChild (sysroot _leanPath : String) (argv : Array String) : IO UInt32 :=
  runFrontendCommon sysroot argv none

@[export lean_zygote_snapshot_summary]
def snapshotSummary (snap : ZygoteSnapshot) : String :=
  s!"modules={snap.info.loadedOLeans.size} imports={snap.info.imports.size} isModule={snap.info.isModule}"

end LeanZygote
