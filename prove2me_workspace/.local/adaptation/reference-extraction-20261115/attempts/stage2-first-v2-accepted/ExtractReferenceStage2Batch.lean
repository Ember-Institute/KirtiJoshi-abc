/-
Stage2 batch draft, not yet compiled. The helpers and elaboration sequence
come from prove2me_workspace/scripts/extract_sketch_info.lean.
Only imports Lean. No source-pattern matching. Re-elaborate each configured
file in a fresh header environment with InfoTree enabled, then write each
file's JSONL separately. The MCP-CI leaf elaboration runs the final run_meta.

Set structured environment.REFERENCE_STAGE2_CONFIG to the JSON config path.
All compiler, source and dependency inputs remain stable until CI terminates.

Canonical oracle limitations remain: macro-fabricated positions and recursive
self references elaborated as locals do not become constant-reference facts.
-/
import Lean
import Iut.Implication.Corollary22
open Lean Elab Parser
namespace ReferenceStage2

/-- First node of syntax kind `k` inside `stx`, depth-first. -/
partial def findKind? (stx : Syntax) (k : SyntaxNodeKind) : Option Syntax :=
  if stx.getKind == k then some stx
  else stx.getArgs.findSome? (findKind? · k)

def posJson (fm : FileMap) (p : String.Pos.Raw) : Json :=
  let pos := fm.toPosition p
  Json.mkObj [("line", toJson pos.line), ("col", toJson pos.column),
              ("offset", toJson p.byteIdx)]

/-- `{"start":…,"end":…}` for a syntax node's source range, null if absent. -/
def rangeJson (fm : FileMap) (stx? : Option Syntax) : Json :=
  match stx?.bind fun s => do pure (← s.getPos?, ← s.getTailPos?) with
  | some (s, e) => Json.mkObj [("start", posJson fm s), ("end", posJson fm e)]
  | none => Json.null

/-- A complete parser tree with exact syntax ranges. No source-text inference.
Signature subtrees retain nested `∀` binders, type-level lets, and all brackets.
Context command subtrees retain `variable`, `include`, and wrapper scopes. -/
partial def syntaxJson (fm : FileMap) (stx : Syntax) : Json :=
  let base := [("syntaxKind", Json.str stx.getKind.toString),
               ("range", rangeJson fm (some stx))]
  let more := match stx with
    | .ident _ raw ident _ => [("identifier", Json.str ident.toString),
                               ("rawIdentifier", Json.str raw.toString)]
    | .atom _ value => [("atom", Json.str value)]
    | .node _ _ args => [("children", Json.arr (args.map (syntaxJson fm)))]
    | .missing => []
  Json.mkObj (base ++ more)

/-- Collect every occurrence, not just the first declaration in a mutual block. -/
partial def collectKinds (stx : Syntax) (kinds : Array SyntaxNodeKind) : Array Syntax :=
  let here := if kinds.contains stx.getKind then #[stx] else #[]
  stx.getArgs.foldl (fun acc child => acc ++ collectKinds child kinds) here

/-- Extraction keeps atomic spans but makes unsupported generation explicit. -/
def generationIssue (cmd : Syntax) : Option String :=
  if (findKind? cmd ``Command.mutual).isSome then some "mutual-command"
  else if (collectKinds cmd #[``Command.declaration]).size > 1 then
    some "multiple-declarations-in-one-command"
  else none

/-- Collect (constant, start, end) for every TermInfo node that elaborated an
original piece of syntax to a constant reference. -/
partial def collectRefs (t : InfoTree) (acc : Array (Name × String.Pos.Raw × String.Pos.Raw)) :
    Array (Name × String.Pos.Raw × String.Pos.Raw) :=
  match t with
  | .context _ t => collectRefs t acc
  | .hole _ => acc
  | .node info children =>
    let acc := match info with
      | .ofTermInfo ti =>
        match ti.expr with
        | .const c _ =>
          let isOriginal := match ti.stx.getHeadInfo with
            | .original .. => true
            | _ => false
          if isOriginal then
            match ti.stx.getPos?, ti.stx.getTailPos? with
            | some s, some e => acc.push (c, s, e)
            | _, _ => acc
          else acc
        | _ => acc
      | _ => acc
    children.foldl (fun a c => collectRefs c a) acc

def fromExcept (e : Except String α) : IO α :=
  match e with
  | .ok value => pure value
  | .error message => throw (IO.userError message)

def writeFact (handle : IO.FS.Handle) (fields : List (String × Json)) : IO Unit :=
  handle.putStrLn (Json.mkObj fields).compress

def readOptions (config : Json) : IO Options := do
  let entries := (config.getObjValAs? (Array Json) "options").toOption.getD #[]
  let mut options : Options := {}
  for entry in entries do
    let name ← fromExcept (entry.getObjValAs? String "name")
    let kind ← fromExcept (entry.getObjValAs? String "type")
    match kind with
    | "bool" =>
      let value ← fromExcept (entry.getObjValAs? Bool "value")
      options := options.setBool name.toName value
    | "nat" =>
      let value ← fromExcept (entry.getObjValAs? Nat "value")
      options := options.set name.toName value
    | "string" =>
      let value ← fromExcept (entry.getObjValAs? String "value")
      options := options.set name.toName value
    | "name" =>
      let value ← fromExcept (entry.getObjValAs? String "value")
      options := options.set name.toName value.toName
    | _ => throw (IO.userError s!"Unsupported option type {kind} for {name}")
  return options

unsafe def extractOne (entry : Json) (outputDir : System.FilePath)
    (prefixes : Array Name) (options : Options) : IO Json := do
  let moduleText ← fromExcept (entry.getObjValAs? String "module")
  let source ← fromExcept (entry.getObjValAs? String "source")
  unless (System.FilePath.mk source).isAbsolute do
    throw (IO.userError s!"Source path must be absolute: {source}")
  let file := (entry.getObjValAs? String "file").toOption.getD
    (moduleText.replace "." "/" ++ ".lean")
  let output := outputDir / (moduleText.replace "." "/" ++ ".jsonl")
  let normalizedOutput := outputDir / (moduleText.replace "." "/" ++ ".normalized.lean")
  let diagnosticsOutput := outputDir / (moduleText.replace "." "/" ++ ".diagnostics.json")
  IO.FS.createDirAll (output.parent.getD outputDir)
  let input ← IO.FS.readFile source
  let inputCtx := Parser.mkInputContext input source
  -- mkInputContext defaults to String.crlfToLf. Every emitted byte offset
  -- addresses THIS immutable artifact, never the raw source file.
  let normalized := inputCtx.inputString
  IO.FS.writeFile normalizedOutput normalized
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  -- The official oracle leaves mainModule anonymous. Set the actual module
  -- before mkState so private names and the auxiliary-name generator agree.
  let (env, messages) ← processHeader header options messages inputCtx
    (mainModule := moduleText.toName)
  let cmdState := Command.mkState env messages options
  let cmdState := { cmdState with infoState := { enabled := true } }
  let s ← IO.processCommands inputCtx parserState cmdState
  let mut diagnosticMessages : Array String := #[]
  for message in s.commandState.messages.toList do
    diagnosticMessages := diagnosticMessages.push (← message.toString)
  let hasErrors := s.commandState.messages.hasErrors
  IO.FS.writeFile diagnosticsOutput (Json.pretty (Json.mkObj [
    ("module", Json.str moduleText), ("source", Json.str source),
    ("hasErrors", toJson hasErrors), ("messages", toJson diagnosticMessages)]) ++ "\n")
  if hasErrors then
    return Json.mkObj [
      ("module", Json.str moduleText), ("file", Json.str file),
      ("source", Json.str source), ("status", Json.str "elaboration_failed"),
      ("diagnostics", Json.str diagnosticsOutput.toString)]
  let fm := inputCtx.fileMap
  -- Preserve all original constant names, including private names. Prefix
  -- filtering, when explicitly configured, accepts their public user names.
  let keep : Name → Bool := fun c =>
    prefixes.isEmpty || prefixes.any (fun p =>
      p.isPrefixOf c || p.isPrefixOf ((privateToUserName? c).getD c))
  let mut refs : Array (Name × String.Pos.Raw × String.Pos.Raw) := #[]
  for tree in s.commandState.infoState.trees do refs := collectRefs tree refs
  let deduped := refs.foldl (init := (Std.HashSet.emptyWithCapacity, #[]))
    fun (seen, out) r@(constant, start, stop) =>
      let key := s!"{constant}:{start.byteIdx}:{stop.byteIdx}"
      if seen.contains key || !keep constant then (seen, out)
      else (seen.insert key, out.push r)
  let sorted := deduped.2.qsort fun (_, a, _) (_, b, _) => a < b
  let temporary := System.FilePath.mk (output.toString ++ ".partial")
  let declCount ← IO.FS.withFile temporary .write fun handle => do
    let mut declCount := 0
    writeFact handle [
      ("kind", Json.str "source"), ("schema", Json.str "reference-stage2-v1"),
      ("module", Json.str moduleText), ("file", Json.str file),
      ("source", Json.str source), ("mainModule", Json.str moduleText),
      ("offsetCoordinate", Json.str "lean-normalized-utf8"),
      ("normalization", Json.str "String.crlfToLf"),
      ("coordinateSource", Json.str normalizedOutput.toString),
      ("rawByteLength", toJson input.utf8ByteSize),
      ("byteLength", toJson normalized.utf8ByteSize),
      ("rawSha256Expected", (entry.getObjValAs? String "sourceSha256").toOption.map Json.str |>.getD Json.null),
      ("normalizedSha256Expected", (entry.getObjValAs? String "normalizedSha256").toOption.map Json.str |>.getD Json.null),
      ("namePrefixes", toJson (prefixes.map Name.toString)),
      ("headerSyntax", syntaxJson fm header)]
    -- Context commands are immutable skeleton material, not deletable
    -- declarations. Full context syntax covers variables, include, open,
    -- local notation, namespace/section/end, options, and attributes.
    for cmd in s.commands do
      let isDecl := (findKind? cmd ``Command.declaration).isSome ||
        (findKind? cmd ``Command.declId).isSome
      writeFact handle [
        ("kind", Json.str "command"), ("file", Json.str file),
        ("syntaxKind", Json.str cmd.getKind.toString),
        ("generationIssue", (generationIssue cmd).map Json.str |>.getD Json.null),
        ("range", rangeJson fm (some cmd)), ("isDeclaration", toJson isDecl),
        ("contextSyntax", if isDecl then Json.null else syntaxJson fm cmd)]
    for cmd in s.commands do
      -- Preserve the canonical oracle's wrapper/anonymous-instance/lemma
      -- detection. Whole outer commands (including mutuals) are atomic.
      let declaration? := findKind? cmd ``Command.declaration
      let decl := declaration?.getD cmd
      let declId? := findKind? decl ``Command.declId
      unless declaration?.isSome || declId?.isSome do continue
      let nameText? := declId?.map fun d => d[0].getId
      let valStx :=
        (findKind? decl ``Command.declValSimple).orElse fun _ =>
        (findKind? decl ``Command.declValEqns).orElse fun _ =>
        findKind? decl ``Command.whereStructInst
      let valKind := valStx.map fun value =>
        if value.isOfKind ``Command.declValSimple then "simple"
        else if value.isOfKind ``Command.declValEqns then "eqns" else "whereStructInst"
      let some start := cmd.getPos? | continue
      let some stop := cmd.getTailPos? | continue
      let signatures := collectKinds cmd #[``Command.declSig, ``Command.optDeclSig]
      let declIds := collectKinds cmd #[``Command.declId]
      declCount := declCount + 1
      writeFact handle [
        ("kind", Json.str "decl"), ("file", Json.str file),
        ("commandKind", Json.str cmd.getKind.toString),
        ("generationIssue", (generationIssue cmd).map Json.str |>.getD Json.null),
        ("nameText", nameText?.map (Json.str ·.toString) |>.getD Json.null),
        ("nameRange", rangeJson fm (declId?.map (fun d => d[0]))),
        ("declarationIds", Json.arr (declIds.map (syntaxJson fm))),
        ("signatureSyntax", Json.arr (signatures.map (syntaxJson fm))),
        ("declStart", posJson fm start), ("declEnd", posJson fm stop),
        ("valStart", (valStx.bind (·.getPos?)).map (posJson fm ·) |>.getD Json.null),
        ("valKind", valKind.map Json.str |>.getD Json.null),
        ("valueRange", rangeJson fm valStx),
        ("docstring", rangeJson fm (findKind? cmd ``Command.docComment)),
        ("privateTok", rangeJson fm (findKind? cmd ``Command.private))]
    for (constant, start, stop) in sorted do
      writeFact handle [
        ("kind", Json.str "ref"), ("file", Json.str file),
        ("const", Json.str constant.toString),
        ("userName", Json.str (((privateToUserName? constant).getD constant).toString)),
        ("isPrivate", toJson (privateToUserName? constant).isSome),
        ("start", posJson fm start), ("end", posJson fm stop)]
    writeFact handle [
      ("kind", Json.str "summary"), ("module", Json.str moduleText),
      ("status", Json.str "success"), ("declarationCount", toJson declCount),
      ("referenceCount", toJson sorted.size)]
    return declCount
  IO.FS.rename temporary output
  return Json.mkObj [
    ("module", Json.str moduleText), ("file", Json.str file),
    ("source", Json.str source), ("status", Json.str "success"),
    ("offsetCoordinate", Json.str "lean-normalized-utf8"),
    ("normalization", Json.str "String.crlfToLf"),
    ("coordinateSource", Json.str normalizedOutput.toString),
    ("rawByteLength", toJson input.utf8ByteSize),
    ("byteLength", toJson normalized.utf8ByteSize),
    ("output", Json.str output.toString),
    ("diagnostics", Json.str diagnosticsOutput.toString),
    ("declarationCount", toJson declCount), ("referenceCount", toJson sorted.size)]

unsafe def runBatch (configPath : String) : IO Unit := do
  let configText ← IO.FS.readFile configPath
  let config ← fromExcept (Json.parse configText)
  let files ← fromExcept (config.getObjValAs? (Array Json) "files")
  let outputText ← fromExcept (config.getObjValAs? String "outputDir")
  let prefixText := (config.getObjValAs? (Array String) "namePrefixes").toOption.getD #[]
  let failFast := (config.getObjValAs? Bool "failFast").toOption.getD true
  let outputDir := System.FilePath.mk outputText
  unless outputDir.isAbsolute do throw (IO.userError "outputDir must be absolute")
  let options ← readOptions config
  IO.FS.createDirAll outputDir
  -- As in the official --run oracle: respect the scheduler-provided LEAN_PATH
  -- and the selected toolchain. No project source or build input is changed.
  Lean.initSearchPath (← Lean.findSysroot)
  Lean.enableInitializersExecution
  let index := outputDir / "index.json"
  let mut results : Array Json := #[]
  let mut failed := false
  for file in files do
    let result ← try
      extractOne file outputDir (prefixText.map String.toName) options
    catch exception =>
      pure (Json.mkObj [("status", Json.str "exception"), ("input", file),
        ("message", Json.str exception.toString)])
    results := results.push result
    let status := (result.getObjValAs? String "status").toOption.getD "exception"
    failed := failed || status != "success"
    IO.FS.writeFile index (Json.pretty (Json.mkObj [
      ("schema", Json.str "reference-stage2-index-v1"),
      ("configPath", Json.str configPath), ("config", config),
      ("requestedFiles", toJson files.size), ("finishedFiles", toJson results.size),
      ("complete", toJson (results.size == files.size && !failed)),
      ("results", Json.arr results)]) ++ "\n")
    let moduleText := (file.getObjValAs? String "module").toOption.getD "<invalid module>"
    IO.println s!"Stage2 {results.size}/{files.size}: {moduleText}: {status}"
    if failed && failFast then
      throw (IO.userError s!"Stage2 failed; see {index}")
  if failed then throw (IO.userError s!"Stage2 had failures; see {index}")
  IO.println s!"Stage2 complete; index: {index}"

run_meta do
  let configPath := (← IO.getEnv "REFERENCE_STAGE2_CONFIG").getD
    "/tmp/p2m-reference-skeleton-tool-20261115/stage2-config.json"
  runBatch configPath

end ReferenceStage2


set_option pp.fullNames true
set_option pp.funBinderTypes true
set_option pp.piBinderTypes true
set_option pp.universes true

open Lean
namespace C22RootUniverses

def queryRoot (name : Name) (outputFile : String) : MetaM Unit := do
  unless Lean.versionString == "4.35.0-rc3" do
    throwError "Wrong original-source query compiler: {Lean.versionString}"
  let ci ← getConstInfo name
  let env ← getEnv
  let sourceModule : Option Name := do
    let index ← env.getModuleIdxFor? name
    env.header.moduleNames[index.toNat]?
  let telescope ← Lean.Meta.forallTelescope ci.type fun xs result => do
    let mut binders : Array Json := #[]
    for x in xs do
      let declaration ← x.fvarId!.getDecl
      binders := binders.push (Json.mkObj [
        ("name", Json.str declaration.userName.toString),
        ("binderInfo", Json.str (reprStr declaration.binderInfo)),
        ("type", Json.str (← Lean.Meta.ppExpr declaration.type).pretty)])
    return Json.mkObj [("binders", Json.arr binders),
      ("result", Json.str (← Lean.Meta.ppExpr result).pretty)]
  let axioms ← collectAxioms name
  let result := Json.mkObj [
    ("schema", Json.str "c22-root-universe-query-v1"),
    ("graphJobId", Json.str "ci-012771-ee109b3e"),
    ("compilerVersion", Json.str Lean.versionString),
    ("name", Json.str name.toString),
    ("module", sourceModule.map (Json.str ·.toString) |>.getD Json.null),
    -- Preserve kernel declaration order; do not sort universe parameters.
    ("levelParams", toJson (ci.levelParams.map Name.toString)),
    ("ppUniverses", toJson true),
    ("elaboratedType", Json.str (← Lean.Meta.ppExpr ci.type).pretty),
    ("elaboratedTelescope", telescope),
    ("axioms", toJson ((axioms.qsort Name.lt).map Name.toString)),
    ("hasSorryAx", toJson (axioms.contains `sorryAx)),
    ("unexpectedAxioms", toJson ((axioms.filter fun ax =>
      !#[`propext, `Classical.choice, `Quot.sound].contains ax).map Name.toString))]
  IO.FS.writeFile outputFile (result.pretty ++ "\n")
  logInfo s!"Root universe/type/axiom query: {name} → {outputFile}"

def outputDirectory : IO String := do
  let directory := (← IO.getEnv "REFERENCE_ROOT_TYPES_DIR").getD
    "/tmp/p2m-reference-skeleton-tool-20261115/c22-root-universes"
  unless (System.FilePath.mk directory).isAbsolute do
    throw (IO.userError "REFERENCE_ROOT_TYPES_DIR must be absolute")
  IO.FS.createDirAll directory
  return directory

run_meta do
  let directory ← outputDirectory
  queryRoot `Iut.Theorem110Invariants.theorem110 (directory ++ "/theorem110.json")

run_meta do
  let directory ← outputDirectory
  queryRoot `Iut.ThetaDataExistence (directory ++ "/theta-data-existence.json")

run_meta do
  let directory ← outputDirectory
  queryRoot `Iut.Corollary22Inputs.c2 (directory ++ "/corollary22-c2.json")

run_meta do
  let directory ← outputDirectory
  queryRoot `Iut.ThetaDataExistence.thetaData (directory ++ "/theta-data-field.json")

run_meta do
  let directory ← outputDirectory
  queryRoot `Iut.ThetaDataExistence.mk (directory ++ "/theta-data-constructor.json")

end C22RootUniverses

#print axioms Iut.Theorem110Invariants.theorem110
#print axioms Iut.ThetaDataExistence
#print axioms Iut.Corollary22Inputs.c2
