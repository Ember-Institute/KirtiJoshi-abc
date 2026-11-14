/-
Phase 0 only. Draft for a normal MCP-CI `leaf` check (no --run required).
Imports Lean only. Parser.parseHeader does not elaborate the reference files
and does not require their oleans. Module names come from parser syntax nodes.

Set structured environment.REFERENCE_HEADER_CONFIG to an absolute JSON file.
The config supplies absolute sourceRoots, roots, and output; optional groups
request separate closures over the same parsed source graph. Keep all inputs
stable until the job and SHA receipt are complete.
-/
import Lean

open Lean
namespace ReferenceHeaders

def fromExcept (e : Except String α) : IO α :=
  match e with
  | .ok value => pure value
  | .error message => throw (IO.userError message)

partial def findKind? (stx : Syntax) (kind : SyntaxNodeKind) : Option Syntax :=
  if stx.getKind == kind then some stx
  else stx.getArgs.findSome? (findKind? · kind)

partial def findIdent? (stx : Syntax) : Option Syntax :=
  if stx.isIdent then some stx else stx.getArgs.findSome? findIdent?

partial def importCommands (stx : Syntax) : Array Syntax :=
  if stx.getKind == ``Lean.Parser.Module.import then #[stx]
  else stx.getArgs.foldl (fun acc child => acc ++ importCommands child) #[]

def posJson (fm : FileMap) (p : String.Pos.Raw) : Json :=
  let position := fm.toPosition p
  Json.mkObj [("line", toJson position.line), ("col", toJson position.column),
    ("offset", toJson p.byteIdx)]

def rangeJson (fm : FileMap) (stx : Syntax) : Json :=
  match stx.getPos?, stx.getTailPos? with
  | some start, some stop => Json.mkObj [
      ("start", posJson fm start), ("end", posJson fm stop)]
  | _, _ => Json.null

def sortedNames (names : Std.HashSet Name) : Array Name :=
  names.toArray.qsort Name.lt

def namesJson (names : Array Name) : Json := toJson (names.map Name.toString)

def reach (edges : Std.HashMap Name (Array Name)) (roots : Array Name) : Array Name := Id.run do
  let mut visited : Std.HashSet Name := {}
  let mut work := roots.toList
  while h : work ≠ [] do
    let name := work.head h
    work := work.tail
    if visited.contains name then continue
    visited := visited.insert name
    work := (edges[name]?.getD #[]).toList ++ work
  return sortedNames visited

def extract (configPath : String) : IO Unit := do
  let configText ← IO.FS.readFile configPath
  let config ← fromExcept (Json.parse configText)
  let sourceRoots ← fromExcept (config.getObjValAs? (Array String) "sourceRoots")
  let rootsText ← fromExcept (config.getObjValAs? (Array String) "roots")
  let output ← fromExcept (config.getObjValAs? String "output")
  let groups := (config.getObjValAs? (Array Json) "groups").toOption.getD #[]
  let mut roots := rootsText.map String.toName
  for group in groups do
    let groupRoots ← fromExcept (group.getObjValAs? (Array String) "roots")
    roots := roots ++ groupRoots.map String.toName
  for root in sourceRoots do
    unless (System.FilePath.mk root).isAbsolute do
      throw (IO.userError s!"sourceRoots must be absolute: {root}")
  unless (System.FilePath.mk output).isAbsolute do
    throw (IO.userError "output must be absolute")
  let mut work := roots.toList
  let mut visited : Std.HashSet Name := {}
  let mut missing : Std.HashSet Name := {}
  let mut headerErrors : Std.HashSet Name := {}
  let mut edges : Std.HashMap Name (Array Name) := {}
  let mut records : Array Json := #[]
  while h : work ≠ [] do
    let name := work.head h
    work := work.tail
    if visited.contains name then continue
    visited := visited.insert name
    let relative := name.toString.replace "." "/" ++ ".lean"
    let mut candidates : Array String := #[]
    for directory in sourceRoots do
      let file := System.FilePath.mk directory / relative
      if ← file.pathExists then candidates := candidates.push file.toString
    let some file := candidates[0]? | do
      missing := missing.insert name
      records := records.push (Json.mkObj [
        ("module", Json.str name.toString), ("status", Json.str "missing_source"),
        ("relativePath", Json.str relative), ("imports", Json.arr #[])])
      continue
    let input ← IO.FS.readFile (System.FilePath.mk file)
    let inputCtx := Lean.Parser.mkInputContext input file
    let (header, parserState, messages) ← Lean.Parser.parseHeader inputCtx
    let mut diagnostics : Array String := #[]
    for message in messages.toList do diagnostics := diagnostics.push (← message.toString)
    let mut explicitImports : Array Name := #[]
    let mut importFacts : Array Json := #[]
    for command in importCommands header.raw do
      let some identifier := findIdent? command |
        throw (IO.userError s!"Import parser node without module identifier in {file}")
      let imported := identifier.getId
      explicitImports := explicitImports.push imported
      importFacts := importFacts.push (Json.mkObj [
        ("module", Json.str imported.toString),
        ("range", rangeJson inputCtx.fileMap command),
        ("moduleRange", rangeJson inputCtx.fileMap identifier),
        ("public", toJson (findKind? command ``Lean.Parser.Module.public).isSome),
        ("meta", toJson (findKind? command ``Lean.Parser.Module.meta).isSome),
        ("all", toJson (findKind? command ``Lean.Parser.Module.all).isSome)])
    let isPrelude := (findKind? header.raw ``Lean.Parser.Module.prelude).isSome
    -- Lean inserts Init unless `prelude` is present. Preserve that real edge.
    let imports := if isPrelude then explicitImports else #[`Init] ++ explicitImports
    let failed := messages.hasErrors
    if failed then
      headerErrors := headerErrors.insert name
    else
      edges := edges.insert name imports
      work := imports.toList ++ work
    records := records.push (Json.mkObj [
      ("module", Json.str name.toString),
      ("status", Json.str (if failed then "header_error" else "parsed")),
      ("source", Json.str file), ("sourceCandidates", toJson candidates),
      ("relativePath", Json.str relative),
      ("parserInputUtf8ByteLength", toJson input.utf8ByteSize),
      ("headerEnd", posJson inputCtx.fileMap parserState.pos),
      ("isModuleSystem", toJson (findKind? header.raw ``Lean.Parser.Module.moduleTk).isSome),
      ("isPrelude", toJson isPrelude),
      ("explicitImports", Json.arr importFacts), ("imports", namesJson imports),
      ("diagnostics", toJson diagnostics)])
  let mut groupFacts : Array Json := #[]
  for group in groups do
    let label ← fromExcept (group.getObjValAs? String "name")
    let groupRoots ← fromExcept (group.getObjValAs? (Array String) "roots")
    let members := reach edges (groupRoots.map String.toName)
    groupFacts := groupFacts.push (Json.mkObj [
      ("name", Json.str label), ("roots", toJson groupRoots),
      ("modules", namesJson members),
      ("missing", namesJson (members.filter missing.contains)),
      ("headerErrors", namesJson (members.filter headerErrors.contains))])
  let report := Json.mkObj [
    ("schema", Json.str "reference-header-closure-v1"),
    ("phase", Json.str "Phase0-header-only"),
    ("configPath", Json.str configPath), ("config", config),
    ("roots", namesJson roots), ("sourceRoots", toJson sourceRoots),
    ("complete", toJson (missing.isEmpty && headerErrors.isEmpty)),
    ("missing", namesJson (sortedNames missing)),
    ("headerErrors", namesJson (sortedNames headerErrors)),
    ("groups", Json.arr groupFacts), ("modules", Json.arr records)]
  IO.FS.writeFile output (report.pretty ++ "\n")
  IO.println s!"Phase0 header report: {output}; visited={visited.size}, missing={missing.size}, headerErrors={headerErrors.size}"

run_meta do
  let configPath := (← IO.getEnv "REFERENCE_HEADER_CONFIG").getD
    "/tmp/p2m-reference-skeleton-tool-20261115/phase0-config.json"
  extract configPath

end ReferenceHeaders
