import Lean
import Iut.Implication.PrimeSelection

set_option pp.fullNames true
set_option pp.funBinderTypes true
set_option pp.piBinderTypes true
set_option pp.universes true

open Lean
namespace PrimeSelectionFacts

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
    ("schema", Json.str "prime-selection-type-query-v1"),
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


partial def findKind? (stx : Syntax) (kind : SyntaxNodeKind) : Option Syntax :=
  if stx.getKind == kind then some stx else stx.getArgs.findSome? (findKind? · kind)

partial def keywordAtoms (stx : Syntax) : Array Syntax :=
  match stx with
  | .atom _ value => if value == "theorem" || value == "lemma" then #[stx] else #[]
  | .node _ _ children => children.foldl (fun found child => found ++ keywordAtoms child) #[]
  | _ => #[]

def positionJson (fm : FileMap) (p : String.Pos.Raw) : Json :=
  let v := fm.toPosition p
  Json.mkObj [("line", toJson v.line), ("col", toJson v.column), ("offset", toJson p.byteIdx)]

def roots : Array Name := #[`Iut.ChebyshevBound.exists_prime_notMem,
  `Iut.LocalHeightData.exists_prime_selection, `Iut.sum_log_primeFactors_le]

run_meta do
  let directory := (← IO.getEnv "REFERENCE_PRIME_FACTS_DIR").getD
    "/home/admin-wsl/Coq/abc/prove2me_workspace/.local/adaptation/reference-extraction-20261115/prime-selection-source-facts"
  IO.FS.createDirAll directory
  let source := "/home/admin-wsl/Coq/abc/refer/iut/Iut/Implication/PrimeSelection.lean"
  let raw ← IO.FS.readFile source
  let inputCtx := Parser.mkInputContext raw source
  let normalized := inputCtx.inputString
  IO.FS.writeFile (directory ++ "/PrimeSelection.normalized.lean") normalized
  let env ← getEnv
  let syntaxModule ← Parser.testParseModule env source normalized
  let sourceSha := (← IO.getEnv "REFERENCE_PRIME_SOURCE_SHA256").getD ""
  unless sourceSha.length == 64 do throwError "Missing source identity checksum"
  let mut facts : Array Json := #[Json.mkObj [("kind", Json.str "source"),
    ("source", Json.str source), ("normalizedSha256", Json.str sourceSha),
    ("offsetCoordinate", Json.str "lean-normalized-utf8"),
    ("coordinateSource", Json.str (directory ++ "/PrimeSelection.normalized.lean")),
    ("byteLength", toJson normalized.utf8ByteSize)]]
  for root in roots do
    let some range ← findDeclarationRanges? root | throwError "No declaration range: {root}"
    let mut matched : Array Syntax := #[]
    for cmd in syntaxModule[1].getArgs do
      let some declId := findKind? cmd ``Lean.Parser.Command.declId | continue
      let some pos := declId[0].getPos? | continue
      if inputCtx.fileMap.toPosition pos == range.selectionRange.pos then
        matched := matched.push cmd
    unless matched.size == 1 do throwError "Ambiguous source command for {root}: {matched.size}"
    let cmd := matched[0]!
    let some declId := findKind? cmd ``Lean.Parser.Command.declId | throwError "Missing declId"
    let some nameStart := declId[0].getPos? | throwError "Missing binding position"
    let atoms := (keywordAtoms cmd).filter fun atom =>
      (atom.getPos?).any (· < nameStart)
    unless atoms.size == 1 do throwError "Ambiguous declaration keyword for {root}: {atoms.size}"
    let atom := atoms[0]!
    let some start := atom.getPos? | throwError "Missing keyword start"
    let some stop := atom.getTailPos? | throwError "Missing keyword stop"
    let .atom _ keyword := atom | throwError "Not an atom"
    facts := facts.push (Json.mkObj [("kind", Json.str "keyword"),
      ("name", Json.str root.toString), ("keyword", Json.str keyword),
      ("keywordRange", Json.mkObj [("start", positionJson inputCtx.fileMap start),
        ("end", positionJson inputCtx.fileMap stop)])])
  IO.FS.writeFile (directory ++ "/keywords.jsonl")
    (String.intercalate "\n" (facts.toList.map Json.compress) ++ "\n")

run_meta do
  let directory := (← IO.getEnv "REFERENCE_PRIME_FACTS_DIR").getD
    "/home/admin-wsl/Coq/abc/prove2me_workspace/.local/adaptation/reference-extraction-20261115/prime-selection-source-facts"
  for root in roots do
    queryRoot root (directory ++ "/" ++ root.toString.replace "." "-" ++ ".json")

end PrimeSelectionFacts

#print axioms Iut.ChebyshevBound.exists_prime_notMem
#print axioms Iut.LocalHeightData.exists_prime_selection
#print axioms Iut.sum_log_primeFactors_le
