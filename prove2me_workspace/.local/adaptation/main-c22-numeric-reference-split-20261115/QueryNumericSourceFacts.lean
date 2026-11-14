import Lean
import Iut.Implication.Corollary22

/-! Stable JSON for *actual compiler Exprs*. No pretty-printer text is decoded here.
    Metadata is erased; local/metavariables are rejected. -/
namespace NumericSourceAudit
open Lean

def field (j : Json) (key : String) : Except String Json := j.getObjVal? key
def stringField (j : Json) (key : String) : Except String String := do
  (← field j key).getStr?
def arrayField (j : Json) (key : String) : Except String (Array Json) := do
  (← field j key).getArr?

-- Preserve actual Name components, including numeric components; do not use String.toName.
partial def encodeName : Name → Json
  | .anonymous => Json.arr #[]
  | .str p s => Json.arr #[(encodeName p), Json.str "str", Json.str s]
  | .num p n => Json.arr #[(encodeName p), Json.str "num", toJson n]

partial def decodeName (j : Json) : Except String Name := do
  let a ← j.getArr?
  if a.isEmpty then return .anonymous
  unless a.size == 3 do throw "Invalid Name JSON"
  let p ← decodeName a[0]!
  match ← a[1]!.getStr? with
  | "str" => return .str p (← a[2]!.getStr?)
  | "num" => return .num p (← a[2]!.getNat?)
  | _ => throw "Invalid Name component"

def node (kind : String) (values : List (String × Json)) : Json :=
  Json.mkObj (("kind", Json.str kind) :: values)

partial def encodeLevel : Level → Except String Json
  | .zero => return node "zero" []
  | .succ u => return node "succ" [("arg", ← encodeLevel u)]
  | .max u v => return node "max" [("left", ← encodeLevel u), ("right", ← encodeLevel v)]
  | .imax u v => return node "imax" [("left", ← encodeLevel u), ("right", ← encodeLevel v)]
  | .param n => return node "param" [("name", encodeName n)]
  | .mvar _ => throw "Universe metavariable in compiler type"

partial def decodeLevel (j : Json) : Except String Level := do
  match ← stringField j "kind" with
  | "zero" => return .zero
  | "succ" => return .succ (← decodeLevel (← field j "arg"))
  | "max" => return .max (← decodeLevel (← field j "left")) (← decodeLevel (← field j "right"))
  | "imax" => return .imax (← decodeLevel (← field j "left")) (← decodeLevel (← field j "right"))
  | "param" => return .param (← decodeName (← field j "name"))
  | k => throw s!"Unknown universe kind: {k}"

def encodeBinder : BinderInfo → String
  | .default => "default"
  | .implicit => "implicit"
  | .strictImplicit => "strictImplicit"
  | .instImplicit => "instImplicit"

def decodeBinder : String → Except String BinderInfo
  | "default" => return .default
  | "implicit" => return .implicit
  | "strictImplicit" => return .strictImplicit
  | "instImplicit" => return .instImplicit
  | k => throw s!"Unknown binder info: {k}"

partial def encodeExpr : Expr → Except String Json
  | .bvar i => return node "bvar" [("index", toJson i)]
  | .sort u => return node "sort" [("level", ← encodeLevel u)]
  | .const n us => return node "const" [("name", encodeName n),
      ("levels", Json.arr (← us.toArray.mapM encodeLevel))]
  | .app f a => return node "app" [("fn", ← encodeExpr f), ("arg", ← encodeExpr a)]
  | .lam n t b bi => return node "lam" [("name", encodeName n),
      ("type", ← encodeExpr t), ("body", ← encodeExpr b), ("binder", toJson (encodeBinder bi))]
  | .forallE n t b bi => return node "forall" [("name", encodeName n),
      ("type", ← encodeExpr t), ("body", ← encodeExpr b), ("binder", toJson (encodeBinder bi))]
  | .letE n t v b nd => return node "let" [("name", encodeName n),
      ("type", ← encodeExpr t), ("value", ← encodeExpr v), ("body", ← encodeExpr b),
      ("nondependent", toJson nd)]
  | .lit (.natVal n) => return node "nat" [("value", toJson n)]
  | .lit (.strVal s) => return node "string" [("value", toJson s)]
  | .mdata _ b => encodeExpr b
  | .proj n i b => return node "proj" [("name", encodeName n), ("index", toJson i),
      ("body", ← encodeExpr b)]
  | .fvar _ => throw "Free variable in compiler declaration type"
  | .mvar _ => throw "Expression metavariable in compiler declaration type"

abbrev NameRelocations := Array (Name × Name)

def relocateName (names : NameRelocations) (n : Name) : Except String Name := do
  if let some (_, target) := names.find? (fun pair => pair.1 == n) then return target
  if (`Iut).isPrefixOf n then throw s!"Unmapped project constant: {n}"
  return n

end NumericSourceAudit



open Lean
namespace NumericSourceFacts

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

def orThrow {α : Type} (value : Except String α) : MetaM α :=
  match value with
  | .ok a => pure a
  | .error e => throwError "{e}"

run_meta do
  unless Lean.versionString == "4.35.0-rc3" do
    throwError "Expected original compiler 4.35.0-rc3, got {Lean.versionString}"
  let some configPath ← IO.getEnv "NUMERIC_SOURCE_FACTS_CONFIG" |
    throwError "Missing NUMERIC_SOURCE_FACTS_CONFIG"
  let config ← orThrow (Json.parse (← IO.FS.readFile configPath))
  let output ← orThrow (config.getObjValAs? String "outputDir")
  let sources ← orThrow (config.getObjValAs? (Array Json) "sources")
  IO.FS.createDirAll output
  let env ← getEnv
  let mut records : Array Json := #[]
  let mut facts : Array Json := #[]
  for entry in sources do
    let source ← orThrow (entry.getObjValAs? String "source")
    let sourceSha ← orThrow (entry.getObjValAs? String "normalizedSha256")
    let moduleName ← orThrow (entry.getObjValAs? String "module")
    let rootText ← orThrow (entry.getObjValAs? String "name")
    let root := rootText.toName
    let raw ← IO.FS.readFile source
    let inputCtx := Parser.mkInputContext raw source
    let normalized := inputCtx.inputString
    let coordinateSource := output ++ "/" ++ moduleName.replace "." "-" ++ ".normalized.lean"
    IO.FS.writeFile coordinateSource normalized
    let syntaxModule ← Parser.testParseModule env source normalized
    unless sourceSha.length == 64 do throwError "Missing source checksum for {root}"
    facts := facts.push (Json.mkObj [("kind", Json.str "source"),
      ("name", Json.str rootText), ("module", Json.str moduleName),
      ("source", Json.str source), ("normalizedSha256", Json.str sourceSha),
      ("offsetCoordinate", Json.str "lean-normalized-utf8"),
      ("coordinateSource", Json.str coordinateSource),
      ("byteLength", toJson normalized.utf8ByteSize)])
    let some range ← findDeclarationRanges? root | throwError "Missing declaration range: {root}"
    let mut matched : Array Syntax := #[]
    for cmd in syntaxModule[1].getArgs do
      let some declId := findKind? cmd ``Lean.Parser.Command.declId | continue
      let some pos := declId[0].getPos? | continue
      if inputCtx.fileMap.toPosition pos == range.selectionRange.pos then
        matched := matched.push cmd
    unless matched.size == 1 do throwError "Source command match count {matched.size} for {root}"
    let cmd := matched[0]!
    let some declId := findKind? cmd ``Lean.Parser.Command.declId | throwError "Missing declaration ID"
    let some nameStart := declId[0].getPos? | throwError "Missing binding position"
    let atoms := (keywordAtoms cmd).filter fun atom => (atom.getPos?).any (· < nameStart)
    unless atoms.size == 1 do throwError "Keyword match count {atoms.size} for {root}"
    let atom := atoms[0]!
    let some start := atom.getPos? | throwError "Missing keyword start"
    let some stop := atom.getTailPos? | throwError "Missing keyword end"
    let .atom _ keyword := atom | throwError "Not keyword atom"
    facts := facts.push (Json.mkObj [("kind", Json.str "keyword"),
      ("name", Json.str rootText), ("module", Json.str moduleName),
      ("keyword", Json.str keyword),
      ("keywordRange", Json.mkObj [("start", positionJson inputCtx.fileMap start),
        ("end", positionJson inputCtx.fileMap stop)])])
    let ci ← getConstInfo root
    let typeJson ← orThrow (NumericSourceAudit.encodeExpr ci.type)
    let axioms ← collectAxioms root
    for ax in axioms do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Unexpected original axiom {ax} in {root}"
    records := records.push (Json.mkObj [("name", Json.str rootText),
      ("nameExpr", NumericSourceAudit.encodeName root),
      ("module", Json.str moduleName), ("sourceSha256", Json.str sourceSha),
      ("levelParams", Json.arr (ci.levelParams.toArray.map NumericSourceAudit.encodeName)),
      ("levelParamDisplay", toJson (ci.levelParams.map Name.toString)),
      ("elaboratedExpr", typeJson), ("axioms", toJson (axioms.map Name.toString))])
  IO.FS.writeFile (output ++ "/keywords.jsonl")
    (String.intercalate "\n" (facts.toList.map Json.compress) ++ "\n")
  IO.FS.writeFile (output ++ "/original-exprs.json") ((Json.mkObj [
    ("schema", Json.str "numeric-source-original-expr-v1"),
    ("compilerVersion", Json.str Lean.versionString),
    ("serialization", Json.str "compiler ConstantInfo.type; recursive metadata erasure; no pretty-printer round-trip"),
    ("records", Json.arr records)]).pretty ++ "\n")
  logInfo s!"Exported {records.size} original numeric theorem types and parser keyword ranges"

end NumericSourceFacts

#print axioms Iut.assembly
#print axioms Iut.c2_final
