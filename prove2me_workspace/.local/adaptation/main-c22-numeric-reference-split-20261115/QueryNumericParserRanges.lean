import Lean
import Iut.Implication.Corollary22
open Lean Elab Parser
namespace NumericParserRanges

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


def orThrow {α : Type} (value : Except String α) : MetaM α :=
  match value with
  | .ok x => pure x
  | .error e => throwError "{e}"

partial def keywordAtoms (stx : Syntax) : Array Syntax :=
  match stx with
  | .atom _ value => if value == "theorem" || value == "lemma" then #[stx] else #[]
  | .node _ _ children => children.foldl (fun found child => found ++ keywordAtoms child) #[]
  | _ => #[]

run_meta do
  unless Lean.versionString == "4.35.0-rc3" do throwError "Expected original compiler 4.35.0-rc3"
  let some configPath ← IO.getEnv "NUMERIC_PARSER_CONFIG" | throwError "Missing NUMERIC_PARSER_CONFIG"
  let config ← orThrow (Json.parse (← IO.FS.readFile configPath))
  let output ← orThrow (config.getObjValAs? String "outputDir")
  let entries ← orThrow (config.getObjValAs? (Array Json) "sources")
  IO.FS.createDirAll output
  let env ← getEnv
  for entry in entries do
    let source ← orThrow (entry.getObjValAs? String "source")
    let rootText ← orThrow (entry.getObjValAs? String "name")
    let moduleName ← orThrow (entry.getObjValAs? String "module")
    let sha ← orThrow (entry.getObjValAs? String "normalizedSha256")
    let root := rootText.toName
    let inputCtx := Parser.mkInputContext (← IO.FS.readFile source) source
    let normalized := inputCtx.inputString
    let coordinateSource := output ++ "/" ++ moduleName.replace "." "-" ++ ".normalized.lean"
    IO.FS.writeFile coordinateSource normalized
    -- Parser only: do not call processHeader/processCommands or re-elaborate.
    let syntaxModule ← Parser.testParseModule env source normalized
    let fm := inputCtx.fileMap
    let some ranges ← findDeclarationRanges? root | throwError "No original range: {root}"
    let mut facts : Array Json := #[Json.mkObj [
      ("kind", Json.str "source"), ("schema", Json.str "numeric-parser-ranges-v1"),
      ("name", Json.str rootText), ("module", Json.str moduleName),
      ("source", Json.str source), ("coordinateSource", Json.str coordinateSource),
      ("offsetCoordinate", Json.str "lean-normalized-utf8"),
      ("normalizedSha256Expected", Json.str sha), ("byteLength", toJson normalized.utf8ByteSize),
      ("headerSyntax", syntaxJson fm syntaxModule[0])]]
    let mut matched : Array Syntax := #[]
    let commands := syntaxModule[1].getArgs
    for cmd in commands do
      let isDecl := (findKind? cmd ``Command.declaration).isSome || (findKind? cmd ``Command.declId).isSome
      facts := facts.push (Json.mkObj [("kind", Json.str "command"),
        ("syntaxKind", Json.str cmd.getKind.toString),
        ("isDeclaration", toJson isDecl), ("range", rangeJson fm (some cmd)),
        ("generationIssue", (generationIssue cmd).map Json.str |>.getD Json.null),
        ("contextSyntax", if isDecl then Json.null else syntaxJson fm cmd)])
      let some declId := findKind? cmd ``Command.declId | continue
      let some pos := declId[0].getPos? | continue
      if fm.toPosition pos == ranges.selectionRange.pos then matched := matched.push cmd
    unless matched.size == 1 do throwError "Original target join count {matched.size}: {root}"
    let cmd := matched[0]!
    if let some problem := generationIssue cmd then throwError "Unsupported target command: {problem}"
    let some declId := findKind? cmd ``Command.declId | throwError "Missing binding AST"
    let some start := cmd.getPos? | throwError "Missing command start"
    let some stop := cmd.getTailPos? | throwError "Missing command end"
    let some bindingStart := declId[0].getPos? | throwError "Missing binding position"
    let some value := findKind? cmd ``Command.declValSimple | throwError "Target is not simple value"
    let some valueStart := value.getPos? | throwError "Missing proof value start"
    let atoms := (keywordAtoms cmd).filter fun a => (a.getPos?).any (· < bindingStart)
    unless atoms.size == 1 do throwError "Keyword join count {atoms.size}"
    let .atom _ keyword := atoms[0]! | throwError "Keyword not atom"
    facts := facts.push (Json.mkObj [
      ("kind", Json.str "decl"), ("name", Json.str rootText),
      ("nameText", Json.str declId[0].getId.toString),
      ("commandKind", Json.str cmd.getKind.toString),
      ("generationIssue", Json.null), ("declStart", posJson fm start),
      ("declEnd", posJson fm stop), ("nameRange", rangeJson fm (some declId[0])),
      ("docstring", rangeJson fm (findKind? cmd ``Command.docComment)),
      ("privateTok", rangeJson fm (findKind? cmd ``Command.private)),
      ("valStart", posJson fm valueStart), ("valKind", Json.str "simple"),
      ("valueRange", rangeJson fm (some value)),
      ("signatureSyntax", Json.arr ((collectKinds cmd #[``Command.declSig, ``Command.optDeclSig]).map (syntaxJson fm))),
      ("keyword", Json.str keyword), ("keywordRange", rangeJson fm (some atoms[0]!))])
    facts := facts.push (Json.mkObj [("kind", Json.str "summary"),
      ("status", Json.str "success"), ("name", Json.str rootText),
      ("mode", Json.str "parser-only-no-reelaboration"),
      ("targetCount", toJson (1 : Nat)), ("commandCount", toJson commands.size)])
    let path := output ++ "/" ++ rootText.replace "." "-" ++ ".jsonl"
    IO.FS.writeFile path (String.intercalate "\n" (facts.toList.map Json.compress) ++ "\n")
    logInfo s!"Parser-only source ranges for {root}: {path}"

end NumericParserRanges
