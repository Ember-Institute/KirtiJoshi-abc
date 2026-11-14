import Lean
import Theorems.Thm_AbcAdaptation_Tripod_epsilonELargeHeight
open Lean Elab Parser
partial def findKind? (stx : Syntax) (k : SyntaxNodeKind) : Option Syntax :=
  if stx.getKind == k then some stx else stx.getArgs.findSome? (findKind? · k)
def posJson (fm : FileMap) (p : String.Pos.Raw) : Json :=
  let pos := fm.toPosition p
  Json.mkObj [("line", toJson pos.line), ("col", toJson pos.column), ("offset", toJson p.byteIdx)]
def rangeJson (fm : FileMap) (stx? : Option Syntax) : Json :=
  match stx?.bind fun s => do pure (← s.getPos?, ← s.getTailPos?) with
  | some (s, e) => Json.mkObj [("start", posJson fm s), ("end", posJson fm e)]
  | none => Json.null
run_meta do
  let env ← getEnv
  let env := Parser.parserExtension.activateScoped env `IntermediateField
  let env := Parser.parserExtension.activateScoped env `IntermediateField.algebraAdjoinAdjoin
  let files : Array String := #["Theorems/Thm_AbcAdaptation_Tripod_epsilonELargeHeight.lean"]
  let mut output : Array Json := #[]
  for file in files do
    let input ← IO.FS.readFile file
    let ctx := Parser.mkInputContext input file
    let syntaxModule ← Parser.testParseModule env file input
    for cmd in syntaxModule[1].getArgs do
      if cmd.isOfKind ``Command.namespace || cmd.isOfKind ``Command.end then
        output := output.push (Json.mkObj [("file", toJson file), ("kind", toJson cmd.getKind.toString), ("command", toJson (String.Pos.Raw.extract input (cmd.getPos?.getD 0) (cmd.getTailPos?.getD 0))), ("start", posJson ctx.fileMap (cmd.getPos?.getD 0)), ("end", posJson ctx.fileMap (cmd.getTailPos?.getD 0))])
      let some decl := findKind? cmd ``Command.declaration | continue
      let some declId := findKind? decl ``Command.declId | continue
      let valStx := (findKind? decl ``Command.declValSimple).orElse fun _ =>
        findKind? decl ``Command.declValEqns
      let some ds := decl.getPos? | continue
      let some de := decl.getTailPos? | continue
      output := output.push (Json.mkObj [
        ("file", toJson file), ("nameText", toJson declId[0].getId.toString),
        ("declStart", posJson ctx.fileMap ds), ("declEnd", posJson ctx.fileMap de),
        ("nameRange", rangeJson ctx.fileMap (some declId[0])),
        ("valStart", (valStx.bind (·.getPos?)).map (posJson ctx.fileMap ·) |>.getD Json.null),
        ("docstring", rangeJson ctx.fileMap (findKind? cmd ``Command.docComment))])
  IO.FS.writeFile ".local/adaptation/epsilon-large-height-sourceproof-20261114/syntax-boundaries.json" (Json.pretty (Json.arr output))
