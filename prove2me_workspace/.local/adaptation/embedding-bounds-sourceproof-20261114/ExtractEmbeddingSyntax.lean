import Lean
import Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_embeddingBoundsToSet
open Lean Elab Parser
open scoped WithZero Real Classical
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
  let files : Array String := #["Solutions/Source_TripodLocalPlaceEmbeddingBasic.lean","Solutions/Source_TripodLocalPlaceEmbeddingDegree.lean","Solutions/Source_TripodLocalPlaceEmbedding.lean","Solutions/Source_TripodLocalEmbeddingBounds.lean","Solutions/Source_FermatEmbeddingBoundsSource.lean","Theorems/Thm_AbcAdaptation_Tripod_Fermat_Proper_embeddingBoundsToSet.lean"]
  let mut output : Array Json := #[]
  for file in files do
    let input ← IO.FS.readFile file
    let ctx := Parser.mkInputContext input file
    let syntaxModule ← Parser.testParseModule env file input
    for cmd in syntaxModule[1].getArgs do
      let some declId := findKind? cmd ``Command.declId | continue
      let decl := (findKind? cmd ``Command.declaration).getD cmd
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
  IO.FS.writeFile ".local/adaptation/embedding-bounds-sourceproof-20261114/syntax-boundaries.json" (Json.pretty (Json.arr output))
