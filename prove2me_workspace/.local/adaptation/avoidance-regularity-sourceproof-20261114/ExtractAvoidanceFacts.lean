import Lean
import Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_avoidanceRegularity

open Lean Elab Parser
set_option pp.fullNames true
set_option pp.funBinderTypes true

partial def findKind? (stx : Syntax) (kind : SyntaxNodeKind) : Option Syntax :=
  if stx.getKind == kind then some stx else stx.getArgs.findSome? (findKind? · kind)

run_meta do
  let env ← getEnv
  let target := `AbcAdaptation.Tripod.Fermat.Proper.avoidanceRegularity
  let moduleName := `Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_avoidanceRegularity
  let ci ← getConstInfo target
  let some ranges ← findDeclarationRanges? target | throwError "Missing declaration range"
  let file := "Theorems/Thm_AbcAdaptation_Tripod_Fermat_Proper_avoidanceRegularity.lean"
  let raw ← IO.FS.readFile file
  let parsed ← Parser.testParseModule env file raw
  let mut spans : Array Json := #[]
  for cmd in parsed[1].getArgs do
    let some decl := findKind? cmd ``Command.declaration | continue
    let some declId := findKind? decl ``Command.declId | continue
    let some s := declId[0].getPos? | continue
    let some e := declId[0].getTailPos? | continue
    spans := spans.push (Json.mkObj [("nameText",toJson declId[0].getId.toString),("start",toJson s.byteIdx),("end",toJson e.byteIdx)])
  let mut axioms : Array Json := #[]
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let some m := env.header.moduleNames[idx.toNat]? | continue
    unless m == moduleName do continue
    let axs ← collectAxioms name
    for ax in axs do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do throwError "Unexpected axiom {ax} in {name}"
    axioms := axioms.push (Json.mkObj [("name",toJson name.toString),("axioms",toJson (axs.map toString))])
  IO.FS.writeFile ".local/adaptation/avoidance-regularity-sourceproof-20261114/compiler-facts.json" (Json.pretty (Json.mkObj [
    ("name",toJson target.toString),("module",toJson moduleName.toString),("file",toJson file),
    ("type",Json.str (← Lean.Meta.ppExpr ci.type).pretty),
    ("start_line",toJson ranges.range.pos.line),("end_line",toJson ranges.range.endPos.line),
    ("name_spans",Json.arr spans),("module_axioms",Json.arr axioms)]))
