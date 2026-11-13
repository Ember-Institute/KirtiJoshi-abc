import Lean
import Definitions.Def_FermatCurveFieldBasic
import Definitions.Def_FermatCurveFieldChart
import Definitions.Def_FermatCurveFieldPlace
import Definitions.Def_FermatCurveFieldResidue
import Definitions.Def_FermatCurveFieldZerosPoles
import Definitions.Def_FermatRiemannSpaces
import Definitions.Def_FermatRiemannComposition
import Definitions.Def_FermatFunctionDivisors
import Definitions.Def_FermatRiemannLocalDimension
import Definitions.Def_FermatRiemannDimensionComposition
open Lean
run_meta do
  let mut rows : Array Json := #[]
  let modules : Array Name := #[`Definitions.Def_FermatCurveFieldBasic, `Definitions.Def_FermatCurveFieldChart, `Definitions.Def_FermatCurveFieldPlace, `Definitions.Def_FermatCurveFieldResidue, `Definitions.Def_FermatCurveFieldZerosPoles, `Definitions.Def_FermatRiemannSpaces, `Definitions.Def_FermatRiemannComposition, `Definitions.Def_FermatFunctionDivisors, `Definitions.Def_FermatRiemannLocalDimension, `Definitions.Def_FermatRiemannDimensionComposition]
  let env ← getEnv
  for (n, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? n | continue
    let some m := env.header.moduleNames[idx.toNat]? | continue
    unless modules.contains m do continue
    let axs ← collectAxioms n
    for ax in axs do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do throwError "Unapproved axiom {ax} in {n}"
    rows := rows.push (Json.mkObj [("name", toJson n.toString), ("axioms", toJson (axs.map toString))])
  IO.FS.writeFile ".local/adaptation/fermat-riemann-20261113/all-definition-axioms.json" (Json.pretty (Json.arr rows))
