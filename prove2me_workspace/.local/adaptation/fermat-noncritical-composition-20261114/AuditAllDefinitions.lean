import Lean
import Definitions.Def_FermatNoncriticalRamificationPositive
open Lean
run_meta do
  let mut rows : Array Json := #[]
  let modules : Array Name := #[`Definitions.Def_FermatNoncriticalRamificationPositive]
  let env ← getEnv
  for (n, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? n | continue
    let some m := env.header.moduleNames[idx.toNat]? | continue
    unless modules.contains m do continue
    let axs ← collectAxioms n
    for ax in axs do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do throwError "Unapproved axiom {ax} in {n}"
    rows := rows.push (Json.mkObj [("name", toJson n.toString), ("axioms", toJson (axs.map toString))])
  IO.FS.writeFile ".local/adaptation/fermat-noncritical-composition-20261114/all-definition-axioms.json" (Json.pretty (Json.arr rows))
