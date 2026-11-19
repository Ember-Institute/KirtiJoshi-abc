/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository https://github.com/lana-agents/iut
Original revision 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
Original path Iut/Concrete/LocalConstruct/Theory.lean
-/
import Solutions.Source_ReferenceIutConcreteLocalArchimedean
import Solutions.Source_ReferenceIutConcreteLocalFiniteLogShell
import Solutions.Source_ReferenceIutConcreteLocalProp14

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut.LocalConstruct

open NumberField

universe u

noncomputable section

variable {K : Type u} [Field K] [NumberField K]

/-- The concrete local theory on the finite and archimedean tensor packets of `K`. -/
def concreteLocalTheory : LocalTheory.{u, u} K where
  toLocalTensor := concreteLocalTensor (K := K)
  residueChar_prime := Tripod.residueChar_prime
  fiber_finite := fiber_finite (K := K)
  ramified_finite := ramified_finite (K := K)
  localDeg_pos := localDeg_pos
  ramIdx_pos := ramIdx_pos
  ordDifferent_eq_zero := ordDifferent_eq_zero
  sum_localDeg p hp _ := sum_localDeg (K := K) p hp
  sum_mult := sum_mult (K := K)
  ordp_p := ordp_p
  ordp_mul := ordp_mul
  incl := incl
  isUnit_incl := isUnit_incl
  integral
    | .finite p, c => LocalConstruct.integral p c
    | .infinite, c => archIntegral c
  one_mem_integral
    | .finite p, c => LocalConstruct.one_mem_integral p c
    | .infinite, c => one_mem_archIntegral c
  smul_integral_subset := smul_integral_subset_of_ordp
  logShell
    | .finite p, c => finiteLogShell p c
    | .infinite, c => archLogShell c
  logShell_relCompact
    | .finite p, c => isCompact_closure_finiteLogShell p c
    | .infinite, c => isCompact_closure_archLogShell c
  integral_subset_logShell := integral_subset_finiteLogShell
  logShell_eq_integral := finiteLogShell_eq_integral_of_unramified
  componentVol
    | .finite p, c => finiteComponentVol p c
    | .infinite, c => archComponentVol c
  componentVol_integral
    | .finite p, c => finiteComponentVol_integral p c
    | .infinite, c => archComponentVol_integral c
  componentVol_mono
    | .finite p, c => finiteComponentVol_mono p c
    | .infinite, c => archComponentVol_mono c
  componentVol_arch_scale := archComponentVol_scale
  admissible
    | .finite p, c => finiteAdmissible p c
    | .infinite, c => archAdmissible c
  admissible_nonempty
    | .finite p, c, U, hU => finiteAdmissible_nonempty p c (U := U) hU
    | .infinite, c, U, hU => archAdmissible_nonempty c (S := U) hU
  admissible_relCompact
    | .finite p, c, U, hU => finiteAdmissible_relCompact p c (U := U) hU
    | .infinite, c, U, hU => archAdmissible_relCompact c (S := U) hU
  integral_admissible
    | .finite p, c => finiteAdmissible_integral p c
    | .infinite, c => archIntegral_admissible c
  smul_integral_admissible
    | .finite p, c => finiteAdmissible_smul_integral p c
    | .infinite, c => smul_archIntegral_admissible c
  componentVol_prime_preimage p c hc U hU :=
    finiteComponentVol_prime_preimage_of_admissible p c hc (U := U) hU
  exists_leastHull p c U hU := exists_leastHull_finite p c (U := U) hU
  exists_leastHull_infinite c U hU := LocalConstruct.exists_leastHull_infinite c (S := U) hU
  smul_integral_infinite_mono := smul_archIntegral_mono
  indAut
    | .finite p, c => finiteIndAut p c
    | .infinite, c => archIndAut c
  id_mem_indAut
    | .finite p, c => id_mem_finiteIndAut p c
    | .infinite, c => id_mem_archIndAut c
  indAut_logShell
    | .finite p, c => finiteIndAut_logShell p c
    | .infinite, c => archIndAut_logShell c
  theta_admissible
    | .finite p, c => theta_admissible_finite p c
    | .infinite, c => theta_admissible_infinite c
  thetaShell_admissible
    | .finite p, c => thetaShell_admissible_finite p c
    | .infinite, c => thetaShell_admissible_infinite c
  prop14_iii p c hc := prop14iii_of_isOver p c hc
  prop14_iv := LocalConstruct.prop14_iv
  prop15 := LocalConstruct.prop15

end

end AbcAdaptation.Reference.Iut.LocalConstruct
