/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

original-path: `refer/iut/Iut/Concrete/SL2Image.lean`
original-author: Christian Merten (Git author); The iut contributors (file authors)
original-commit: `47ef99c97945984ea799ee2333fcf920abecdae4`
source-snapshot: `07cb1da58f6d428a670dbb5dd6093d428bcbcdd8`
license: Apache-2.0 (see project `LICENSE`)
modification: constructs local Tate witnesses on the representation fixed field
from actual initial Theta data, using torsion descent and parameter uniqueness.
-/
import ArithmeticTeichmullerSpaces.Act1Scene1.IutSL2ImageSourceBridge
import ArithmeticTeichmullerSpaces.Act1Scene1.IutModEllRepAdmissibleAdapter
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaPrimeToSupport
import ArithmeticTeichmullerSpaces.Act1Scene1.IutTateParameterCompletion

/-!
source-id: IUT-COR312-INITIAL-THETA-LOCAL-TATE-IMAGE
source: `refer/iut/Iut/Concrete/SL2Image.lean`, local Tate/ramification argument;
`Iut/Cor312/ThetaData/TateFamilyOfTorsion.lean`, `tateStructureOfTorsion`;
actual `InitialThetaData.global` and `InitialThetaData.prime` fields.
fidelity: constructs the full local source on the actual VBad pullback. The
Tate structure is derived on the representation fixed field from multiplicative
reduction and rational torsion. Its q parameter agrees with the given base Tate
parameter by j-invariant uniqueness. No SL2-image field is used in this argument.
This does not construct an InitialThetaData or identify paper representatives,
q-sums or theta volumes.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1

open JoshiTeich.Prologue
open NumberField WeierstrassCurve TateCurvesTheta
open JoshiTeich.ReferenceIut
open scoped Classical

universe u

noncomputable section

variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}
variable (D : InitialThetaData AG TG)

private theorem initialTheta_rep_badPlace
    {w : FinitePlace D.F}
    (hw : w ∈ badPlacesOver D.F D.E D.VBad)
    (w' : FinitePlace ↥(iutInitialThetaModEllRepData D).torsionField)
    (hw'w : FinitePlace.LiesOver w' w) :
    IsBadPlace D.E (iutInitialThetaModEllRepData D).torsionField D.VBad w' := by
  let K := (iutInitialThetaModEllRepData D).torsionField
  obtain ⟨v, hv, hwv⟩ := hw
  letI : Algebra ↥(fieldOfModuli D.F D.E) ↥K :=
    (fieldOfModuli D.F D.E).instAlgebraSubtypeMem
  have hmap : algebraMap ↥(fieldOfModuli D.F D.E) ↥K =
      (algebraMap D.F ↥K).comp (algebraMap ↥(fieldOfModuli D.F D.E) D.F) :=
    RingHom.ext fun _ => rfl
  letI : IsScalarTower ↥(fieldOfModuli D.F D.E) D.F ↥K :=
    IsScalarTower.of_algebraMap_eq' hmap
  letI : IsScalarTower (𝓞 ↥(fieldOfModuli D.F D.E)) (𝓞 D.F) (𝓞 ↥K) :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext fun x => by
      apply RingOfIntegers.coe_injective
      exact RingHom.congr_fun hmap x)
  haveI : w'.maximalIdeal.asIdeal.LiesOver w.maximalIdeal.asIdeal := hw'w
  haveI : w.maximalIdeal.asIdeal.LiesOver v.maximalIdeal.asIdeal := hwv
  exact ⟨v, hv, ⟨(Ideal.LiesOver.trans w'.maximalIdeal.asIdeal
    w.maximalIdeal.asIdeal v.maximalIdeal.asIdeal).over⟩⟩

/-- Actual initial Theta data supplies all local Tate witnesses on its VBad pullback. -/
theorem iutInitialThetaLocalTateImageSource :
    (iutInitialThetaModEllRepData D).LocalTateImageSource
      (badPlacesOver D.F D.E D.VBad) := by
  intro w _h2 hw _hwℓ w' hw'w
  let R := iutInitialThetaModEllRepData D
  let K := R.torsionField
  letI : Algebra ↥(fieldOfModuli D.F D.E) ↥K :=
    (fieldOfModuli D.F D.E).instAlgebraSubtypeMem
  have hBad : IsBadPlace D.E K D.VBad w' := initialTheta_rep_badPlace D hw w' hw'w
  have hOver : Ideal.LiesOver w'.maximalIdeal.asIdeal w.maximalIdeal.asIdeal := hw'w
  have hOdd : ∀ v ∈ D.VBad, residueChar v ≠ 2 := by
    intro v hv htwo
    have hodd := D.global.bad_odd v hv
    rw [htwo] at hodd
    norm_num at hodd
  let S : TateStructure (curveKw D.E K w') :=
    tateStructureOfTorsion D.E K D.prime.ℓ hOdd D.global.bad_multiplicative
      D.prime.ℓ_prime (by have := D.prime.five_le; omega)
      R.TK le_rfl (by rw [R.card_torsionBy_EK, pow_two]) hBad
  refine ⟨D.prime.tate w hw, D.prime.unif w hw,
    D.prime.unif_isUniformizer w hw, S, ?_, ?_, ?_⟩
  · apply iutTateParameter_q_eq_of_tateJ_eq hOver
    rw [← iutTateJ_embed hOver, D.prime.tateJ_eq w hw,
      iutEmbedCompletion_embedding hOver, iutTateStructure_tateJ_eq,
      iutCurve_j_eq_div]
    simp only [curveKw, curveK, WeierstrassCurve.map_c₄,
      WeierstrassCurve.map_Δ, map_div₀, map_pow]
  · letI : NeZero D.prime.ℓ := ⟨D.prime.ℓ_prime.ne_zero⟩
    letI : Finite ↥(TateStructure.torsion D.prime.ℓ (curveKw D.E K w')) :=
      S.finite_torsion D.prime.ℓ
    exact R.card_torsion_curveKw_ge w'
  · have hcop := ((D.prime.tate w hw).toOrdered_primeToOrder_iff
      (D.prime.unif_isUniformizer w hw) D.prime.ℓ).mp
        (D.prime.q_order_coprime w hw)
    intro hdvd
    have hone := Nat.eq_one_of_dvd_coprimes hcop (dvd_refl D.prime.ℓ) hdvd
    exact D.prime.ℓ_prime.ne_one hone

/-- The local Tate source gives prime divisibility of the actual representation image. -/
theorem iutInitialThetaPrime_dvd_card_range_of_local_tate :
    D.prime.ℓ ∣ Nat.card (iutInitialThetaModEllRepData D).rep.range := by
  apply IutCurveModEllRepData.prime_dvd_card_range_of_local_tate
    (iutInitialThetaModEllRepData D) D.prime.ℓ_prime
  · exact iutInitialThetaBadPlacesOver_exists_residueChar_ne_two_ell D
  · exact iutInitialThetaLocalTateImageSource D

end

end JoshiTeich.Act1Scene1
