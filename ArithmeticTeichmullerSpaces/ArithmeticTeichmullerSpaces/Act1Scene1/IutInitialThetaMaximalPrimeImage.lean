/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

original-path: `refer/iut/Iut/Concrete/SL2Image.lean`
original-author: Christian Merten (Git author); The iut contributors (file authors)
original-commit: `47ef99c97945984ea799ee2333fcf920abecdae4`
source-snapshot: `07cb1da58f6d428a670dbb5dd6093d428bcbcdd8`
license: Apache-2.0 (see project `LICENSE`)
modification: derives the candidate-prime image condition on the complete odd
support and supplies it to the local maximal admissible-prime constructor.
-/
import ArithmeticTeichmullerSpaces.Act1Scene1.IutSL2ImageSourceBridge
import ArithmeticTeichmullerSpaces.Act1Scene1.IutTateParameterCompletion

/-!
source-id: IUT-COR312-INITIAL-THETA-MAXIMAL-PRIME-IMAGE
source: `refer/iut/Iut/Concrete/SL2Image.lean`, `prime_dvd_card_range`
and `sl_le_range_of`; local full-support Tate parameters and the elementary
prime bound; `Iut/Concrete/Existence.lean`, `primeData`.
fidelity: derives the local Tate source for an arbitrary candidate-prime
representation. The elementary bound supplies coprime Tate orders and the
residue-characteristic witness. Absence of a Galois-stable subgroup of order
ell gives SL2 inclusion, which the maximal prime constructor consumes.
The representation and cyclic-subgroup condition remain explicit. No image
field of the original initial Theta prime is used. No new InitialThetaData,
paper representatives or theta-volume model is constructed.
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
variable {ell : ℕ} (R : IutCurveModEllRepData D.F D.E D.Fbar ell)

private theorem maximalPrime_rep_badPlace
    {w : FinitePlace D.F} (hw : w ∈ IutOddMultiplicativeSupport D)
    (w' : FinitePlace ↥R.torsionField) (hw'w : FinitePlace.LiesOver w' w) :
    IsBadPlace D.E R.torsionField (IutOddMultiplicativeModSupport D) w' := by
  let K := R.torsionField
  rw [iutOddMultiplicativeSupport_eq_badPlacesOver_modSupport D] at hw
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

private theorem maximalPrime_uniformizer (w : FinitePlace D.F) :
    IsUniformizer (Arithmetic.completionUniformizer w) := by
  have h := Arithmetic.completionUniformizer_isCompletionUniformizer w
  exact ⟨h.ne_zero, h.norm_lt_one, h.generates⟩

/-- A large candidate prime has the full local Tate source on the complete odd support. -/
theorem iutInitialThetaMaximalPrimeLocalTateImageSource
    (hp : ell.Prime) (hLarge : iutInitialThetaElementaryPrimeBound D < ell) :
    R.LocalTateImageSource (IutOddMultiplicativeSupport D) := by
  intro w _h2 hw _hwEll w' hw'w
  let K := R.torsionField
  letI : Algebra ↥(fieldOfModuli D.F D.E) ↥K :=
    (fieldOfModuli D.F D.E).instAlgebraSubtypeMem
  have hBad : IsBadPlace D.E K (IutOddMultiplicativeModSupport D) w' :=
    maximalPrime_rep_badPlace D R hw w' hw'w
  have hOver : Ideal.LiesOver w'.maximalIdeal.asIdeal w.maximalIdeal.asIdeal := hw'w
  have hOdd : ∀ v ∈ IutOddMultiplicativeModSupport D, residueChar v ≠ 2 := by
    intro v hv htwo
    have hodd := hv.1
    change Odd (residueChar v) at hodd
    rw [htwo] at hodd
    norm_num at hodd
  let S : TateStructure (curveKw D.E K w') :=
    tateStructureOfTorsion D.E K ell hOdd
      (fun _ hv => hv.2.2) hp
      (by have := (iutInitialThetaElementaryPrimeBound_spec D).1; omega)
      R.TK le_rfl (by rw [R.card_torsionBy_EK, pow_two]) hBad
  let t := iutInitialThetaOddSupportBaseTateParameterAtCurvePlace D w hw
  let B := iutInitialThetaOddSupportBaseQPilotSource D
  have hwB : w ∈ B.badFinset := (Set.ext_iff.mp B.badFinset_spec w).mpr hw
  refine ⟨t, Arithmetic.completionUniformizer w, maximalPrime_uniformizer D w,
    S, ?_, ?_, ?_⟩
  · apply iutTateParameter_q_eq_of_tateJ_eq hOver
    rw [← iutTateJ_embed hOver,
      iutInitialThetaOddSupportBaseTateParameterAtCurvePlace_tateJ_eq D w hw,
      iutEmbedCompletion_embedding hOver, iutTateStructure_tateJ_eq,
      iutCurve_j_eq_div]
    simp only [curveKw, curveK, WeierstrassCurve.map_c₄,
      WeierstrassCurve.map_Δ, map_div₀, map_pow]
  · letI : NeZero ell := ⟨hp.ne_zero⟩
    letI : Finite ↥(TateStructure.torsion ell (curveKw D.E K w')) :=
      S.finite_torsion ell
    exact R.card_torsion_curveKw_ge w'
  · have hnorm : ‖B.tateParameter ⟨w, hwB⟩‖ =
        ‖Arithmetic.completionUniformizer w‖ ^
          (t.toOrdered (maximalPrime_uniformizer D w)).orderNat :=
      t.norm_q_eq_pow_orderNat (maximalPrime_uniformizer D w)
    have hOrder := iutCompletionQOrder_eq_of_norm_eq_uniformizer_pow w
      (B.tateParameter ⟨w, hwB⟩) (B.tateParameter_ne_zero ⟨w, hwB⟩)
      (B.tateParameter_norm_lt_one ⟨w, hwB⟩) (Arithmetic.completionUniformizer w)
      (Arithmetic.completionUniformizer_isCompletionUniformizer w) _ hnorm
    have hcop := iutInitialThetaOddSupportQOrder_coprime_of_largePrime D hp hLarge ⟨w, hwB⟩
    change Nat.Coprime ell (iutCompletionQOrder w (B.tateParameter ⟨w, hwB⟩)) at hcop
    rw [hOrder] at hcop
    intro hdvd
    exact hp.ne_one (Nat.eq_one_of_dvd_coprimes hcop (dvd_refl ell) hdvd)

/-- Nonemptiness and the curve bound supply the candidate-prime local witness. -/
theorem iutInitialThetaMaximalPrime_exists_residueChar_ne_two_ell
    (hLarge : iutInitialThetaElementaryPrimeBound D < ell) :
    ∃ w : FinitePlace D.F, w ∈ IutOddMultiplicativeSupport D ∧
      residueChar w ≠ 2 ∧ residueChar w ≠ ell := by
  obtain ⟨v, hv⟩ := D.global.bad_nonempty
  obtain ⟨w, hwv⟩ := FinitePlace.exists_liesOver (K := D.F) v
  have hw : w ∈ badPlacesOver D.F D.E D.VBad := ⟨v, hv, hwv⟩
  have hFull := iutBadPlacesOver_subset_oddMultiplicativeSupport D hw
  refine ⟨w, hFull, ?_, ?_⟩
  · intro htwo
    have hodd := hFull.1
    change Odd (residueChar w) at hodd
    rw [htwo] at hodd
    norm_num at hodd
  · have hlt := (iutMultiplicative_residueChar_le_bound D.E w hFull.2).trans_lt
      ((iutInitialThetaElementaryPrimeBound_spec D).2.1.trans_lt hLarge)
    exact ne_of_lt hlt

/-- The candidate representation image follows from local Tate data and the cyclic obstruction. -/
theorem iutInitialThetaMaximalPrime_sl_le_range
    (hp : ell.Prime) (hLarge : iutInitialThetaElementaryPrimeBound D < ell)
    (hP4 : ¬ IutHasCyclicSubgroup D.E D.Fbar ell)
    (A : Matrix.SpecialLinearGroup (Fin 2) (ZMod ell)) : A.toGL ∈ R.rep.range := by
  exact R.sl_le_range_of_local_tate hp
    (iutInitialThetaMaximalPrime_exists_residueChar_ne_two_ell D hLarge)
    (iutInitialThetaMaximalPrimeLocalTateImageSource D R hp hLarge) hP4 A

/-- Construct maximal admissible-prime data with a proved image condition. -/
def iutInitialThetaMaximalPrimeData_of_not_hasCyclicSubgroup
    (hp : ell.Prime) (hLarge : iutInitialThetaElementaryPrimeBound D < ell)
    (hP4 : ¬ IutHasCyclicSubgroup D.E D.Fbar ell) :
    AdmissiblePrimeData D.F D.E D.Fbar (IutOddMultiplicativeModSupport D) :=
  iutInitialThetaMaximalPrimeData D hp hLarge R
    (iutInitialThetaMaximalPrime_sl_le_range D R hp hLarge hP4)

end

end JoshiTeich.Act1Scene1
