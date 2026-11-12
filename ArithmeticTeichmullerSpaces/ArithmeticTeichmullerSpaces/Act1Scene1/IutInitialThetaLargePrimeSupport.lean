/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

original-path: `refer/iut/Iut/Concrete/CurveArithmeticProved.lean`
original-commit: `a2c25b2edbf5a9cbc30588b466a738b49547b443`
source-snapshot: `07cb1da58f6d428a670dbb5dd6093d428bcbcdd8`
license: Apache-2.0 (see project `LICENSE`)
modification: adapts the `badAll_finite` proof to bound multiplicative residue
characteristics. Connects this bound to the local support and q-pilot proofs.
-/
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaPrimeToSupport
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaFullSupportCanonicalAbsLogQ

namespace JoshiTeich.Act1Scene1

open JoshiTeich.Prologue
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped BigOperators

universe u

noncomputable section

/-!
source-id: IUT-COR312-INITIAL-THETA-LARGE-PRIME-SUPPORT
source: mathlib `FinitePlace.hasFiniteMulSupport`; the local port of
`one_lt_valuation_j_of_mult`; the S1.202 prime-to-ell support identity;
JoshiTeich, Arithmetic Teichmuller Spaces III, Section 3 and
`th:moccor-Mochizuki-form2` (sufficiently large ell).
fidelity: gives a bound depending only on the base curve and field, above
which there are no multiplicative places. The maximal prime-to-ell VBad
choice then supplies the full-support equality used by S1.200. The VBad
choice and the admissible-prime construction remain explicit source inputs.
boundary: Scene1/Derived
-/

/-- An upper bound for multiplicative residue characteristics. The finite
j-support may also contain places without multiplicative reduction. -/
noncomputable def iutMultiplicativeResidueBound
    {F : Type u} [Field F] [NumberField F]
    (E : WeierstrassCurve F) [E.IsElliptic] : ℕ := by
  classical
  exact if hj : E.j = 0 then 0
    else (NumberField.FinitePlace.hasFiniteMulSupport hj).toFinset.sup
      Arithmetic.residueChar

/-- Multiplicative reduction forces membership in the finite j-support. -/
theorem iutMultiplicative_residueChar_le_bound
    {F : Type u} [Field F] [NumberField F]
    (E : WeierstrassCurve F) [E.IsElliptic]
    (w : NumberField.FinitePlace F)
    (hw : JoshiTeich.ReferenceIut.HasMultiplicativeReductionAt E w) :
    Arithmetic.residueChar w ≤ iutMultiplicativeResidueBound E := by
  classical
  have hVal := JoshiTeich.ReferenceIut.one_lt_valuation_j_of_mult E w hw
  by_cases hj : E.j = 0
  · rw [hj, map_zero] at hVal
    exact (not_lt_of_ge zero_le_one hVal).elim
  · rw [iutMultiplicativeResidueBound, dif_neg hj]
    apply Finset.le_sup
    apply (NumberField.FinitePlace.hasFiniteMulSupport hj).mem_toFinset.mpr
    rw [Function.mem_mulSupport, ← NumberField.FinitePlace.norm_embedding_eq]
    intro hNorm
    have hNormVal :
        ‖(FinitePlace.embedding w.maximalIdeal E.j :
          JoshiTeich.ReferenceIut.localCompletion w)‖ ≤ 1 ↔
        w.maximalIdeal.valuation F E.j ≤ 1 := by
      rw [JoshiTeich.ReferenceIut.norm_le_one_iff_valued,
        FinitePlace.embedding_apply, valuedAdicCompletion_eq_valuation']
    have hLe := hNormVal.mp hNorm.le
    exact not_le_of_gt hVal hLe

/-- The threshold is uniform in the candidate residue characteristic p. -/
theorem iutMultiplicative_noReduction_of_residueChar_gt_bound
    {F : Type u} [Field F] [NumberField F]
    (E : WeierstrassCurve F) [E.IsElliptic]
    {p : ℕ} (hLarge : iutMultiplicativeResidueBound E < p)
    (w : NumberField.FinitePlace F) (hChar : Arithmetic.residueChar w = p) :
    ¬ JoshiTeich.ReferenceIut.HasMultiplicativeReductionAt E w := by
  intro hw
  have hLe := iutMultiplicative_residueChar_le_bound E w hw
  rw [hChar] at hLe
  exact not_le_of_gt hLarge hLe

variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}

/-- The maximal prime-to-ell VBad choice covers the full odd support once
ell is above the curve bound. -/
theorem iutInitialThetaOddMultiplicativeSupport_eq_badPlacesOver_of_largePrime
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    (hVBad : D.VBad = {v | v ∈ IutOddMultiplicativeModSupport D ∧
      Arithmetic.residueChar v ≠ D.prime.ℓ})
    (hLarge : iutMultiplicativeResidueBound D.E < D.prime.ℓ) :
    IutOddMultiplicativeSupport D =
      JoshiTeich.ReferenceIut.badPlacesOver D.F D.E D.VBad := by
  apply
    (iutInitialThetaOddMultiplicativeSupport_eq_badPlacesOver_iff_no_multiplicative_at_ell
      D hVBad).mpr
  exact iutMultiplicative_noReduction_of_residueChar_gt_bound D.E hLarge

/-- S1.200 consumes the derived carrier equality; it no longer requires
the caller to supply that equality separately on this large-prime route. -/
theorem iutInitialThetaOddSupportWeighted_logSum_eq_reference_absLogQ_of_largePrime
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    (hVBad : D.VBad = {v | v ∈ IutOddMultiplicativeModSupport D ∧
      Arithmetic.residueChar v ≠ D.prime.ℓ})
    (hLarge : iutMultiplicativeResidueBound D.E < D.prime.ℓ) :
    let B := iutInitialThetaOddSupportBaseQPilotSource D
    ∑ p ∈ B.badFinset.image Arithmetic.residueChar,
        Real.log p * IutTorsionQRootSource.iutInitialThetaOddSupportWeightedFiber D p =
      JoshiTeich.ReferenceIut.QPilotData.absLogQ
        (IutTorsionQRootSource.iutInitialThetaQPilotData D) := by
  exact iutInitialThetaOddSupportWeighted_logSum_eq_reference_absLogQ_of_support_eq D
    (iutInitialThetaOddMultiplicativeSupport_eq_badPlacesOver_of_largePrime D hVBad hLarge)

end

end JoshiTeich.Act1Scene1
