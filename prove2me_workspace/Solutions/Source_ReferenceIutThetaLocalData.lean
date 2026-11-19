/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository https://github.com/lana-agents/iut
Original revision 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
Original path Iut/Concrete/ThetaLocalConstruct/Data.lean
-/
import ArithmeticTeichmullerSpaces.Prologue.Arithmetic.BaseChange
import Solutions.Source_ReferenceIutThetaLocalBadChars
import Solutions.Source_ReferenceIutThetaLocalOrder
import Solutions.Source_ReferenceIutThetaLocalRoots
import Mathlib.Tactic.Positivity

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut

open NumberField
open scoped BigOperators Classical

universe u v

variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}
variable (D : InitialThetaData AG TG) (htwo : TwoTorsionRational D)

/-- The normalized order of a chosen root is the Tate order divided by `2ℓ e_w`. -/
theorem ordp_qrootOf (v : FinitePlace D.Kt) (w : FinitePlace D.F)
    (hvw : FinitePlace.LiesOver v w) (hw : w ∈ badPlacesOver D.F D.E D.VBad) :
    ordp D.Kt v (qrootOf D htwo v) = (D.prime.qOrder w hw : ℝ) / (2 * D.ℓ * ramIdx D.F w) := by
  have hℓ : (D.ℓ : ℝ) ≠ 0 := by exact_mod_cast D.prime.ℓ_prime.ne_zero
  have htwoℓ : (2 * (D.ℓ : ℝ)) ≠ 0 := mul_ne_zero two_ne_zero hℓ
  have hp := JoshiTeich.Prologue.Arithmetic.ordp_pow v (qrootOf D htwo v) (2 * D.ℓ)
  change ordp D.Kt v (qrootOf D htwo v ^ (2 * D.ℓ)) =
    ((2 * D.ℓ : ℕ) : ℝ) * ordp D.Kt v (qrootOf D htwo v) at hp
  rw [qrootOf_pow D htwo v w hvw hw] at hp
  change ordp D.Kt v (embedCompletion hvw ((D.prime.tate w hw).q : localCompletion w)) = _ at hp
  rw [ordp_embedCompletion hvw, ordp_tateParameter _ (D.prime.unif_isUniformizer w hw),
    Nat.cast_mul, Nat.cast_ofNat] at hp
  change (D.prime.qOrder w hw : ℝ) / ramIdx D.F w =
    (2 * (D.ℓ : ℝ)) * ordp D.Kt v (qrootOf D htwo v) at hp
  rw [div_mul_eq_div_div_swap, hp, mul_div_cancel_left₀ _ htwoℓ]

variable (LT : LocalTheory.{u, v} D.Kt)

/-- The sum of normalized root orders over a rational prime is the scaled q-pilot sum. -/
theorem sum_weight_ordp_qrootOf (p : Nat.Primes) (bad : Finset (FinitePlace D.F))
    (hbad : ↑bad = badPlacesOver D.F D.E D.VBad) :
    ∑ v : LT.Fiber (.finite p), LT.weight (.finite p) v * ordp D.Kt (LT.fiberPlace v)
        (qrootOf D htwo (LT.fiberPlace v)) =
      (∑ w ∈ bad.attach.filter (fun w => residueChar w.1 = p),
        (inertDeg D.F w.1 : ℝ) / Module.finrank ℚ D.F *
          (D.prime.qOrder w.1 (hbad ▸ Finset.mem_coe.mpr w.2) : ℝ)) / (2 * D.ℓ) := by
  letI : Fintype {v : FinitePlace D.Kt // residueChar v = (p : ℕ)} :=
    @Fintype.ofFinite _ (LT.fiber_finite p)
  letI : Fintype {v : FinitePlace D.Kt //
      JoshiTeich.Prologue.Arithmetic.residueChar v = (p : ℕ)} :=
    inferInstanceAs (Fintype {v : FinitePlace D.Kt // residueChar v = (p : ℕ)})
  have hfiber : ∑ v : LT.Fiber (.finite p), LT.weight (.finite p) v *
      ordp D.Kt (LT.fiberPlace v) (qrootOf D htwo (LT.fiberPlace v)) =
      ∑ v : {v : FinitePlace D.Kt // residueChar v = (p : ℕ)},
        placeWeight D.Kt v.1 * ordp D.Kt v.1 (qrootOf D htwo v.1) := by
    refine Fintype.sum_equiv (LT.fiberFiniteEquiv p) _ _ ?_
    rintro ⟨w | w, hw⟩
    · rfl
    · exact absurd hw (by simp [LocalTheory.toRational])
  let c : FinitePlace D.F → ℝ := fun w =>
    if hw : w ∈ badPlacesOver D.F D.E D.VBad then (D.prime.qOrder w hw : ℝ) / (2 * D.ℓ) else 0
  have hgroup : ∑ v : {v : FinitePlace D.Kt // residueChar v = (p : ℕ)},
      placeWeight D.Kt v.1 * ordp D.Kt v.1 (qrootOf D htwo v.1) =
      ∑ w ∈ bad.filter (fun w => residueChar w = p),
        (inertDeg D.F w : ℝ) / Module.finrank ℚ D.F * c w := by
    refine JoshiTeich.Prologue.Arithmetic.sum_placeWeight_mul (F := D.F) (L := D.Kt)
      (p : ℕ) (badPlacesOver D.F D.E D.VBad) bad hbad c
      (fun v => ordp D.Kt v (qrootOf D htwo v)) ?_ ?_
    · intro v w hvw hw
      change ordp D.Kt v (qrootOf D htwo v) = c w / ramIdx D.F w
      rw [ordp_qrootOf D htwo v w hvw hw]
      simp only [c, dif_pos hw, div_div]
    · intro v hv
      have hgood : ¬ IsBadK D v := by
        intro h
        obtain ⟨w, hw, hvw⟩ := exists_liesOver_of_isBadK D h
        exact hv w hw hvw
      change ordp D.Kt v (qrootOf D htwo v) = 0
      rw [qrootOf_of_not D htwo hgood]
      simp [ordp]
  rw [hfiber, hgroup, Finset.sum_div, Finset.sum_filter, ← Finset.sum_attach bad,
    Finset.sum_filter]
  refine Finset.sum_congr rfl fun w _ => ?_
  have hw : w.1 ∈ badPlacesOver D.F D.E D.VBad := hbad ▸ Finset.mem_coe.mpr w.2
  by_cases hp : residueChar w.1 = (p : ℕ)
  · simp only [c, dif_pos hw, if_pos hp, mul_div_assoc]
  · simp only [if_neg hp]

/-- The local θ-data formed from the Tate roots and q-pilot of the same initial datum. -/
noncomputable def thetaLocalData (QI : QPilotInputs D) : ThetaLocalData D LT where
  badChars := QI.badChars
  qroot := qrootOf D htwo
  qroot_ne_zero := qrootOf_ne_zero D htwo
  ordp_qroot_nonneg v := by
    by_cases hv : IsBadK D v
    · obtain ⟨w, hw, hvw⟩ := exists_liesOver_of_isBadK D hv
      rw [ordp_qrootOf D htwo v w hvw hw]
      positivity
    · rw [qrootOf_of_not D htwo hv]
      simp [ordp]
  qroot_eq_one v hv := by
    apply qrootOf_of_not D htwo
    intro h
    obtain ⟨w, hw, hvw⟩ := exists_liesOver_of_isBadK D h
    exact hv (QI.mem_badChars.mpr ⟨w, hw, (Tripod.residueChar_eq_of_liesOver hvw).symm⟩)
  embedF := embedFOf D
  qroot_pow := qrootOf_pow D htwo
  ordp_qroot := ordp_qrootOf D htwo
  residueChar_mem _ w hvw hw :=
    QI.mem_badChars.mpr ⟨w, hw, (Tripod.residueChar_eq_of_liesOver hvw).symm⟩
  bad_residueChar_mem w hw := QI.mem_badChars.mpr ⟨w, hw, rfl⟩
  badChars_prime p hp := by
    obtain ⟨w, _, rfl⟩ := QI.mem_badChars.mp hp
    exact Tripod.residueChar_prime w
  sum_weight_ordp_qroot := sum_weight_ordp_qrootOf D htwo LT

end AbcAdaptation.Reference.Iut
