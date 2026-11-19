/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository https://github.com/lana-agents/iut
Original revision 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
Original path Iut/Concrete/Existence.lean
-/
import Definitions.Def_AbcAdaptation_Reference_Iut_Concrete_LocalHeightDataAssembly
import Definitions.Def_AbcAdaptation_Reference_Iut_Concrete_TripodalInvariants
import Mathlib.Data.Nat.Prime.Basic

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut.EllipticCurveData

open NumberField
open scoped Classical

universe u

variable (C : EllipticCurveData.{u})

/-- Every place of the base field above the selected bad places is multiplicative. -/
lemma mem_badAll_of_mem_badPlacesOver {ℓ : ℕ} {w : FinitePlace C.F}
    (hw : w ∈ badPlacesOver C.F C.E (C.VBadOf ℓ)) : w ∈ C.badAll := by
  obtain ⟨v, hv, hwv⟩ := hw
  exact hv.2.2.2 w hwv

/-- The global conditions of IUT I, Definition 3.1(a)–(b), for the selected bad places. -/
theorem globalData (CA : C.CurveArithmetic) {ℓ : ℕ}
    (hP5 : ∃ w ∈ C.badAll, residueChar w ≠ 2 ∧ residueChar w ≠ ℓ) :
    IsInitialThetaGlobalData C.F C.E C.Fbar (C.VBadOf ℓ) where
  sqrt_neg_one := CA.sqrt_neg_one
  stable_reduction := CA.stable_reduction
  six_torsion_rational := CA.six_torsion_rational
  bad_nonempty := by
    obtain ⟨w, hw, h2, hℓ⟩ := hP5
    obtain ⟨v, hwv⟩ := CA.exists_liesOver w
    have hres := CA.residueChar_liesOver v w hwv
    have hv2 : residueChar v ≠ 2 := fun h => h2 (hres.trans h)
    have hvℓ : residueChar v ≠ ℓ := fun h => hℓ (hres.trans h)
    refine ⟨v, ?_⟩
    exact ⟨hv2, hvℓ, ⟨w, hwv⟩, fun w' hw' => CA.mult_invariant v hv2 w w' hwv hw' hw⟩
  bad_odd v hv := (residueChar_prime v).odd_of_ne_two hv.1
  bad_multiplicative v hv w hwv := hv.2.2.2 w hwv

/-- The admissible prime datum of IUT I, Definition 3.1(b)–(c), for the given curve. -/
noncomputable def primeData (CA : C.CurveArithmetic) (TI : C.TateInputs) {ℓ : ℕ}
    (hℓ : ℓ.Prime) (h7 : 7 ≤ ℓ) (R : C.ModEllRepData ℓ)
    (hsl : ∀ A : Matrix.SpecialLinearGroup (Fin 2) (ZMod ℓ), A.toGL ∈ R.rep.range)
    (hP2 : ∀ w (hw : w ∈ C.badAll), ¬ ℓ ∣ TI.qOrder w hw) :
    AdmissiblePrimeData C.F C.E C.Fbar (C.VBadOf ℓ) where
  ℓ := ℓ
  ℓ_prime := hℓ
  five_le := (show 5 ≤ (7 : ℕ) by decide).trans h7
  torsionBasis := R.torsionBasis
  rep := R.rep
  rep_spec := R.rep_spec
  sl_le_range := hsl
  ker_isOpen := R.ker_isOpen
  galois_deg_prime := CA.galois_deg_prime ℓ hℓ h7
  residueChar_coprime v hv :=
    (Nat.coprime_primes hℓ (residueChar_prime v)).mpr (Ne.symm hv.2.1)
  tate w hw := TI.tate w (C.mem_badAll_of_mem_badPlacesOver hw)
  tateJ_eq w hw := TI.tateJ_eq w (C.mem_badAll_of_mem_badPlacesOver hw)
  unif w hw := TI.unif w (C.mem_badAll_of_mem_badPlacesOver hw)
  unif_isUniformizer w hw := TI.unif_isUniformizer w (C.mem_badAll_of_mem_badPlacesOver hw)
  q_order_coprime w hw :=
    (hℓ.coprime_iff_not_dvd).mpr (hP2 w (C.mem_badAll_of_mem_badPlacesOver hw))

end AbcAdaptation.Reference.Iut.EllipticCurveData
