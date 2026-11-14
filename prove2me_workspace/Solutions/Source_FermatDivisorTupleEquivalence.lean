/-
Copyright (c) 2026 The heights contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The heights contributors

Independent source-proof adaptation; receipts are recorded with this unit. Complete source bodies from
Heights/Curve/LinearEquiv.lean:61-108, at
721496ca4c158e511d25d8ccf6bfe8503eda73c1.
Only these missing comparison consequences are added. Existing tupleHeight,
minOrd, Segre, scaling and monotonicity declarations are imported and reused.
-/
import Solutions.Source_FermatPolarPresentationHeights
import Solutions.Source_FermatPolarIntegrality

set_option autoImplicit false
namespace AbcAdaptation.Tripod.Fermat.Proper.PolarTuple
open AbcAdaptation.Tripod.Fermat.Proper
open scoped Classical
variable {K : Type*} [Field K] [CharZero K] [IsCurveField K] {ι κ ι' κ' : Type*}
  [Fintype ι] [Fintype κ] [Fintype ι'] [Fintype κ']

/-- **Tuples with the same divisor have boundedly different heights.** -/
theorem abs_tupleHeight_sub_le_of_minOrd_eq {s : ι → K} {t : κ → K} (hs : ∃ i, s i ≠ 0)
    (ht : ∃ j, t j ≠ 0) (heq : ∀ P : Place K, minOrd P s = minOrd P t) :
    ∃ C, ∀ x : QbarPoint K, |tupleHeight s x - tupleHeight t x| ≤ C := by
  obtain ⟨C₁, hC₁⟩ := tupleHeight_le_of_minOrd_le hs ht fun P => (heq P).ge
  obtain ⟨C₂, hC₂⟩ := tupleHeight_le_of_minOrd_le ht hs fun P => (heq P).le
  refine ⟨max C₁ C₂, fun x => abs_le.mpr ⟨?_, ?_⟩⟩
  · linarith [hC₂ x, le_max_right C₁ C₂]
  · linarith [hC₁ x, le_max_left C₁ C₂]

/-- **Invariance under linear equivalence and additivity**: if
`A_s − A_{s'} = A_u − A_{u'} + div r`, i.e. `minOrd s + minOrd u' = minOrd u + minOrd s' + ord r`
at every place, then `h_s − h_{s'} ≈ h_u − h_{u'}`. -/
theorem abs_tupleHeight_sub_sub_le {s : ι → K} {s' : κ → K} {u : ι' → K} {u' : κ' → K}
    (hs : ∃ i, s i ≠ 0) (hs' : ∃ i, s' i ≠ 0) (hu : ∃ i, u i ≠ 0) (hu' : ∃ i, u' i ≠ 0)
    {r : K} (hr : r ≠ 0)
    (heq : ∀ P : Place K, minOrd P s + minOrd P u' = P.ord r + (minOrd P u + minOrd P s')) :
    ∃ C, ∀ x : QbarPoint K,
      |(tupleHeight s x - tupleHeight s' x) - (tupleHeight u x - tupleHeight u' x)| ≤ C := by
  set S : ι × κ' → K := fun p => s p.1 * u' p.2
  set T₀ : ι' × κ → K := fun p => u p.1 * s' p.2
  set T : ι' × κ → K := fun p => r * T₀ p
  have hS : ∃ p, S p ≠ 0 := ⟨(normIdx (Classical.arbitrary (Place K)) s hs,
    normIdx (Classical.arbitrary (Place K)) u' hu'),
    mul_ne_zero (normIdx_ne_zero hs) (normIdx_ne_zero hu')⟩
  have hT₀ : ∃ p, T₀ p ≠ 0 := ⟨(normIdx (Classical.arbitrary (Place K)) u hu,
    normIdx (Classical.arbitrary (Place K)) s' hs'),
    mul_ne_zero (normIdx_ne_zero hu) (normIdx_ne_zero hs')⟩
  have hT : ∃ p, T p ≠ 0 := by
    obtain ⟨p, hp⟩ := hT₀
    exact ⟨p, mul_ne_zero hr hp⟩
  obtain ⟨C, hC⟩ := abs_tupleHeight_sub_le_of_minOrd_eq hS hT fun P => by
    change minOrd P (fun p : ι × κ' => s p.1 * u' p.2) =
      minOrd P (fun p => r * (fun p : ι' × κ => u p.1 * s' p.2) p)
    rw [minOrd_mul hs hu', minOrd_smul hT₀ hr, minOrd_mul hu hs', heq P]
  refine ⟨C, fun x => ?_⟩
  have h1 : tupleHeight S x = tupleHeight s x + tupleHeight u' x := tupleHeight_mul hs hu' x
  have h2 : tupleHeight T x = tupleHeight u x + tupleHeight s' x := by
    change tupleHeight (fun p => r * T₀ p) x = _
    rw [tupleHeight_smul x hr]
    exact tupleHeight_mul hu hs' x
  have := hC x
  rw [h1, h2] at this
  calc |(tupleHeight s x - tupleHeight s' x) - (tupleHeight u x - tupleHeight u' x)|
      = |(tupleHeight s x + tupleHeight u' x) - (tupleHeight u x + tupleHeight s' x)| := by
        congr 1
        ring
    _ ≤ C := this


end AbcAdaptation.Tripod.Fermat.Proper.PolarTuple
