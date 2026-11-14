/-
Independent source-proof adaptation; validation is recorded in this unit's CI receipts.
Exact original target, using supplied RD and RE without replacement.
Adapted from Heights/Curve/LinearEquiv.lean:74 and TupleHeight.lean:249,268,
with the actual local divisor coefficients and actual minimal-field height.
-/
import Solutions.Source_FermatPolarMinOrd
import Definitions.Def_FermatProperDivisorHeight

set_option autoImplicit false

namespace AbcAdaptation.Tripod.Fermat.Proper

open scoped Classical

namespace PolarTuple

variable {K : Type*} [Field K] [CharZero K] [IsCurveField K]

abbrev pairOne (f : K) : Fin 2 → K := ![1, f]

theorem pairOne_nonzero (f : K) : ∃ i, pairOne f i ≠ 0 := ⟨0, by simp [pairOne]⟩

/-- The zero entry is excluded by minOrd; the result still holds at f=0. -/
theorem minOrd_pairOne (P : Place K) (f : K) :
    minOrd P (pairOne f) = min 0 (P.ord f) := by
  have h0 : minOrd P (pairOne f) ≤ 0 := by
    simpa [pairOne] using
      (minOrd_le (P := P) (pairOne_nonzero f) (j := 0) (by simp [pairOne]))
  apply le_antisymm
  · rcases eq_or_ne f 0 with rfl | hf
    · simpa only [Place.ord_zero, min_self] using h0
    · apply le_min h0
      simpa [pairOne] using
        (minOrd_le (P := P) (pairOne_nonzero f) (j := 1) (by simpa [pairOne] using hf))
  · rw [minOrd_eq (pairOne_nonzero f)]
    generalize normIdx P (pairOne f) (pairOne_nonzero f) = i
    fin_cases i
    · simpa [pairOne] using
        (min_le_left (0 : ℤ) (P.ord f))
    · simpa [pairOne] using
        (min_le_right (0 : ℤ) (P.ord f))

/-- The exact minimal-field normalization, including the pole branch. -/
theorem tupleHeight_pairOne_eq_functionHeight {N : ℕ} (M : Model N) [IsCurveField M.K]
    (f : M.K) (x : QbarPoint M.K) :
    tupleHeight (pairOne f) x = functionHeight M f x := by
  letI : IsCurveField M.K := M.isCurveField
  by_cases hf : f ∈ x.P.1
  · rw [functionHeight_of_regular M f x hf]
    change tupleHeight ![1, f] x = _
    rw [tupleHeight_pair_one_of_mem x hf, PolarAbsolute.logHeight_one_eq_gen]
    rw [AbcAdaptation.Tripod.deg_eq_finrank]
    rfl
  · rw [functionHeight_of_pole M f x hf]
    exact tupleHeight_pair_one_of_notMem x hf

/-- Local pole convention agrees even for the zero rational function. -/
theorem minOrd_pairOne_eq_neg_pole {N : ℕ} (M : Model N) [IsCurveField M.K]
    (hDVR : PlacesDiscrete M) (P : Place M.K) (f : M.K) :
    minOrd P (pairOne f) = -poleMultiplicity M hDVR f P := by
  letI : IsCurveField M.K := M.isCurveField
  rw [minOrd_pairOne, poleMultiplicity, ord_eq_placeOrd]
  omega

end PolarTuple

open PolarTuple

/-- Exact reusable checkpoint: the sole analytic/geometric input here is
source Integrality:493 for these canonical tuple heights. Its quantifiers cover
all finite tuple indices, all proper places, and all full algebraic points. -/
def PolarTupleHeightMonotonicity : Prop :=
  ∀ {K : Type} [Field K] [CharZero K] [IsCurveField K]
    {ι κ : Type} [Fintype ι] [Fintype κ]
    (s : ι → K) (t : κ → K)
    (hs : ∃ i, s i ≠ 0) (ht : ∃ j, t j ≠ 0)
    (hle : ∀ P : Place K, minOrd P t ≤ minOrd P s),
    ∃ C : ℝ, ∀ x : QbarPoint K, tupleHeight s x ≤ tupleHeight t x + C

/-- Complete exact parent composer. Two monotonicity constants supply one
uniform C=max C₁ C₂; no constant depends on x or its field degree. -/
theorem polarPresentationHeightSum_of_tupleMonotonicity
    (hMono : PolarTupleHeightMonotonicity) {N : ℕ}
    (M : Model N) (hDVR : PlacesDiscrete M) (hRF : ResiduesFinite M)
    (D E : Divisor M) (RD : PolarPresentation M hDVR D)
    (RE : PolarPresentation M hDVR E) (f r : M.K) (hr : r ≠ 0)
    (hrel : ∀ P : Place M.K,
      D P + E P = poleMultiplicity M hDVR f P + ord M hDVR P r) :
    ∃ C : ℝ, ∀ x : QbarPoint M.K,
      |divHeight RD x + divHeight RE x - functionHeight M f x| ≤ C := by
  letI : IsCurveField M.K := M.isCurveField
  let s : Fin 2 × Fin 2 → M.K := fun p => pairOne RD.f p.1 * pairOne RE.f p.2
  let d : Fin 2 × Fin 2 → M.K := fun p => pairOne RD.g p.1 * pairOne RE.g p.2
  let t₀ : Fin 2 × (Fin 2 × Fin 2) → M.K := fun p => pairOne f p.1 * d p.2
  -- The inverse is forced by D+E=polar(f)+div(r), since A_s=-minOrd(s).
  let t : Fin 2 × (Fin 2 × Fin 2) → M.K := fun p => r⁻¹ * t₀ p
  have hs : ∃ i, s i ≠ 0 := ⟨(0, 0), by simp [s, pairOne]⟩
  have hd : ∃ i, d i ≠ 0 := ⟨(0, 0), by simp [d, pairOne]⟩
  have ht₀ : ∃ i, t₀ i ≠ 0 := ⟨(0, (0, 0)), by simp [t₀, d, pairOne]⟩
  have ht : ∃ i, t i ≠ 0 :=
    ⟨(0, (0, 0)), by simpa [t, t₀, d, pairOne] using inv_ne_zero hr⟩
  have heq : ∀ P : Place M.K, minOrd P s = minOrd P t := by
    intro P
    change minOrd P (fun p : Fin 2 × Fin 2 => pairOne RD.f p.1 * pairOne RE.f p.2) =
      minOrd P (fun p => r⁻¹ * t₀ p)
    rw [minOrd_mul (pairOne_nonzero RD.f) (pairOne_nonzero RE.f),
      minOrd_smul ht₀ (inv_ne_zero hr)]
    change _ = P.ord r⁻¹ + minOrd P (fun p : Fin 2 × (Fin 2 × Fin 2) => pairOne f p.1 * d p.2)
    rw [minOrd_mul (pairOne_nonzero f) hd]
    change _ = P.ord r⁻¹ + (minOrd P (pairOne f) +
      minOrd P (fun p : Fin 2 × Fin 2 => pairOne RD.g p.1 * pairOne RE.g p.2))
    rw [minOrd_mul (pairOne_nonzero RD.g) (pairOne_nonzero RE.g), Place.ord_inv]
    simp only [minOrd_pairOne_eq_neg_pole M hDVR P]
    have hc := hrel P
    rw [RD.divisor_eq P, RE.divisor_eq P, ord_eq_placeOrd] at hc
    linarith
  obtain ⟨C₁, hC₁⟩ := hMono s t hs ht fun P => (heq P).ge
  obtain ⟨C₂, hC₂⟩ := hMono t s ht hs fun P => (heq P).le
  refine ⟨max C₁ C₂, fun x => ?_⟩
  have hhs : tupleHeight s x = functionHeight M RD.f x + functionHeight M RE.f x := by
    change tupleHeight (fun p : Fin 2 × Fin 2 => pairOne RD.f p.1 * pairOne RE.f p.2) x = _
    rw [tupleHeight_mul (pairOne_nonzero RD.f) (pairOne_nonzero RE.f),
      tupleHeight_pairOne_eq_functionHeight M, tupleHeight_pairOne_eq_functionHeight M]
  have hhd : tupleHeight d x = functionHeight M RD.g x + functionHeight M RE.g x := by
    change tupleHeight (fun p : Fin 2 × Fin 2 => pairOne RD.g p.1 * pairOne RE.g p.2) x = _
    rw [tupleHeight_mul (pairOne_nonzero RD.g) (pairOne_nonzero RE.g),
      tupleHeight_pairOne_eq_functionHeight M, tupleHeight_pairOne_eq_functionHeight M]
  have hht : tupleHeight t x = functionHeight M f x +
      (functionHeight M RD.g x + functionHeight M RE.g x) := by
    change tupleHeight (fun p => r⁻¹ * t₀ p) x = _
    rw [tupleHeight_smul x (inv_ne_zero hr)]
    change tupleHeight (fun p : Fin 2 × (Fin 2 × Fin 2) => pairOne f p.1 * d p.2) x = _
    rw [tupleHeight_mul (pairOne_nonzero f) hd,
      tupleHeight_pairOne_eq_functionHeight M, hhd]
  have hb₁ := hC₁ x
  have hb₂ := hC₂ x
  rw [hhs, hht] at hb₁ hb₂
  dsimp only [divHeight]
  apply abs_le.mpr
  constructor
  · linarith [le_max_right C₁ C₂]
  · linarith [le_max_left C₁ C₂]

end AbcAdaptation.Tripod.Fermat.Proper
