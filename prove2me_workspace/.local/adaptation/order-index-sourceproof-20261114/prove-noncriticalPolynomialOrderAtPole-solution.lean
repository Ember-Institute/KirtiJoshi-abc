import Definitions.Def_FermatNoncriticalElementarySource
import Definitions.Def_FermatNoncriticalOrderSource
import Mathlib.Algebra.Polynomial.Reverse

set_option autoImplicit false
open AbcAdaptation
open Polynomial
open AbcAdaptation.Tripod.Fermat.Proper

theorem solution {N : ℕ} (M : Model N)
    (hDVR : PlacesDiscrete M) (ψ : M.K) (hψ : Transcendental ℚ ψ)
    (P : Place M.K) (h : ψ ∉ P.1) {p : ℚ[X]} (hp : p ≠ 0) :
    letI : IsCurveField M.K := M.isCurveField
    P.ord (aeval ψ p) = p.natDegree * P.ord ψ := by
  letI : IsCurveField M.K := M.isCurveField
  have hψ0 : ψ ≠ 0 := ne_zero_of_transcendental hψ
  letI : Invertible ψ := invertibleOfNonzero hψ0
  have key : aeval ψ⁻¹ p.reverse * ψ ^ p.natDegree = aeval ψ p := by
    have := eval₂_reverse_mul_pow (algebraMap ℚ M.K) ψ p
    rwa [invOf_eq_inv] at this
  have hneg := (P.ord_neg_iff).mpr h
  have hpos : 0 < P.ord ψ⁻¹ := by rw [P.ord_inv]; omega
  have hinv : ψ⁻¹ ∈ P.1 := P.mem_of_ord_nonneg hpos.le
  have hres : P.residue ⟨aeval ψ⁻¹ p.reverse, P.noncritical_aeval_mem hinv _⟩ ≠ 0 := by
    rw [P.noncritical_residue_aeval hinv, P.noncritical_residue_eq_zero_of_ord_pos hpos, ← coeff_zero_eq_aeval_zero',
      coeff_zero_reverse]
    exact (map_ne_zero_iff _ (algebraMap ℚ _).injective).mpr (leadingCoeff_ne_zero.mpr hp)
  have h0 : aeval ψ⁻¹ p.reverse ≠ 0 := by
    rintro h0
    apply hres
    rw [show (⟨aeval ψ⁻¹ p.reverse, P.noncritical_aeval_mem hinv _⟩ : P.1) = 0 from Subtype.ext h0,
      map_zero]
  rw [← key, P.ord_mul h0 (pow_ne_zero _ hψ0), P.noncritical_ord_eq_zero_of_residue_ne_zero _ hres,
    P.ord_pow, zero_add]
