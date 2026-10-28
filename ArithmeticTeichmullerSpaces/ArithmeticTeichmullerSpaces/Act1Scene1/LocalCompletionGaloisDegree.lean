import ArithmeticTeichmullerSpaces.Act1Scene1.LocalCompletionRelativeDegree
import Mathlib.FieldTheory.Galois.IsGaloisGroup
import Mathlib.NumberTheory.RamificationInertia.Galois

/-!
source-id: JT-SCENE1-LOCAL-COMPLETION-GALOIS-DEGREE
source: Mathlib Galois transitivity on primes, invariance of ramification and
inertia under ideal conjugacy, and the actual relative-completion degree law;
Joshi III `eq:weights` requires these degrees on chosen over-places.
fidelity: proves equality of absolute ramification, residue and local degrees
over one base place in a Galois number-field extension, and equality of the
actual relative completion dimensions. No equality across base places is input.
boundary: Scene1/Derived. Original proofs; no reference code copied.
-/

namespace JoshiTeich.Act1Scene1.LocalCompletion

open NumberField JoshiTeich.Prologue.Arithmetic
open scoped Pointwise
universe u
noncomputable section
variable {K L : Type u} [Field K] [NumberField K] [Field L] [NumberField L]
variable [Algebra K L] [IsGalois K L]
variable {w : FinitePlace K} {v z : FinitePlace L}
variable (hv : Ideal.LiesOver v.maximalIdeal.asIdeal w.maximalIdeal.asIdeal)
variable (hz : Ideal.LiesOver z.maximalIdeal.asIdeal w.maximalIdeal.asIdeal)

include hv hz

private theorem ideals_conjugate_of_galois_liesOver :
    ∃ σ : L ≃ₐ[K] L, σ • v.maximalIdeal.asIdeal = z.maximalIdeal.asIdeal := by
  let : FiniteDimensional K L := Module.Finite.of_restrictScalars_finite ℚ K L
  let : Ideal.LiesOver v.maximalIdeal.asIdeal w.maximalIdeal.asIdeal := hv
  let : Ideal.LiesOver z.maximalIdeal.asIdeal w.maximalIdeal.asIdeal := hz
  let : IsGaloisGroup (L ≃ₐ[K] L) (𝓞 K) (𝓞 L) :=
    IsGaloisGroup.of_isFractionRing (L ≃ₐ[K] L) (𝓞 K) (𝓞 L) K L
  exact Ideal.exists_smul_eq_of_isGaloisGroup w.maximalIdeal.asIdeal
    v.maximalIdeal.asIdeal z.maximalIdeal.asIdeal (L ≃ₐ[K] L)

theorem ramIdx_eq_of_galois_liesOver : ramIdx v = ramIdx z := by
  obtain ⟨σ, hσ⟩ := ideals_conjugate_of_galois_liesOver hv hz
  unfold ramIdx
  rw [← hσ, Ideal.ramificationIdx_smul]

theorem inertDeg_eq_of_galois_liesOver : inertDeg v = inertDeg z := by
  obtain ⟨σ, hσ⟩ := ideals_conjugate_of_galois_liesOver hv hz
  unfold inertDeg
  rw [← hσ, Ideal.inertiaDeg_smul]

theorem localDeg_eq_of_galois_liesOver : localDeg v = localDeg z := by
  unfold localDeg
  rw [ramIdx_eq_of_galois_liesOver hv hz, inertDeg_eq_of_galois_liesOver hv hz]

theorem relativeFinrank_eq_of_galois_liesOver :
    letI := relativeAlgebra hv
    letI := relativeAlgebra hz
    Module.finrank (completionAt K w) (completionAt L v) =
      Module.finrank (completionAt K w) (completionAt L z) := by
  let := relativeAlgebra hv
  let := relativeAlgebra hz
  apply Nat.eq_of_mul_eq_mul_left (localDeg_pos w)
  rw [finrank_relativeAlgebra_eq_ramification_inertia hv,
    finrank_relativeAlgebra_eq_ramification_inertia hz,
    ← localDeg_eq_mul hv, ← localDeg_eq_mul hz]
  exact localDeg_eq_of_galois_liesOver hv hz

end
end JoshiTeich.Act1Scene1.LocalCompletion
