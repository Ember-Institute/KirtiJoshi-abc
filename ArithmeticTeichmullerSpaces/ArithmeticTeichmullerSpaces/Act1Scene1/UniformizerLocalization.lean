import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.FractionRing

/-!
source-id: JT-SCENE1-UNIFORMIZER-LOCALIZATION
source: Mathlib localization of associated elements and fraction rings;
the de Rham period field in Joshi II (1069--1076).
fidelity: inverting any generating set of associates of π is equivalent to
inverting π; unit-times-π-power factorizations identify that localization
with the fraction ring of the original domain. Original proofs, no copied
reference-engine code or new Prologue/Core assumptions.
-/

namespace JoshiTeich.Act1Scene1.UniformizerLocalization

variable {R : Type*} [CommRing R]

theorem generators_localization (π : R) (s : Set R) (hπ : π ∈ s)
    (hassoc : ∀ a ∈ s, Associated a π) :
    IsLocalization (Submonoid.closure s) (Localization.Away π) := by
  apply IsLocalization.of_le (Submonoid.powers π) (Submonoid.closure s)
    (Submonoid.powers_le.mpr (Submonoid.subset_closure hπ))
  have hle : Submonoid.closure s ≤ (IsUnit.submonoid (Localization.Away π)).comap
      (algebraMap R (Localization.Away π)).toMonoidHom := by
    apply Submonoid.closure_le.mpr
    intro a ha
    exact ((hassoc a ha).map (algebraMap R (Localization.Away π))).isUnit_iff.mpr
      (IsLocalization.Away.algebraMap_isUnit π)
  exact fun a ha => hle ha

theorem fractionRing [IsDomain R] (π : R) (S : Type*) [CommRing S] [Algebra R S]
    [IsLocalization.Away π S] (hπ : π ≠ 0)
    (hfactor : ∀ x : R, x ≠ 0 → ∃ n : ℕ, ∃ u : Rˣ, x = π ^ n * u) :
    IsFractionRing R S := by
  apply IsLocalization.of_le (Submonoid.powers π) (nonZeroDivisors R)
  · rintro a ⟨n, rfl⟩
    exact mem_nonZeroDivisors_iff_ne_zero.mpr (pow_ne_zero n hπ)
  · intro a ha
    obtain ⟨n, u, hu⟩ := hfactor a (nonZeroDivisors.ne_zero ha)
    rw [hu, map_mul, map_pow]
    exact ((IsLocalization.Away.algebraMap_isUnit π).pow n).mul
      (u.isUnit.map (algebraMap R S))

end JoshiTeich.Act1Scene1.UniformizerLocalization
