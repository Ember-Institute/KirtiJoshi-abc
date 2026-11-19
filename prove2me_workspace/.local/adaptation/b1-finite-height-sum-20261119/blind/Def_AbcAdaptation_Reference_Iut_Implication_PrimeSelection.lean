structure LocalHeightData : Type (w + 1) where

  ι : Type w

  bad : Finset ι

  p : ι → ℕ

  hv : ι → ℕ

  f : ι → ℕ

  deg : ℕ

  one_le_deg : 1 ≤ deg

  p_prime : ∀ v ∈ bad, (p v).Prime

  one_le_hv : ∀ v ∈ bad, 1 ≤ hv v

  one_le_f : ∀ v ∈ bad, 1 ≤ f v

  sum_f_le : ∀ q : ℕ, ∑ v ∈ bad.filter (fun v => p v = q), f v ≤ deg

namespace LocalHeightData

variable (L : LocalHeightData)

noncomputable def height : ℝ :=
  (∑ v ∈ L.bad, (L.hv v : ℝ) * L.f v * Real.log (L.p v)) / L.deg
