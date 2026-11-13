/-
Copyright (c) 2026 The genl contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The genl contributors

Independent specialization of Genl/Curves/Covering.lean and
Genl/Curves/BelyiDescent.lean at Genl ea2846c877d1e16d8f0b911a5fed07f5ee69eaaf.
Only concrete algebraic points and Mathlib number-field heights occur below.
-/
import Definitions.Def_AbcTripod
import Mathlib.Data.Fin.VecNotation

set_option autoImplicit false

open NumberField
open scoped IntermediateField

namespace AbcAdaptation.Tripod.Fermat

/-- The affine open of the actual Fermat curve U^N + V^N = W^N, W = 1,
with the two cusp coordinates nonzero. No arbitrary curve carrier is supplied. -/
def Pt (N : ℕ) : Type :=
  {p : Qbar × Qbar // p.1 ^ N + p.2 ^ N = 1 ∧ p.1 ≠ 0 ∧ p.2 ≠ 0}

noncomputable abbrev fieldOf {N : ℕ} (p : Pt N) : IntermediateField ℚ Qbar :=
  ℚ⟮p.1.1, p.1.2⟯

instance {N : ℕ} (p : Pt N) : FiniteDimensional ℚ (fieldOf p) :=
  IntermediateField.finiteDimensional_adjoin_pair (isIntegral p.1.1) (isIntegral p.1.2)

noncomputable def degree {N : ℕ} (p : Pt N) : ℕ := Module.finrank ℚ (fieldOf p)

noncomputable def u {N : ℕ} (p : Pt N) : fieldOf p :=
  ⟨p.1.1, IntermediateField.subset_adjoin ℚ _ (by simp)⟩

noncomputable def v {N : ℕ} (p : Pt N) : fieldOf p :=
  ⟨p.1.2, IntermediateField.subset_adjoin ℚ _ (by simp)⟩

/-- The morphism on the open parts is (u,v) ↦ u^N. -/
noncomputable def toTripod {N : ℕ} (p : Pt N) : AbcAdaptation.Tripod.Pt :=
  ⟨p.1.1 ^ N, pow_ne_zero _ p.2.2.1, by
    intro h
    have hv : p.1.2 ^ N = 0 := by
      have := p.2.1
      rw [h] at this
      exact add_eq_left.mp this
    exact (pow_ne_zero _ p.2.2.2) hv⟩

/-- The actual extension used for both the normalized height comparison and
the Kummer discriminant bound. No independent field is supplied. -/
theorem fieldOf_toTripod_le {N : ℕ} (p : Pt N) :
    AbcAdaptation.Tripod.fieldOf (toTripod p).1 ≤ fieldOf p := by
  apply IntermediateField.adjoin_simple_le_iff.mpr
  change p.1.1 ^ N ∈ fieldOf p
  exact pow_mem (IntermediateField.subset_adjoin ℚ _ (by simp)) N

/-- Normalized discriminant of the full point field ℚ(u,v), not of ℚ(u^N). -/
noncomputable def logDiff {N : ℕ} (p : Pt N) : ℝ :=
  Real.log |(NumberField.discr (fieldOf p) : ℝ)| / degree p

/-- The normalized projective height of the actual point [u:v:1]. -/
noncomputable def projectiveHeight {N : ℕ} (p : Pt N) : ℝ :=
  Height.logHeight ![u p, v p, 1] / degree p

/-- The explicit representative associated with O_F(N-3).
Identifying this with a canonical-divisor height uses adjunction for the smooth
degree-N plane Fermat curve; that geometric step belongs to CanonicalEstimate. -/
noncomputable def canonicalHeight {N : ℕ} (p : Pt N) : ℝ :=
  ((N : ℝ) - 3) * projectiveHeight p

noncomputable def coefficient (N : ℕ) : ℝ := ((N : ℝ) - 3) / N

/-- Explicit field/height normalization bridge. This includes the height tower
normalization ℚ(u^N) ⊆ ℚ(u,v), the N-th power height formula, and the comparison
of [u:v:1] with [u:1] on U^N+V^N=1. It is not a definitional identity. -/
def HeightNormalization : Prop :=
  ∀ N : ℕ, 3 < N → ∃ C : ℝ, ∀ p : Pt N,
    |canonicalHeight p - coefficient N * htCan (toTripod p)| ≤ C

/-- Real Kummer-cover lift and arithmetic comparison. The existence includes
the extension ℚ(z) ⊆ ℚ(u,v), u^N=z, v^N=1-z, and the sharp N² degree bound.
The discriminant estimate is for the full extension, uniformly in z. -/
def LiftDifferent : Prop :=
  ∀ N : ℕ, 0 < N → ∃ C : ℝ, ∀ z : AbcAdaptation.Tripod.Pt,
    ∃ p : Pt N, toTripod p = z ∧
      degree p ≤ N ^ 2 * deg z.1 ∧
      logDiff p ≤ AbcAdaptation.Tripod.logDiff z + logCond z + C

/-- The divisor-free estimate for the actual proper Fermat curves of degree N>3.
This child owns the noncritical Belyi, local compactness, height/conductor,
and canonical-adjunction arguments; it remains an OPEN mathematical child.
The statement has no freely chosen height, curve, or Belyi theory parameter. -/
def CanonicalEstimate : Prop :=
  StatementII → ∀ N : ℕ, 3 < N → ∀ (d : ℕ) (ε : ℝ), 0 < ε →
    ∃ C : ℝ, ∀ p : Pt N, degree p ≤ d →
      canonicalHeight p ≤ (1 + ε) * logDiff p + C

end AbcAdaptation.Tripod.Fermat
