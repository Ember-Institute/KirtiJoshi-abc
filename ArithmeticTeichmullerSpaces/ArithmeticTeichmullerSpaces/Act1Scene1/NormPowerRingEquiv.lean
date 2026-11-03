import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.Topology.Algebra.UniformRing

/-!
source-id: JT-SCENE1-NORM-POWER-RING-EQUIV
source: Joshi II `se:ff-rings`, radius changes for the original rho norms;
Mathlib's completion of normed rings.
fidelity: a positive integer norm power law gives uniform continuity in
both directions of the original ring equivalence. The induced completion
equivalence preserves the same norm power law. No norm is replaced.
Original proofs; no reference implementation copied.
boundary: generic mathematics; no period-ring identity is asserted.
-/

namespace JoshiTeich.Act1Scene1.NormPowerRingEquiv

open scoped Topology
noncomputable section

variable {A B : Type*} [NormedCommRing A] [NormedCommRing B]

private theorem dist_pow (e : A ≃+* B) (d : ℕ)
    (hNormPower : ∀ x : A, ‖e x‖ ^ d = ‖x‖) (x y : A) :
    dist (e x) (e y) ^ d = dist x y := by
  rw [dist_eq_norm, ← map_sub, hNormPower, dist_eq_norm]

private theorem symm_dist (e : A ≃+* B) (d : ℕ)
    (hNormPower : ∀ x : A, ‖e x‖ ^ d = ‖x‖) (x y : B) :
    dist (e.symm x) (e.symm y) = dist x y ^ d := by
  simpa only [RingEquiv.apply_symm_apply] using
    (dist_pow e d hNormPower (e.symm x) (e.symm y)).symm

theorem uniformContinuous (e : A ≃+* B) (d : ℕ)
    (hNormPower : ∀ x : A, ‖e x‖ ^ d = ‖x‖) : UniformContinuous e := by
  apply Metric.uniformContinuous_iff.mpr
  intro ε hε
  refine ⟨ε ^ d, pow_pos hε _, ?_⟩
  intro x y hxy
  exact lt_of_pow_lt_pow_left₀ d hε.le (by
    rwa [dist_pow e d hNormPower])

theorem symm_uniformContinuous (e : A ≃+* B) (d : ℕ) (hd : 0 < d)
    (hNormPower : ∀ x : A, ‖e x‖ ^ d = ‖x‖) : UniformContinuous e.symm := by
  apply Metric.uniformContinuous_iff.mpr
  intro ε hε
  refine ⟨min ε 1, lt_min hε zero_lt_one, ?_⟩
  intro x y hxy
  rw [symm_dist e d hNormPower]
  exact (pow_le_of_le_one dist_nonneg
    (lt_of_lt_of_le hxy (min_le_right _ _)).le hd.ne').trans_lt
      (lt_of_lt_of_le hxy (min_le_left _ _))

def completedRingEquiv (e : A ≃+* B) (d : ℕ) (hd : 0 < d)
    (hNormPower : ∀ x : A, ‖e x‖ ^ d = ‖x‖) :
    UniformSpace.Completion A ≃+* UniformSpace.Completion B :=
  UniformSpace.Completion.mapRingEquiv e
    (uniformContinuous e d hNormPower).continuous
    (symm_uniformContinuous e d hd hNormPower).continuous

theorem completedRingEquiv_continuous (e : A ≃+* B) (d : ℕ) (hd : 0 < d)
    (hNormPower : ∀ x : A, ‖e x‖ ^ d = ‖x‖) :
    Continuous (completedRingEquiv e d hd hNormPower) := by
  change Continuous (UniformSpace.Completion.map (e : A → B))
  exact UniformSpace.Completion.continuous_map

theorem completedRingEquiv_symm_continuous (e : A ≃+* B) (d : ℕ) (hd : 0 < d)
    (hNormPower : ∀ x : A, ‖e x‖ ^ d = ‖x‖) :
    Continuous (completedRingEquiv e d hd hNormPower).symm := by
  change Continuous (UniformSpace.Completion.map (e.symm : B → A))
  exact UniformSpace.Completion.continuous_map

theorem completedRingEquiv_coe (e : A ≃+* B) (d : ℕ) (hd : 0 < d)
    (hNormPower : ∀ x : A, ‖e x‖ ^ d = ‖x‖) (x : A) :
    completedRingEquiv e d hd hNormPower (x : UniformSpace.Completion A) =
      (e x : UniformSpace.Completion B) := by
  change UniformSpace.Completion.map (e : A → B) (x : UniformSpace.Completion A) = _
  exact UniformSpace.Completion.map_coe (uniformContinuous e d hNormPower) x

theorem completedRingEquiv_norm_pow (e : A ≃+* B) (d : ℕ) (hd : 0 < d)
    (hNormPower : ∀ x : A, ‖e x‖ ^ d = ‖x‖)
    (x : UniformSpace.Completion A) :
    ‖completedRingEquiv e d hd hNormPower x‖ ^ d = ‖x‖ := by
  refine UniformSpace.Completion.induction_on x
    (isClosed_eq ((completedRingEquiv_continuous e d hd hNormPower).norm.pow d)
      continuous_norm) ?_
  intro a
  rw [completedRingEquiv_coe, UniformSpace.Completion.norm_coe,
    UniformSpace.Completion.norm_coe]
  exact hNormPower a

def completedHomeomorph (e : A ≃+* B) (d : ℕ) (hd : 0 < d)
    (hNormPower : ∀ x : A, ‖e x‖ ^ d = ‖x‖) :
    UniformSpace.Completion A ≃ₜ UniformSpace.Completion B where
  toEquiv := (completedRingEquiv e d hd hNormPower).toEquiv
  continuous_toFun := completedRingEquiv_continuous e d hd hNormPower
  continuous_invFun := completedRingEquiv_symm_continuous e d hd hNormPower

end
end JoshiTeich.Act1Scene1.NormPowerRingEquiv
