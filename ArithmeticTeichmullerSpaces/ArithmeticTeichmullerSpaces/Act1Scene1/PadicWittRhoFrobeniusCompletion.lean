import ArithmeticTeichmullerSpaces.Act1Scene1.PadicWittRhoFrobenius
import ArithmeticTeichmullerSpaces.Act1Scene1.PadicWittRhoCompletion
import Mathlib.Analysis.Normed.Module.Completion

/-!
source-id: JT-SCENE1-STANDARD-PADIC-WITT-RHO-FROBENIUS-COMPLETION
source: Joshi II `se:ff-rings` and `pr:teichmuller-lift-A/B`.
fidelity: transports standard p-only Frobenius between fixed-radius
completions, with the radius changed from rho to rho^p.
boundary: all-radius carrier assembly and the paper B identities remain open.
-/

namespace JoshiTeich.Act1Scene1.PadicWittRhoFrobeniusCompletion

open PadicBoundedWittLocalization
open scoped ENNReal Topology
noncomputable section
variable (p : ℕ) [Fact p.Prime]

abbrev Radius := PadicWittRhoCompletion.Radius
abbrev Source (ρ : Radius) := PadicWittRhoCompletion.Source p ρ
abbrev Completed (ρ : Radius) := PadicWittRhoCompletion.Completed p ρ

def poweredRadius (ρ : Radius) : Radius :=
  ⟨ρ.val ^ p, pos_iff_ne_zero.mpr (pow_ne_zero _ ρ.property.1.ne'),
    pow_lt_one₀ bot_le ρ.property.2 (Fact.out : p.Prime).ne_zero⟩

def sourceFrobeniusEquiv (ρ : Radius) : Source p ρ ≃+* Source p (poweredRadius p ρ) :=
  (PadicWittRhoCompletion.sourceEquiv p ρ).symm.trans
    ((PadicWittRhoFrobenius.frobeniusEquiv p).trans
      (PadicWittRhoCompletion.sourceEquiv p (poweredRadius p ρ)))

theorem sourceFrobeniusEquiv_apply (ρ : Radius) (x : Source p ρ) :
    sourceFrobeniusEquiv p ρ x =
      PadicWittRhoCompletion.sourceEquiv p (poweredRadius p ρ)
        (PadicWittRhoFrobenius.frobeniusEquiv p
          ((PadicWittRhoCompletion.sourceEquiv p ρ).symm x)) := rfl

def sourceHom (ρ : Radius) : Source p ρ →+* Source p (poweredRadius p ρ) :=
  (sourceFrobeniusEquiv p ρ).toRingHom

theorem sourceHom_norm (ρ : Radius) (x : Source p ρ) :
    ‖sourceHom p ρ x‖ = ‖x‖ ^ p := by
  change ‖sourceFrobeniusEquiv p ρ x‖ = ‖x‖ ^ p
  rw [sourceFrobeniusEquiv_apply, PadicWittRhoCompletion.source_norm]
  calc
    PadicWittRhoNorm.realValue p (poweredRadius p ρ).val
        (PadicWittRhoFrobenius.frobeniusEquiv p
          ((PadicWittRhoCompletion.sourceEquiv p ρ).symm x)) =
        PadicWittRhoNorm.realValue p ρ.val
          ((PadicWittRhoCompletion.sourceEquiv p ρ).symm x) ^ p :=
      PadicWittRhoFrobenius.realValue_frobenius p ρ
        ((PadicWittRhoCompletion.sourceEquiv p ρ).symm x)
    _ = ‖x‖ ^ p := by
      have hn : PadicWittRhoNorm.realValue p ρ.val
          ((PadicWittRhoCompletion.sourceEquiv p ρ).symm x) = ‖x‖ := by
        calc
          _ = ‖PadicWittRhoCompletion.sourceEquiv p ρ
              ((PadicWittRhoCompletion.sourceEquiv p ρ).symm x)‖ :=
            (PadicWittRhoCompletion.source_norm p ρ _).symm
          _ = ‖x‖ := congrArg norm (RingEquiv.apply_symm_apply
            (PadicWittRhoCompletion.sourceEquiv p ρ) x)
      rw [hn]

private theorem sourceHom_dist (ρ : Radius) (x y : Source p ρ) :
    dist (sourceHom p ρ x) (sourceHom p ρ y) = dist x y ^ p := by
  rw [dist_eq_norm, ← map_sub, sourceHom_norm, dist_eq_norm]

private theorem sourceFrobeniusEquiv_symm_dist (ρ : Radius)
    (x y : Source p (poweredRadius p ρ)) :
    dist ((sourceFrobeniusEquiv p ρ).symm x) ((sourceFrobeniusEquiv p ρ).symm y) ^ p =
      dist x y := by
  have h := sourceHom_dist p ρ ((sourceFrobeniusEquiv p ρ).symm x)
    ((sourceFrobeniusEquiv p ρ).symm y)
  have hx : sourceHom p ρ ((sourceFrobeniusEquiv p ρ).symm x) = x := by
    change sourceFrobeniusEquiv p ρ ((sourceFrobeniusEquiv p ρ).symm x) = x
    exact RingEquiv.apply_symm_apply _ _
  have hy : sourceHom p ρ ((sourceFrobeniusEquiv p ρ).symm y) = y := by
    change sourceFrobeniusEquiv p ρ ((sourceFrobeniusEquiv p ρ).symm y) = y
    exact RingEquiv.apply_symm_apply _ _
  rw [hx, hy] at h
  exact h.symm

theorem sourceHom_uniformContinuous (ρ : Radius) : UniformContinuous (sourceHom p ρ) := by
  apply Metric.uniformContinuous_iff.mpr
  intro ε hε
  refine ⟨min ε 1, lt_min hε zero_lt_one, ?_⟩
  intro x y hxy
  rw [sourceHom_dist]
  have hp : dist x y ^ p ≤ dist x y := by
    obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (Fact.out : p.Prime).ne_zero
    have hpow : dist x y ^ p = dist x y ^ n * dist x y := by
      calc
        dist x y ^ p = dist x y ^ n.succ :=
          congrArg (fun k : ℕ => dist x y ^ k) hn
        _ = dist x y ^ n * dist x y := pow_succ (dist x y) n
    rw [hpow]
    exact mul_le_of_le_one_left dist_nonneg
      (pow_le_one₀ dist_nonneg (lt_of_lt_of_le hxy (min_le_right _ _)).le)
  exact hp.trans_lt (lt_of_lt_of_le hxy (min_le_left _ _))

theorem sourceHom_continuous (ρ : Radius) : Continuous (sourceHom p ρ) :=
  (sourceHom_uniformContinuous p ρ).continuous

private theorem sourceFrobeniusEquiv_symm_continuous (ρ : Radius) :
    Continuous (sourceFrobeniusEquiv p ρ).symm := by
  have huc : UniformContinuous (sourceFrobeniusEquiv p ρ).symm := by
    apply Metric.uniformContinuous_iff.mpr
    intro ε hε
    refine ⟨ε ^ p, pow_pos hε _, ?_⟩
    intro x y hxy
    apply lt_of_pow_lt_pow_left₀ p hε.le
    rw [sourceFrobeniusEquiv_symm_dist p ρ x y]
    exact hxy
  exact huc.continuous

def completedHom (ρ : Radius) : Completed p ρ →+* Completed p (poweredRadius p ρ) :=
  UniformSpace.Completion.mapRingHom (sourceHom p ρ) (sourceHom_continuous p ρ)

theorem completedHom_inclusion (ρ : Radius) (x : Ring p) :
    completedHom p ρ (PadicWittRhoCompletion.inclusion p ρ x) =
      PadicWittRhoCompletion.inclusion p (poweredRadius p ρ)
        (PadicWittRhoFrobenius.frobeniusEquiv p x) := by
  exact UniformSpace.Completion.mapRingHom_coe _ (PadicWittRhoCompletion.sourceEquiv p ρ x)

theorem completedHom_norm (ρ : Radius) (x : Completed p ρ) :
    ‖completedHom p ρ x‖ = ‖x‖ ^ p := by
  refine UniformSpace.Completion.induction_on x
    (isClosed_eq (continuous_norm.comp (UniformSpace.Completion.continuous_map))
      (continuous_norm.pow p)) ?_
  intro a
  let y := (PadicWittRhoCompletion.sourceEquiv p ρ).symm a
  change ‖completedHom p ρ (PadicWittRhoCompletion.inclusion p ρ y)‖ =
    ‖PadicWittRhoCompletion.inclusion p ρ y‖ ^ p
  rw [completedHom_inclusion, PadicWittRhoCompletion.inclusion_norm,
    PadicWittRhoCompletion.inclusion_norm]
  exact PadicWittRhoFrobenius.realValue_frobenius p ρ y

def completedEquiv (ρ : Radius) : Completed p ρ ≃+* Completed p (poweredRadius p ρ) :=
  UniformSpace.Completion.mapRingEquiv (sourceFrobeniusEquiv p ρ)
    (sourceHom_continuous p ρ)
    (sourceFrobeniusEquiv_symm_continuous p ρ)

theorem completedEquiv_apply (ρ : Radius) (x : Completed p ρ) :
    completedEquiv p ρ x = completedHom p ρ x := rfl

theorem completedHom_injective (ρ : Radius) : Function.Injective (completedHom p ρ) := by
  intro x y hxy
  apply (completedEquiv p ρ).injective
  simpa only [completedEquiv_apply] using hxy

theorem completedEquiv_inclusion (ρ : Radius) (x : Ring p) :
    completedEquiv p ρ (PadicWittRhoCompletion.inclusion p ρ x) =
      PadicWittRhoCompletion.inclusion p (poweredRadius p ρ)
        (PadicWittRhoFrobenius.frobeniusEquiv p x) :=
  completedHom_inclusion p ρ x

theorem completedEquiv_inverse_inclusion (ρ : Radius) (x : Ring p) :
    (completedEquiv p ρ).symm (PadicWittRhoCompletion.inclusion p (poweredRadius p ρ) x) =
      PadicWittRhoCompletion.inclusion p ρ ((PadicWittRhoFrobenius.frobeniusEquiv p).symm x) := by
  apply (completedEquiv p ρ).injective
  rw [RingEquiv.apply_symm_apply, completedEquiv_inclusion,
    RingEquiv.apply_symm_apply]

theorem completedEquiv_norm (ρ : Radius) (x : Completed p ρ) :
    ‖completedEquiv p ρ x‖ = ‖x‖ ^ p := by
  rw [completedEquiv_apply]
  exact completedHom_norm p ρ x

theorem completedEquiv_inverse_norm (ρ : Radius)
    (x : Completed p (poweredRadius p ρ)) :
    ‖(completedEquiv p ρ).symm x‖ ^ p = ‖x‖ := by
  rw [← completedEquiv_norm p ρ ((completedEquiv p ρ).symm x)]
  simp

theorem completedEquiv_continuous (ρ : Radius) :
    Continuous (completedEquiv p ρ) := UniformSpace.Completion.continuous_map

theorem completedEquiv_symm_continuous (ρ : Radius) :
    Continuous (completedEquiv p ρ).symm := UniformSpace.Completion.continuous_map

def completedHomeomorph (ρ : Radius) :
    Completed p ρ ≃ₜ Completed p (poweredRadius p ρ) where
  toEquiv := (completedEquiv p ρ).toEquiv
  continuous_toFun := completedEquiv_continuous p ρ
  continuous_invFun := completedEquiv_symm_continuous p ρ

end
end JoshiTeich.Act1Scene1.PadicWittRhoFrobeniusCompletion
