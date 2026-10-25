import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittRhoFrobeniusCompletion

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITT-RHO-FROBENIUS-EQUIV
source: Joshi II `se:ff-rings`, invertible Frobenius on the rho-normed
period ring and its action on the radius family.
fidelity: proves continuity of the actual inverse Frobenius by the
exact norm-power identity. The original ring equivalence extends to a
ring equivalence of the rho and rho^p completions, continuous in both
directions. Both maps retain their original localization values.
Original proofs; no reference implementation copied.
boundary: Scene1/Derived; all-radius automorphism, scalar algebra,
Tate-log eigenspace and paper B/BK identities remain separate obligations.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittRhoFrobeniusEquiv

open JoshiTeich.Prologue
open InitialThetaWittRhoCompletion InitialThetaWittRhoFrobeniusCompletion
open scoped ENNReal Topology
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

def sourceFrobeniusEquiv (ρ : Radius) : Source D w ρ ≃+* Source D w (poweredRadius D w ρ) :=
  (sourceEquiv D w ρ).symm.trans
    ((InitialThetaBoundedWittLocalization.frobeniusEquiv D w).trans
      (sourceEquiv D w (poweredRadius D w ρ)))

theorem sourceFrobeniusEquiv_apply (ρ : Radius) (x : Source D w ρ) :
    sourceFrobeniusEquiv D w ρ x = sourceHom D w ρ x := rfl

theorem source_inverse_norm (ρ : Radius) (x : Source D w (poweredRadius D w ρ)) :
    ‖(sourceFrobeniusEquiv D w ρ).symm x‖ ^ Arithmetic.residueChar w.1 = ‖x‖ := by
  have h := sourceHom_norm D w ρ ((sourceFrobeniusEquiv D w ρ).symm x)
  rw [← sourceFrobeniusEquiv_apply, RingEquiv.apply_symm_apply] at h
  exact h.symm

theorem source_inverse_continuous (ρ : Radius) :
    Continuous (sourceFrobeniusEquiv D w ρ).symm := by
  apply continuous_iff_continuousAt.mpr
  intro a
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [eventually_norm_sub_lt a (pow_pos hε (Arithmetic.residueChar w.1))] with x hx
  have hlt : ‖(sourceFrobeniusEquiv D w ρ).symm x -
      (sourceFrobeniusEquiv D w ρ).symm a‖ < ε := by
    apply lt_of_pow_lt_pow_left₀ (Arithmetic.residueChar w.1) hε.le
    rwa [← map_sub, source_inverse_norm]
  simpa only [dist_zero_right, norm_norm] using hlt

def completedEquiv (ρ : Radius) : Completed D w ρ ≃+* Completed D w (poweredRadius D w ρ) :=
  UniformSpace.Completion.mapRingEquiv (sourceFrobeniusEquiv D w ρ)
    (sourceHom_continuous D w ρ) (source_inverse_continuous D w ρ)

theorem completedEquiv_apply (ρ : Radius) (x : Completed D w ρ) :
    completedEquiv D w ρ x = completedHom D w ρ x := rfl

theorem completedEquiv_continuous (ρ : Radius) : Continuous (completedEquiv D w ρ) :=
  completedHom_continuous D w ρ

theorem completedEquiv_symm_continuous (ρ : Radius) : Continuous (completedEquiv D w ρ).symm :=
  UniformSpace.Completion.continuous_map

theorem completedEquiv_inclusion (ρ : Radius) (x : InitialThetaBoundedWittLocalization.Ring D w) :
    completedEquiv D w ρ (inclusion D w ρ x) =
      inclusion D w (poweredRadius D w ρ) (InitialThetaBoundedWittLocalization.frobeniusEquiv D w x) :=
  completedHom_inclusion D w ρ x

theorem completedEquiv_symm_inclusion (ρ : Radius)
    (x : InitialThetaBoundedWittLocalization.Ring D w) :
    (completedEquiv D w ρ).symm (inclusion D w (poweredRadius D w ρ) x) =
      inclusion D w ρ ((InitialThetaBoundedWittLocalization.frobeniusEquiv D w).symm x) := by
  apply (completedEquiv D w ρ).injective
  rw [RingEquiv.apply_symm_apply, completedEquiv_inclusion, RingEquiv.apply_symm_apply]

theorem completedEquiv_symm_norm (ρ : Radius) (x : Completed D w (poweredRadius D w ρ)) :
    ‖(completedEquiv D w ρ).symm x‖ ^ Arithmetic.residueChar w.1 = ‖x‖ := by
  have h := completedHom_norm D w ρ ((completedEquiv D w ρ).symm x)
  rw [← completedEquiv_apply, RingEquiv.apply_symm_apply] at h
  exact h.symm

def completedHomeomorph (ρ : Radius) : Completed D w ρ ≃ₜ Completed D w (poweredRadius D w ρ) where
  toEquiv := (completedEquiv D w ρ).toEquiv
  continuous_toFun := completedEquiv_continuous D w ρ
  continuous_invFun := completedEquiv_symm_continuous D w ρ

end
end JoshiTeich.Act1Scene1.InitialThetaWittRhoFrobeniusEquiv
