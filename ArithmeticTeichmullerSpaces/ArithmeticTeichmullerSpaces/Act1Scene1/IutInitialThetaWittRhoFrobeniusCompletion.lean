import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittRhoFrobenius
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittRhoCompletion

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITT-RHO-FROBENIUS-COMPLETION
source: Joshi II `se:ff-rings`, Frobenius on the family of rho completions.
fidelity: extends the actual localization Frobenius to a continuous ring
homomorphism from the rho completion to the rho^p completion. Proves
agreement with the original inclusion and the exact norm-power law.
Original proofs; no reference implementation copied.
boundary: Scene1/Derived; all-radius automorphism, scalar algebra,
Tate-log eigenspace and paper B/BK identities remain separate obligations.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittRhoFrobeniusCompletion

open JoshiTeich.Prologue
open InitialThetaWittRhoCompletion
open scoped ENNReal Topology
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

def poweredRadius (ρ : Radius) : Radius :=
  ⟨ρ.val ^ Arithmetic.residueChar w.1, pos_iff_ne_zero.mpr (pow_ne_zero _ ρ.property.1.ne'),
    pow_lt_one₀ bot_le ρ.property.2 (Arithmetic.residueChar_prime w.1).ne_zero⟩

def sourceHom (ρ : Radius) : Source D w ρ →+* Source D w (poweredRadius D w ρ) :=
  (sourceEquiv D w (poweredRadius D w ρ)).toRingHom.comp
    ((InitialThetaBoundedWittLocalization.frobeniusEquiv D w).toRingHom.comp
      (sourceEquiv D w ρ).symm.toRingHom)

theorem sourceHom_norm (ρ : Radius) (x : Source D w ρ) :
    ‖sourceHom D w ρ x‖ = ‖x‖ ^ Arithmetic.residueChar w.1 :=
  InitialThetaWittRhoFrobenius.realValue_frobenius D w ρ.val
    ρ.property.1.ne' (ρ.property.2.trans ENNReal.one_lt_top).ne x

theorem sourceHom_continuous (ρ : Radius) : Continuous (sourceHom D w ρ) := by
  apply continuous_iff_continuousAt.mpr
  intro a
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have h := ((show Continuous (fun x : Source D w ρ => x - a) from
    continuous_id.sub continuous_const).norm.tendsto a).pow (Arithmetic.residueChar w.1)
  simpa only [← map_sub, sourceHom_norm, sub_self, norm_zero,
    zero_pow (Arithmetic.residueChar_prime w.1).ne_zero] using h

def completedHom (ρ : Radius) : Completed D w ρ →+* Completed D w (poweredRadius D w ρ) :=
  UniformSpace.Completion.mapRingHom (sourceHom D w ρ) (sourceHom_continuous D w ρ)

theorem completedHom_continuous (ρ : Radius) : Continuous (completedHom D w ρ) :=
  UniformSpace.Completion.continuous_map

theorem completedHom_inclusion (ρ : Radius) (x : InitialThetaBoundedWittLocalization.Ring D w) :
    completedHom D w ρ (inclusion D w ρ x) =
      inclusion D w (poweredRadius D w ρ) (InitialThetaBoundedWittLocalization.frobeniusEquiv D w x) :=
  UniformSpace.Completion.mapRingHom_coe (sourceHom_continuous D w ρ) (sourceEquiv D w ρ x)

theorem completedHom_norm (ρ : Radius) (x : Completed D w ρ) :
    ‖completedHom D w ρ x‖ = ‖x‖ ^ Arithmetic.residueChar w.1 := by
  refine (inclusion_denseRange D w ρ).induction_on
    (p := fun z : Completed D w ρ => ‖completedHom D w ρ z‖ = ‖z‖ ^ Arithmetic.residueChar w.1)
    x ?_ ?_
  · exact isClosed_eq (completedHom_continuous D w ρ).norm
      (continuous_norm.pow (Arithmetic.residueChar w.1))
  · intro y
    rw [completedHom_inclusion, inclusion_norm, inclusion_norm]
    exact InitialThetaWittRhoFrobenius.realValue_frobenius D w ρ.val
      ρ.property.1.ne' (ρ.property.2.trans ENNReal.one_lt_top).ne y

theorem completedHom_injective (ρ : Radius) : Function.Injective (completedHom D w ρ) := by
  apply (injective_iff_map_eq_zero (completedHom D w ρ)).mpr
  intro x hx
  have he := completedHom_norm D w ρ x
  rw [hx, norm_zero] at he
  exact norm_eq_zero.mp (eq_zero_of_pow_eq_zero he.symm)

end
end JoshiTeich.Act1Scene1.InitialThetaWittRhoFrobeniusCompletion
