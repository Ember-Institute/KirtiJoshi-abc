import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittRhoFrobeniusEquiv
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittAllRadiusCompletion

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITT-PRODUCT-FROBENIUS
source: Joshi II `se:ff-rings`, Frobenius and the family of rho norms.
fidelity: proves the radius-power map is a bijection of the open unit
interval, and assembles the actual fixed-radius Frobenius equivalences
into a continuous automorphism of the all-radius product ring. Computes
both maps on the original bounded localization diagonal.
Original proofs; no reference implementation copied.
boundary: Scene1/Derived; restriction to the common closure is separate.
No scalar algebra, Tate-log eigenspace or paper B/BK identity is assumed.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittProductFrobenius

open JoshiTeich.Prologue
open InitialThetaWittRhoCompletion InitialThetaWittRhoFrobeniusCompletion
open InitialThetaWittRhoFrobeniusEquiv
open scoped ENNReal Topology
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

def radiusEquiv : Radius ≃ Radius := by
  let E := ENNReal.powOrderIso (Arithmetic.residueChar w.1) (Arithmetic.residueChar_prime w.1).ne_zero
  have h0 : E 0 = 0 := zero_pow (Arithmetic.residueChar_prime w.1).ne_zero
  have h1 : E 1 = 1 := one_pow _
  refine
    { toFun := poweredRadius D w
      invFun := fun r => ⟨E.symm r.val, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · constructor
    · apply E.lt_iff_lt.mp
      simpa only [h0, E.apply_symm_apply] using r.property.1
    · apply E.lt_iff_lt.mp
      simpa only [h1, E.apply_symm_apply] using r.property.2
  · intro r
    apply Subtype.ext
    exact E.symm_apply_apply r.val
  · intro r
    apply Subtype.ext
    exact E.apply_symm_apply r.val

theorem radiusEquiv_apply (ρ : Radius) : radiusEquiv D w ρ = poweredRadius D w ρ := rfl

abbrev Product := InitialThetaWittAllRadiusCompletion.Product D w

def productEquiv : Product D w ≃+* Product D w :=
  (RingEquiv.piCongrRight (completedEquiv D w)).trans
    (RingEquiv.piCongrLeft (Completed D w) (radiusEquiv D w))

theorem productEquiv_powered (x : Product D w) (ρ : Radius) :
    productEquiv D w x (poweredRadius D w ρ) = completedEquiv D w ρ (x ρ) :=
  Equiv.piCongrLeft_apply_apply _ _ _ _

theorem productEquiv_symm_apply (x : Product D w) (ρ : Radius) :
    (productEquiv D w).symm x ρ = (completedEquiv D w ρ).symm (x (poweredRadius D w ρ)) := rfl

theorem productEquiv_continuous : Continuous (productEquiv D w) := by
  apply continuous_pi
  intro r
  obtain ⟨ρ, rfl⟩ := (radiusEquiv D w).surjective r
  exact ((completedEquiv_continuous D w ρ).comp
    (continuous_apply ρ : Continuous (fun x : Product D w => x ρ))).congr
    (fun x => (productEquiv_powered D w x ρ).symm)

theorem productEquiv_symm_continuous : Continuous (productEquiv D w).symm :=
  continuous_pi (fun ρ => (completedEquiv_symm_continuous D w ρ).comp
    (continuous_apply (poweredRadius D w ρ)))

theorem productEquiv_diagonal (x : InitialThetaBoundedWittLocalization.Ring D w) :
    productEquiv D w (InitialThetaWittAllRadiusCompletion.diagonal D w x) =
      InitialThetaWittAllRadiusCompletion.diagonal D w
        (InitialThetaBoundedWittLocalization.frobeniusEquiv D w x) := by
  apply funext
  intro r
  obtain ⟨ρ, rfl⟩ := (radiusEquiv D w).surjective r
  rw [radiusEquiv_apply, productEquiv_powered]
  exact completedEquiv_inclusion D w ρ x

theorem productEquiv_symm_diagonal (x : InitialThetaBoundedWittLocalization.Ring D w) :
    (productEquiv D w).symm (InitialThetaWittAllRadiusCompletion.diagonal D w x) =
      InitialThetaWittAllRadiusCompletion.diagonal D w
        ((InitialThetaBoundedWittLocalization.frobeniusEquiv D w).symm x) := by
  apply (productEquiv D w).injective
  rw [RingEquiv.apply_symm_apply, productEquiv_diagonal, RingEquiv.apply_symm_apply]

end
end JoshiTeich.Act1Scene1.InitialThetaWittProductFrobenius
