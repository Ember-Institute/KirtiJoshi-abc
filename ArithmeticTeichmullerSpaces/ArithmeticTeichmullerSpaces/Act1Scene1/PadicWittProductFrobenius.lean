import ArithmeticTeichmullerSpaces.Act1Scene1.PadicWittRhoFrobeniusCompletion
import ArithmeticTeichmullerSpaces.Act1Scene1.PadicWittAllRadiusCompletion

/-!
source-id: JT-SCENE1-STANDARD-PADIC-WITT-PRODUCT-FROBENIUS
source: Joshi II `se:ff-rings`, Frobenius and the family of rho norms.
fidelity: proves the radius-power map is a bijection of the open unit
interval, and assembles the standard fixed-radius Frobenius equivalences
into a continuous automorphism of the all-radius product ring. Computes
both maps on the original bounded localization diagonal.
boundary: Scene1/Derived; restriction to the common closure is separate.
No scalar algebra, Tate-log eigenspace or paper B/BK identity is assumed.
-/

namespace JoshiTeich.Act1Scene1.PadicWittProductFrobenius

open PadicBoundedWittLocalization
open PadicWittRhoFrobeniusCompletion
open PadicWittRhoFrobenius
open scoped ENNReal Topology
noncomputable section

variable (p : ℕ) [Fact p.Prime]

abbrev Radius := PadicWittRhoCompletion.Radius
abbrev Product := PadicWittAllRadiusCompletion.Product p

def radiusEquiv : Radius ≃ Radius := by
  let E := ENNReal.powOrderIso p (Fact.out : p.Prime).ne_zero
  have h0 : E 0 = 0 := zero_pow (Fact.out : p.Prime).ne_zero
  have h1 : E 1 = 1 := one_pow _
  refine
    { toFun := poweredRadius p
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

theorem radiusEquiv_apply (ρ : Radius) :
    radiusEquiv p ρ = poweredRadius p ρ := rfl

def productEquiv : Product p ≃+* Product p :=
  (RingEquiv.piCongrRight (completedEquiv p)).trans
    (RingEquiv.piCongrLeft (Completed p) (radiusEquiv p))

theorem productEquiv_powered (x : Product p) (ρ : Radius) :
    productEquiv p x (poweredRadius p ρ) = completedEquiv p ρ (x ρ) :=
  Equiv.piCongrLeft_apply_apply _ _ _ _

theorem productEquiv_symm_apply (x : Product p) (ρ : Radius) :
    (productEquiv p).symm x ρ =
      (completedEquiv p ρ).symm (x (poweredRadius p ρ)) := rfl

theorem productEquiv_continuous : Continuous (productEquiv p) := by
  apply continuous_pi
  intro r
  obtain ⟨ρ, rfl⟩ := (radiusEquiv p).surjective r
  exact ((completedEquiv_continuous p ρ).comp
    (continuous_apply ρ : Continuous (fun x : Product p => x ρ))).congr
    (fun x => (productEquiv_powered p x ρ).symm)

theorem productEquiv_symm_continuous : Continuous (productEquiv p).symm :=
  continuous_pi (fun ρ => (completedEquiv_symm_continuous p ρ).comp
    (continuous_apply (poweredRadius p ρ)))

theorem productEquiv_diagonal (x : Ring p) :
    productEquiv p (PadicWittAllRadiusCompletion.diagonal p x) =
      PadicWittAllRadiusCompletion.diagonal p (frobeniusEquiv p x) := by
  apply funext
  intro r
  obtain ⟨ρ, rfl⟩ := (radiusEquiv p).surjective r
  rw [radiusEquiv_apply, productEquiv_powered]
  exact completedEquiv_inclusion p ρ x

theorem productEquiv_symm_diagonal (x : Ring p) :
    (productEquiv p).symm (PadicWittAllRadiusCompletion.diagonal p x) =
      PadicWittAllRadiusCompletion.diagonal p ((frobeniusEquiv p).symm x) := by
  apply (productEquiv p).injective
  rw [RingEquiv.apply_symm_apply, productEquiv_diagonal, RingEquiv.apply_symm_apply]

end
end JoshiTeich.Act1Scene1.PadicWittProductFrobenius
