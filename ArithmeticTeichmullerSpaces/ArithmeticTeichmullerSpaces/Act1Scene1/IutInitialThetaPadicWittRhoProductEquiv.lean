import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaPadicWittRhoCompletionComparison
import ArithmeticTeichmullerSpaces.Act1Scene1.PadicWittAllRadiusCompletion
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittAllRadiusCompletion

/-!
source-id: JT-SCENE1-ACTUAL-STANDARD-PADIC-WITT-RHO-PRODUCT-EQUIV
source: Joshi II `se:ff-rings` and `pr:teichmuller-lift-A/B`, the all-radius
family of rho completions and its local-degree radius reparameterization.
fidelity: reindexes the actual all-radius product by `rho ↦ rho ^ localDeg(w)`
and applies the proved fixed-radius completion equivalences coordinatewise.
The product equivalence is continuous in both directions.
Original proof; no reference implementation copied.
boundary: diagonal compatibility, closure-carrier restriction, paper B,
Fréchet identities and period/BK comparisons remain separate.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaPadicWittRhoProductEquiv

open JoshiTeich.Prologue
open InitialThetaWittRhoCompletion
open InitialThetaPadicWittRhoCompletionComparison
open scoped ENNReal Topology
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

local instance selectedPrimeProduct : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

abbrev Radius := PadicWittRhoCompletion.Radius

def radiusEquiv : Radius ≃ InitialThetaWittRhoCompletion.Radius := by
  let E := ENNReal.powOrderIso (Arithmetic.localDeg w.1)
    (Arithmetic.localDeg_pos w.1).ne_zero
  have h0 : E 0 = 0 := zero_pow (Arithmetic.localDeg_pos w.1).ne_zero
  have h1 : E 1 = 1 := one_pow _
  refine
    { toFun := actualRadius D w
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

theorem radiusEquiv_apply (ρ : Radius) : radiusEquiv D w ρ = actualRadius D w ρ := rfl

abbrev StdProduct := PadicWittAllRadiusCompletion.Product (Arithmetic.residueChar w.1)
abbrev ActProduct := InitialThetaWittAllRadiusCompletion.Product D w

def productEquiv : StdProduct D w ≃+* ActProduct D w :=
  (RingEquiv.piCongrRight (fun ρ => (completedRingEquiv D w ρ).symm)).trans
    (RingEquiv.piCongrLeft (fun α => InitialThetaWittRhoCompletion.Completed D w α)
      (radiusEquiv D w))

theorem productEquiv_actual (x : StdProduct D w) (ρ : Radius) :
    productEquiv D w x (actualRadius D w ρ) =
      (completedRingEquiv D w ρ).symm (x ρ) := by
  exact Equiv.piCongrLeft_apply_apply _ _ _ _

theorem productEquiv_symm_apply (x : ActProduct D w) (ρ : Radius) :
    (productEquiv D w).symm x ρ =
      completedRingEquiv D w ρ (x (actualRadius D w ρ)) := rfl

theorem productEquiv_continuous : Continuous (productEquiv D w) := by
  apply continuous_pi
  intro α
  obtain ⟨ρ, rfl⟩ := (radiusEquiv D w).surjective α
  exact ((completedRingEquiv_symm_continuous D w ρ).comp
    (continuous_apply ρ : Continuous (fun x : StdProduct D w => x ρ))).congr
    (fun x => (productEquiv_actual D w x ρ).symm)

theorem productEquiv_symm_continuous : Continuous (productEquiv D w).symm :=
  continuous_pi (fun ρ => (completedRingEquiv_continuous D w ρ).comp
    (continuous_apply (actualRadius D w ρ)))

end
end JoshiTeich.Act1Scene1.InitialThetaPadicWittRhoProductEquiv
