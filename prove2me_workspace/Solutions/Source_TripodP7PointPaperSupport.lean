import Solutions.Source_ReferenceIutPointThetaData
import Solutions.Source_TripodP7PaperSupport

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut.CurveInputs

open NumberField

universe u

variable {T : Genl.HeightTheory} {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}
variable {K : T.CBS} {d : ℕ}
variable (CI : CurveInputs.{u} T AG K d) (anab : AnabelianExistence AG TG)
variable (x : T.Pt T.tripod) (hx : x ∈ T.cbsSet K ∩ T.ptLE T.tripod d)
variable (hxe : x ∉ CI.toCorollary22Inputs.excCore) (ℓ : ℕ) (hℓ : ℓ.Prime) (h7 : 7 ≤ ℓ)
variable (hP2 : ∀ w ∈ (CI.toCorollary22Inputs.localData x hx).bad,
  ¬ ℓ ∣ (CI.toCorollary22Inputs.localData x hx).hv w)
variable (hP5 : ∃ w ∈ (CI.toCorollary22Inputs.localData x hx).bad,
  (CI.toCorollary22Inputs.localData x hx).p w ≠ 2 ∧
    (CI.toCorollary22Inputs.localData x hx).p w ≠ ℓ)
variable (hsl : CI.toCorollary22Inputs.SL2Image x ℓ)
variable (E₀ : WeierstrassCurve ↥(fieldOfModuli (CI.curve x hx).F (CI.curve x hx).E))

/-- The initial data of the chosen P7 point and prime retain the same support
difference against the split-multiplicative places of the moduli model. -/
theorem pointThetaData_VBad_diff_joshiIIIBadModuliSupport :
    let W := CI.pointThetaData anab x hx hxe ℓ hℓ h7 hP2 hP5 hsl
    let C := CI.curve x hx
    W.data.VBad \ C.joshiIIIBadModuliSupport E₀ =
      (C.VBadOdd \ C.joshiIIIBadModuliSupport E₀) ∩ {v | residueChar v ≠ W.data.ℓ} := by
  intro W C
  rw [W.prime_eq]
  change C.VBadOf ℓ \ C.joshiIIIBadModuliSupport E₀ = _
  exact C.VBadOf_diff_joshiIIIBadModuliSupport E₀ ℓ

/-- For a moduli model with the same j-invariant, the paper places omitted by the
chosen P7 initial data lie precisely in its selected residue-characteristic fibre. -/
theorem pointThetaData_joshiIIIBadModuliSupport_diff_VBad [E₀.IsElliptic]
    (hj : E₀.j = (CI.curve x hx).jMod) :
    let W := CI.pointThetaData anab x hx hxe ℓ hℓ h7 hP2 hP5 hsl
    let C := CI.curve x hx
    C.joshiIIIBadModuliSupport E₀ \ W.data.VBad =
      C.joshiIIIBadModuliSupport E₀ ∩ {v | residueChar v = W.data.ℓ} := by
  intro W C
  rw [W.prime_eq]
  change C.joshiIIIBadModuliSupport E₀ \ C.VBadOf ℓ = _
  exact C.joshiIIIBadModuliSupport_diff_VBadOf E₀ (CI.arith x hx) hj ℓ

end AbcAdaptation.Reference.Iut.CurveInputs
