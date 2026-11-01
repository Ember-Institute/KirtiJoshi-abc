import ArithmeticTeichmullerSpaces.Act1Scene1.GeometricTiltIntegerRing
import ArithmeticTeichmullerSpaces.Act1Scene1.PadicTiltField

/-!
source-id: JT-SCENE1-PADIC-TILT-INTEGER-RING-BRIDGE
source: Joshi II `se:ff-rings`, specialized to Mathlib's standard
`PadicComplex p` and the independently constructed standard tilt carrier.
fidelity: specializes the generic PreTilt-to-fraction-field integer-ring
equivalence to `C_p^flat`. It exposes the standard source/integer-ring bridge
without constructing Witt vectors, p-localization, bounded localization, rho
norms, Frechet completion, or paper `B`. Original proof; Prologue R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.PadicTiltIntegerRingBridge

noncomputable section
variable (p : ℕ) [Fact p.Prime]

abbrev StandardIntegers := PadicTiltField.Integers p

def preTiltEquiv : PadicTiltField.Source p ≃+* StandardIntegers p :=
  GeometricTiltIntegerRing.preTiltEquiv (PadicComplex p) p

theorem preTiltEquiv_apply (x : PadicTiltField.Source p) :
    (preTiltEquiv p x : PadicTiltField.Carrier p) =
      algebraMap (PadicTiltField.Source p) (PadicTiltField.Carrier p) x := rfl

theorem preTiltEquiv_norm (x : PadicTiltField.Source p) :
    ‖preTiltEquiv p x‖ = ‖x‖ :=
  GeometricTiltIntegerRing.preTiltEquiv_norm (PadicComplex p) p x

end
end JoshiTeich.Act1Scene1.PadicTiltIntegerRingBridge
