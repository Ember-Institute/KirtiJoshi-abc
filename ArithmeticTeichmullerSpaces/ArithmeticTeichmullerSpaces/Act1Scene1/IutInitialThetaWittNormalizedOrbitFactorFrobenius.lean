import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittNormalizedOrbitProduct

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITT-NORMALIZED-ORBIT-FACTOR-FROBENIUS
source: Joshi II `se:ff-rings`, `pr:primitive-elements1` and
`pr:teichmuller-lift-A`, Frobenius shift of primitive period factors.
fidelity: proves the exact local shift law phi(f_n)=f_(n+1) for the
normalized actual primitive Frobenius orbit. The normalizing unit is
fixed because the actual Frobenius fixes the embedded residue prime.
Original proofs; no reference implementation copied.
boundary: Scene1/Derived; this is the factor shift law only. It does
not identify the infinite product with a Tate period or assert the full
kernel identity. Original topology and Prologue R5 retained.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittNormalizedOrbitFactorFrobenius

open JoshiTeich.Prologue InitialThetaWittAllRadiusCompletion
open InitialThetaWittAllRadiusFrobenius InitialThetaWittNormalizedOrbitProduct
open InitialThetaWittFrobeniusThetaOrbit
open scoped Topology
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

local instance selectedPrime : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

theorem frobenius_primeUnit :
    InitialThetaWittAllRadiusFrobenius.frobeniusEquiv D w
        (primeUnit D w : Carrier D w) = primeUnit D w := by
  rw [primeUnit_val D w]
  simpa only [map_natCast] using
    (frobenius_padic D w
      (Arithmetic.residueChar w.1 : Padic (Arithmetic.residueChar w.1)))

theorem frobenius_scaleUnit :
    InitialThetaWittAllRadiusFrobenius.frobeniusEquiv D w
        (scaleUnit D w : Carrier D w) = scaleUnit D w := by
  change InitialThetaWittAllRadiusFrobenius.frobeniusEquiv D w
      (-(((primeUnit D w)⁻¹ : (Carrier D w)ˣ) : Carrier D w)) =
    -(((primeUnit D w)⁻¹ : (Carrier D w)ˣ) : Carrier D w)
  rw [map_neg]
  have hu : Units.map
      (InitialThetaWittAllRadiusFrobenius.frobeniusEquiv D w).toMonoidHom
      (primeUnit D w) = primeUnit D w := by
    apply Units.ext
    exact frobenius_primeUnit D w
  have hi := congrArg (fun u : (InitialThetaWittAllRadiusCompletion.Carrier D w)ˣ =>
      (u : InitialThetaWittAllRadiusCompletion.Carrier D w)) (congrArg Inv.inv hu)
  rw [Units.coe_map_inv] at hi
  exact congrArg Neg.neg hi

theorem frobenius_factor (n : ℕ) :
    InitialThetaWittAllRadiusFrobenius.frobeniusEquiv D w (factor D w n) =
      factor D w (n + 1) := by
  rw [factor, map_mul, frobenius_scaleUnit]
  change (scaleUnit D w : Carrier D w) *
    InitialThetaWittAllRadiusFrobenius.frobeniusEquiv D w (primitiveOrbit D w n) =
    (scaleUnit D w : Carrier D w) * primitiveOrbit D w (n + 1)
  exact congrArg (fun z : Carrier D w => (scaleUnit D w : Carrier D w) * z)
    (InitialThetaWittFrobeniusThetaOrbit.primitiveOrbit_succ D w n).symm

end
end JoshiTeich.Act1Scene1.InitialThetaWittNormalizedOrbitFactorFrobenius
