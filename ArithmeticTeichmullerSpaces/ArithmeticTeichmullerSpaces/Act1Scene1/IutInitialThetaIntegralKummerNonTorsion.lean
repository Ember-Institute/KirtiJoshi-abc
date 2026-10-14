import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaCoefficientChange
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaRationalKummerNonzero

/-!
source-id: JT-SCENE1-INITIAL-THETA-INTEGRAL-KUMMER-NONTORSION
source: actual integral/rational coefficient comparison, Joshi III (3214--3236).
fidelity: proves that the actual standard integral Kummer class is not killed
by any nonzero p-adic integral scalar, using the already proved nonvanishing of
the actual rational class. This is an actual-class result, not injectivity of
the coefficient map on all H1 and not an H^1_e/BK identification.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.PrincipalUnitKummer
open JoshiTeich.Prologue
universe u
noncomputable section
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)

local instance integralNonTorsionResiduePrime
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    Fact (Arithmetic.residueChar s.1).Prime := ⟨Arithmetic.residueChar_prime s.1⟩

local instance integralNonTorsionCharZero
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    CharZero (localField D s) :=
  charZero_of_injective_ringHom (NumberField.FinitePlace.embedding s.1.maximalIdeal).injective

theorem padicClass_smul_ne_zero
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset)
    {r : ℤ_[Arithmetic.residueChar s.1]} (hr : r ≠ 0) :
    r • padicClass D s ≠ 0 := by
  intro hzero
  have hmap := congrArg
    (LocalKummer.Rational.standardMap (Arithmetic.residueChar s.1)) hzero
  rw [map_smulₛₗ, map_zero] at hmap
  have hcast : (r : ℚ_[Arithmetic.residueChar s.1]) ≠ 0 :=
    PadicInt.coe_ne_zero.mpr hr
  have hrat : rationalClass D s = 0 := by
    rw [rationalClass_eq_changeCoefficients D s]
    exact (smul_eq_zero.mp hmap).resolve_left hcast
  exact rationalClass_ne_zero D s hrat

end
end JoshiTeich.Act1Scene1.PrincipalUnitKummer
