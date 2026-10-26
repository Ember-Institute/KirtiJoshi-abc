import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittPrincipalUnitLiftBound
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittPrincipalUnitInjective
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittRationalTatePeriod

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITT-PRINCIPAL-UNIT-LIFT
source: Joshi II `pr:teichmuller-lift-A` and the multiplicative formal
group description of B^{phi=p} following that proposition.
fidelity: actual sharp restricts to a surjective homomorphism of the
principal-unit groups. A right inverse uses the existing compatible-root
tower in the original untilt. Its actual log([u]) period is a phi=p
element whose theta value is the convergent ordinary logarithm series
of the prescribed untilt principal unit.
Original proofs; no reference implementation copied.
boundary: Scene1/Derived; logarithm surjectivity to the entire untilt,
the full period/kernel comparison and the paper identity remain open.
The root lift is a choice of elements, not a claimed group section.
No new comparison or surjectivity law is input. R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittPrincipalUnitLift

open JoshiTeich.Prologue InitialThetaWittThetaBound
open InitialThetaWittPrincipalUnitDomain InitialThetaWittPrincipalUnitPeriod
open InitialThetaWittLogarithmSeries InitialThetaWittRationalTatePeriod
open scoped Topology
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

local instance selectedPrime : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

abbrev UntilPrincipal := UltrametricPrincipalUnits.subgroup (Untilt D w)

def untiltValue : UntilPrincipal D w →* LocalGeometricFontaine.integerRing (Untilt D w) where
  toFun z := ⟨((z : (Untilt D w)ˣ) : Untilt D w),
    (LocalGeometricFontaine.mem_integerRing _ _).mpr
      (le_of_eq (UltrametricPrincipalUnits.norm_coe (Untilt D w) z))⟩
  map_one' := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl

def sharpPrincipal : Principal D w →* UntilPrincipal D w where
  toFun v := ⟨Units.map (InitialThetaTiltSharp.sharp D w).toMonoidHom v.val,
    untiltCoordinate_lt_one D w v⟩
  map_one' := Subtype.ext (map_one (Units.map (InitialThetaTiltSharp.sharp D w).toMonoidHom))
  map_mul' v v' := Subtype.ext
    (map_mul (Units.map (InitialThetaTiltSharp.sharp D w).toMonoidHom) v.val v'.val)

theorem sharpPrincipal_coe (v : Principal D w) :
    ((sharpPrincipal D w v : (Untilt D w)ˣ) : Untilt D w) =
      InitialThetaTiltSharp.sharp D w ((v : (InitialThetaTiltField.Carrier D w)ˣ) :
        InitialThetaTiltField.Carrier D w) := rfl

def principalLift (z : UntilPrincipal D w) : Principal D w := by
  let y : InitialThetaTiltField.Carrier D w :=
    InitialThetaTiltFontaine.integralLift D w (untiltValue D w z)
  have hy : ‖y - 1‖ < 1 :=
    InitialThetaWittPrincipalUnitLiftBound.integralLift_near_one D w (untiltValue D w z) z.property
  have hn : ‖y‖ = 1 := UltrametricPrincipalUnits.norm_eq_one _ hy
  have hy0 : y ≠ 0 := norm_pos_iff.mp (hn ▸ zero_lt_one)
  exact ⟨Units.mk0 y hy0, hy⟩

theorem principalLift_coe (z : UntilPrincipal D w) :
    ((principalLift D w z : (InitialThetaTiltField.Carrier D w)ˣ) : InitialThetaTiltField.Carrier D w) =
      (InitialThetaTiltFontaine.integralLift D w (untiltValue D w z) :
        InitialThetaTiltField.Carrier D w) := rfl

theorem sharpPrincipal_principalLift (z : UntilPrincipal D w) :
    sharpPrincipal D w (principalLift D w z) = z := by
  apply Subtype.ext
  apply Units.ext
  rw [sharpPrincipal_coe, principalLift_coe]
  exact congrArg Subtype.val
    ((InitialThetaTiltFontaine.theta_teichmuller D w
      (InitialThetaTiltFontaine.integralLift D w (untiltValue D w z))).symm.trans
        (InitialThetaTiltFontaine.theta_integralLift D w (untiltValue D w z)))

theorem sharpPrincipal_surjective : Function.Surjective (sharpPrincipal D w) :=
  fun z => ⟨principalLift D w z, sharpPrincipal_principalLift D w z⟩

theorem untiltCoordinate_principalLift (z : UntilPrincipal D w) :
    untiltCoordinate D w (principalLift D w z) = ((z : (Untilt D w)ˣ) : Untilt D w) - 1 :=
  congrArg (fun q : UntilPrincipal D w => ((q : (Untilt D w)ˣ) : Untilt D w) - 1)
    (sharpPrincipal_principalLift D w z)

def liftPeriod (z : UntilPrincipal D w) :
    InitialThetaWittAdditiveTatePeriod.frobeniusPrimeSubmodule D w :=
  eigenLogHom D w (Additive.ofMul (principalLift D w z))

theorem liftPeriod_val (z : UntilPrincipal D w) :
    (liftPeriod D w z : InitialThetaWittAllRadiusCompletion.Carrier D w) =
      periodLog D w (principalLift D w z) := rfl

theorem hasSum_eigenEvaluation_liftPeriod (z : UntilPrincipal D w) :
    HasSum (fun n : ℕ => logCoefficient D w n •
      (((z : (Untilt D w)ˣ) : Untilt D w) - 1) ^ n)
      (eigenEvaluation D w (liftPeriod D w z)) := by
  have h := hasSum_evaluation_periodLog D w (principalLift D w z)
  rw [untiltCoordinate_principalLift] at h
  exact h

theorem eigenEvaluation_liftPeriod_eq_tsum (z : UntilPrincipal D w) :
    eigenEvaluation D w (liftPeriod D w z) =
      ∑' n : ℕ, logCoefficient D w n • (((z : (Untilt D w)ˣ) : Untilt D w) - 1) ^ n :=
  (hasSum_eigenEvaluation_liftPeriod D w z).tsum_eq.symm

theorem exists_eigenPeriod_logarithm (z : UntilPrincipal D w) :
    ∃ v : InitialThetaWittAdditiveTatePeriod.frobeniusPrimeSubmodule D w,
      HasSum (fun n : ℕ => logCoefficient D w n •
        (((z : (Untilt D w)ˣ) : Untilt D w) - 1) ^ n) (eigenEvaluation D w v) :=
  ⟨liftPeriod D w z, hasSum_eigenEvaluation_liftPeriod D w z⟩

end
end JoshiTeich.Act1Scene1.InitialThetaWittPrincipalUnitLift
