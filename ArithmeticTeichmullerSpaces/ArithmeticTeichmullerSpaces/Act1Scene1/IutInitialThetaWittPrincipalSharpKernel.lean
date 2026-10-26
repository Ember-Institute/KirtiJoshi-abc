import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittPrincipalUnitLift

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITT-PRINCIPAL-SHARP-KERNEL
source: Joshi II `eq:tate-module-of-lubin-tate` and the period sequence
in the proof of `pr:teichmuller-lift-A`, with the multiplicative formal group.
fidelity: transports the proved compatible-root-tower/sharp-one equivalence
through the actual PreTilt-to-tilt-integers equivalence. The original Tate
towers embed into the principal tilt units, and their image is exactly the
kernel of the actual principal-unit sharp map.
Original proofs; no reference implementation copied.
boundary: Scene1/Derived; additive period-kernel comparisons are separate
consumers. No sharp-one existence or new comparison law is input. R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittPrincipalSharpKernel

open JoshiTeich.Prologue InitialThetaWittThetaBound
open InitialThetaWittPrincipalUnitDomain InitialThetaWittPrincipalUnitPeriod
open InitialThetaWittPrincipalUnitInjective InitialThetaWittPrincipalUnitLift
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

local instance selectedPrime : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩
local instance primeNorm : Fact
    (0 < ‖(Arithmetic.residueChar w.1 : Untilt D w)‖ ∧
      ‖(Arithmetic.residueChar w.1 : Untilt D w)‖ < 1) :=
  InitialThetaCanonicalGeometricFontaine.primeNormFact D w

theorem exists_epsilon_of_sharp_eq_one (y : InitialThetaTiltIntegers.Integers D w)
    (hy : InitialThetaTiltIntegers.sharp D w y = 1) :
    ∃ t : InitialThetaCyclotomicTateTilt.Tate D w, InitialThetaCyclotomicTateTilt.epsilon D w t = y := by
  let a : InitialThetaTiltField.Source D w := (InitialThetaTiltIntegers.preTiltEquiv D w).symm y
  have ha : GeometricTiltSharp.integralSharp (Untilt D w) (Arithmetic.residueChar w.1) a = 1 := by
    have h : InitialThetaTiltIntegers.sharp D w (InitialThetaTiltIntegers.preTiltEquiv D w a) = 1 := by
      rw [RingEquiv.apply_symm_apply]
      exact hy
    rw [InitialThetaTiltIntegers.sharp_preTiltEquiv] at h
    exact congrArg Subtype.val h
  let z : CyclotomicTateTilt.sharpOne (Untilt D w) (Arithmetic.residueChar w.1) := ⟨a, ha⟩
  let t := (CyclotomicTateTilt.sharpOneEquiv (Untilt D w) (Arithmetic.residueChar w.1)).symm z
  refine ⟨t, ?_⟩
  have ht : CyclotomicTateTilt.toPreTilt (Untilt D w) (Arithmetic.residueChar w.1) t = a :=
    congrArg Subtype.val
      ((CyclotomicTateTilt.sharpOneEquiv (Untilt D w) (Arithmetic.residueChar w.1)).apply_symm_apply z)
  change InitialThetaTiltIntegers.preTiltEquiv D w
    (CyclotomicTateTilt.toPreTilt (Untilt D w) (Arithmetic.residueChar w.1) t) = y
  rw [ht, RingEquiv.apply_symm_apply]

def tatePrincipalHom : InitialThetaCyclotomicTateTilt.Tate D w →* Principal D w where
  toFun := tatePrincipal D w
  map_one' := by
    apply integralValue_injective D w
    rw [integralValue_tatePrincipal, map_one, map_one]
  map_mul' t s := by
    apply integralValue_injective D w
    rw [map_mul, integralValue_tatePrincipal, integralValue_tatePrincipal,
      integralValue_tatePrincipal, map_mul]

theorem tatePrincipalHom_injective : Function.Injective (tatePrincipalHom D w) := by
  intro t s h
  apply InitialThetaCyclotomicTateTilt.epsilon_injective D w
  have he := congrArg (integralValue D w) h
  change integralValue D w (tatePrincipal D w t) = integralValue D w (tatePrincipal D w s) at he
  simpa only [integralValue_tatePrincipal] using he

theorem untiltCoordinate_eq_zero_iff (u : Principal D w) :
    untiltCoordinate D w u = 0 ↔ ∃ t : InitialThetaCyclotomicTateTilt.Tate D w,
      tatePrincipal D w t = u := by
  constructor
  · intro hu
    have hy : InitialThetaTiltIntegers.sharp D w (integralValue D w u) = 1 :=
      Subtype.ext (sub_eq_zero.mp hu)
    obtain ⟨t, ht⟩ := exists_epsilon_of_sharp_eq_one D w (integralValue D w u) hy
    refine ⟨t, integralValue_injective D w ?_⟩
    rw [integralValue_tatePrincipal]
    exact ht
  · rintro ⟨t, rfl⟩
    rw [untiltCoordinate, integralValue_tatePrincipal, InitialThetaCyclotomicTateTilt.sharp_epsilon,
      OneMemClass.coe_one, sub_self]

theorem sharpPrincipal_eq_one_iff (u : Principal D w) :
    sharpPrincipal D w u = 1 ↔ untiltCoordinate D w u = 0 := by
  constructor
  · intro hu
    change ((sharpPrincipal D w u : (Untilt D w)ˣ) : Untilt D w) - 1 = 0
    rw [hu]
    simp
  · intro hu
    apply Subtype.ext
    apply Units.ext
    exact sub_eq_zero.mp hu

theorem tatePrincipalHom_range : (tatePrincipalHom D w).range = (sharpPrincipal D w).ker := by
  ext u
  change (∃ t, tatePrincipal D w t = u) ↔ sharpPrincipal D w u = 1
  rw [sharpPrincipal_eq_one_iff, untiltCoordinate_eq_zero_iff]

end
end JoshiTeich.Act1Scene1.InitialThetaWittPrincipalSharpKernel
