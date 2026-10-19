import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaTiltIntegers
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
source-id: JT-SCENE1-INITIAL-THETA-TILT-FONTAINE
source: Joshi II canonical eta_K:W(O_F)->O_K (932),
pr:teichmuller-lift-A (940--958), and the primitive equation (838).
fidelity: transports the same Fontaine map to Witt vectors of the actual
tilt integers. Constructs norm-preserving integral Teichmuller lifts, exact
fibers and a nonzero [p-flat]-p kernel element. No period norm, principal
kernel identity, Tate-module identification or paper theta-value is assumed
or asserted. Original proofs; Scene1/Derived; Prologue-R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaTiltFontaine

open JoshiTeich.Prologue
universe u
noncomputable section
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)
local instance selectedPrime : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩
local instance primeNorm : Fact
    (0 < ‖(Arithmetic.residueChar w.1 : InitialThetaCanonicalGeometricFontaine.coefficientField D w)‖ ∧
      ‖(Arithmetic.residueChar w.1 : InitialThetaCanonicalGeometricFontaine.coefficientField D w)‖ < 1) :=
  InitialThetaCanonicalGeometricFontaine.primeNormFact D w

/-- Witt vectors of the actual tilt valuation integers. -/
abbrev Ainf := WittVector (Arithmetic.residueChar w.1) (InitialThetaTiltIntegers.Integers D w)

def preTiltWittEquiv :
    WittVector (Arithmetic.residueChar w.1) (InitialThetaTiltField.Source D w) ≃+* Ainf D w :=
  { WittVector.map (InitialThetaTiltIntegers.preTiltEquiv D w).toRingHom with
    invFun := WittVector.map (InitialThetaTiltIntegers.preTiltEquiv D w).symm.toRingHom
    left_inv x := by
      apply WittVector.ext
      intro n
      change (InitialThetaTiltIntegers.preTiltEquiv D w).symm
        (InitialThetaTiltIntegers.preTiltEquiv D w (x.coeff n)) = x.coeff n
      exact (InitialThetaTiltIntegers.preTiltEquiv D w).symm_apply_apply _
    right_inv x := by
      apply WittVector.ext
      intro n
      change InitialThetaTiltIntegers.preTiltEquiv D w
        ((InitialThetaTiltIntegers.preTiltEquiv D w).symm (x.coeff n)) = x.coeff n
      exact (InitialThetaTiltIntegers.preTiltEquiv D w).apply_symm_apply _ }

def theta : Ainf D w →+*
    LocalGeometricFontaine.integerRing (InitialThetaCanonicalGeometricFontaine.coefficientField D w) :=
  (Perfectoid.thetaMap
    (O := LocalGeometricFontaine.integerRing (InitialThetaCanonicalGeometricFontaine.coefficientField D w))
    (p := Arithmetic.residueChar w.1)).comp
    (preTiltWittEquiv D w).symm.toRingHom

/-- This is the same canonical Fontaine map after the proved domain equivalence. -/
theorem theta_preTiltWittEquiv
    (a : WittVector (Arithmetic.residueChar w.1) (InitialThetaTiltField.Source D w)) :
    theta D w (preTiltWittEquiv D w a) =
      (InitialThetaCanonicalGeometricFontaine.placeData D w).data.theta a := by
  change (InitialThetaCanonicalGeometricFontaine.placeData D w).data.theta
    ((preTiltWittEquiv D w).symm (preTiltWittEquiv D w a)) = _
  rw [RingEquiv.symm_apply_apply]

theorem theta_surjective : Function.Surjective (theta D w) :=
  (InitialThetaCanonicalGeometricFontaine.theta_surjective D w).comp
    (preTiltWittEquiv D w).symm.surjective

theorem theta_teichmuller (x : InitialThetaTiltIntegers.Integers D w) :
    theta D w (WittVector.teichmuller (Arithmetic.residueChar w.1) x) =
      InitialThetaTiltIntegers.sharp D w x := by
  change (InitialThetaCanonicalGeometricFontaine.placeData D w).data.theta
    (WittVector.map (InitialThetaTiltIntegers.preTiltEquiv D w).symm.toRingHom
      (WittVector.teichmuller (Arithmetic.residueChar w.1) x)) = _
  rw [WittVector.map_teichmuller]
  apply Subtype.ext
  change (((InitialThetaCanonicalGeometricFontaine.placeData D w).data.theta
    (WittVector.teichmuller (Arithmetic.residueChar w.1)
      ((InitialThetaTiltIntegers.preTiltEquiv D w).symm x))) :
        InitialThetaCanonicalGeometricFontaine.coefficientField D w) =
      InitialThetaTiltSharp.sharp D w x
  rw [InitialThetaTiltSharp.theta_teichmuller_eq_sharp,
    InitialThetaTiltIntegers.preTiltEquiv_symm_coe]

theorem theta_teichmuller_norm (x : InitialThetaTiltIntegers.Integers D w) :
    ‖theta D w (WittVector.teichmuller (Arithmetic.residueChar w.1) x)‖ = ‖x‖ := by
  rw [theta_teichmuller, InitialThetaTiltIntegers.sharp_norm]

/-- A compatible root tower in the same untilt produces an actual integral tilt lift. -/
def integralLift
    (z : LocalGeometricFontaine.integerRing (InitialThetaCanonicalGeometricFontaine.coefficientField D w)) :
    InitialThetaTiltIntegers.Integers D w :=
  InitialThetaTiltIntegers.preTiltEquiv D w
    (GeometricTiltSharp.rootLift (InitialThetaCanonicalGeometricFontaine.coefficientField D w)
      (Arithmetic.residueChar w.1) z)

theorem theta_integralLift
    (z : LocalGeometricFontaine.integerRing (InitialThetaCanonicalGeometricFontaine.coefficientField D w)) :
    theta D w (WittVector.teichmuller (Arithmetic.residueChar w.1) (integralLift D w z)) = z := by
  rw [theta_teichmuller, integralLift, InitialThetaTiltIntegers.sharp_preTiltEquiv]
  exact GeometricTiltSharp.untilt_rootLift _ _ z

theorem integralLift_norm
    (z : LocalGeometricFontaine.integerRing (InitialThetaCanonicalGeometricFontaine.coefficientField D w)) :
    ‖integralLift D w z‖ = ‖z‖ := by
  rw [← theta_teichmuller_norm, theta_integralLift]

/-- The local Teichmuller lifting assertion on the actual W(O_F) carrier. -/
theorem exists_teichmuller_lift
    (z : LocalGeometricFontaine.integerRing (InitialThetaCanonicalGeometricFontaine.coefficientField D w)) :
    ∃ x : InitialThetaTiltIntegers.Integers D w,
      theta D w (WittVector.teichmuller (Arithmetic.residueChar w.1) x) = z ∧ ‖x‖ = ‖z‖ :=
  ⟨integralLift D w z, theta_integralLift D w z, integralLift_norm D w z⟩

theorem integralLift_norm_lt_one
    (z : LocalGeometricFontaine.integerRing (InitialThetaCanonicalGeometricFontaine.coefficientField D w))
    (hz : ‖z‖ < 1) : ‖integralLift D w z‖ < 1 := by
  rwa [integralLift_norm]

/-- In particular n may be the actual theta-link exponent j^2. -/
theorem theta_integralLift_pow
    (z : LocalGeometricFontaine.integerRing (InitialThetaCanonicalGeometricFontaine.coefficientField D w))
    (n : ℕ) :
    theta D w ((WittVector.teichmuller (Arithmetic.residueChar w.1) (integralLift D w z)) ^ n) =
      z ^ n := by
  rw [map_pow, theta_integralLift]

/-- The entire fiber is the kernel translate of the constructed Teichmuller lift. -/
theorem theta_fiber
    (z : LocalGeometricFontaine.integerRing (InitialThetaCanonicalGeometricFontaine.coefficientField D w))
    (a : Ainf D w) :
    theta D w a = z ↔ ∃ k ∈ RingHom.ker (theta D w),
      a = k + WittVector.teichmuller (Arithmetic.residueChar w.1) (integralLift D w z) := by
  constructor
  · intro h
    refine ⟨a - WittVector.teichmuller (Arithmetic.residueChar w.1) (integralLift D w z), ?_,
      (sub_add_cancel _ _).symm⟩
    change theta D w _ = 0
    rw [map_sub, h, theta_integralLift, sub_self]
  · rintro ⟨k, hk, rfl⟩
    change theta D w k = 0 at hk
    rw [map_add, hk, theta_integralLift, zero_add]

theorem theta_kernel_isPrime : (RingHom.ker (theta D w)).IsPrime :=
  RingHom.ker_isPrime (theta D w)

def quotientEquiv : (Ainf D w ⧸ RingHom.ker (theta D w)) ≃+*
    LocalGeometricFontaine.integerRing (InitialThetaCanonicalGeometricFontaine.coefficientField D w) :=
  (theta D w).quotientKerEquivOfSurjective (theta_surjective D w)

theorem quotientEquiv_mk (a : Ainf D w) :
    quotientEquiv D w (Ideal.Quotient.mk _ a) = theta D w a :=
  RingHom.quotientKerEquivOfSurjective_apply_mk _ _

/-- The actual primitive-equation candidate; generation of the whole kernel is separate. -/
def primitive : Ainf D w :=
  WittVector.teichmuller (Arithmetic.residueChar w.1)
    (integralLift D w (Arithmetic.residueChar w.1)) - Arithmetic.residueChar w.1

theorem primitive_mem_kernel : primitive D w ∈ RingHom.ker (theta D w) := by
  change theta D w (primitive D w) = 0
  rw [primitive, map_sub, theta_integralLift, map_natCast, sub_self]

theorem primitive_ne_zero : primitive D w ≠ 0 := by
  have hpcast : (Arithmetic.residueChar w.1 : InitialThetaTiltIntegers.Integers D w) = 0 :=
    CharP.cast_eq_zero _ _
  have hc : WittVector.constantCoeff (primitive D w) =
      integralLift D w (Arithmetic.residueChar w.1) := by
    rw [primitive, map_sub, map_natCast, hpcast, sub_zero]
    rfl
  have hp : 0 < ‖integralLift D w (Arithmetic.residueChar w.1)‖ := by
    rw [integralLift_norm]
    exact (InitialThetaCanonicalGeometricFontaine.primeNormFact D w).out.1
  intro h
  exact (norm_pos_iff.mp hp) (hc.symm.trans (by rw [h, map_zero]))

end
end JoshiTeich.Act1Scene1.InitialThetaTiltFontaine
