import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaDeRhamField

/-!
source-id: JT-SCENE1-INITIAL-THETA-DE-RHAM-TEICHMULLER
source: Joshi II pr:teichmuller-lift-A (940--958) and the inclusion into
B_dR (1069--1076); the same actual Witt-vector and Fontaine producers.
fidelity: maps actual W(O_F) into the original BDeRhamPlus, retaining theta.
Transports the constructed Teichmuller lifts, powers and the full principal
kernel fiber. Norms here are untilt evaluation norms; no Frechet/rho norm,
Tate-module identity or paper theta-locus identity is asserted.
Original proofs, no reference-engine copy; Prologue-R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaDeRhamTeichmuller

open JoshiTeich.Prologue InitialThetaDeRhamCompletion
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

def localizationToPlus : InitialThetaFontaineLocalization.AinfInvertP D w →+* Ring D w :=
  (algebraMap (Source D w) (AdicCompletion (sourceKernel D w) (Source D w))).comp
    (InitialThetaFontaineLocalization.sourceLocalizationEquiv D w).symm.toRingHom

theorem theta_localizationToPlus (a : InitialThetaFontaineLocalization.AinfInvertP D w) :
    theta D w (localizationToPlus D w a) = InitialThetaFontaineLocalization.theta D w a :=
  theta_of_actual D w a

def ainfToPlus : InitialThetaTiltFontaine.Ainf D w →+* Ring D w :=
  (localizationToPlus D w).comp (algebraMap (InitialThetaTiltFontaine.Ainf D w)
    (InitialThetaFontaineLocalization.AinfInvertP D w))

theorem theta_ainfToPlus (a : InitialThetaTiltFontaine.Ainf D w) :
    theta D w (ainfToPlus D w a) = (InitialThetaTiltFontaine.theta D w a :
      InitialThetaCanonicalGeometricFontaine.coefficientField D w) := by
  change theta D w (localizationToPlus D w (algebraMap _ _ a)) = _
  rw [theta_localizationToPlus, InitialThetaFontaineLocalization.theta_algebraMap]

def lift
    (z : LocalGeometricFontaine.integerRing (InitialThetaCanonicalGeometricFontaine.coefficientField D w)) :
    Ring D w :=
  ainfToPlus D w (WittVector.teichmuller (Arithmetic.residueChar w.1)
    (InitialThetaTiltFontaine.integralLift D w z))

theorem theta_lift
    (z : LocalGeometricFontaine.integerRing (InitialThetaCanonicalGeometricFontaine.coefficientField D w)) :
    theta D w (lift D w z) = z := by
  rw [lift, theta_ainfToPlus, InitialThetaTiltFontaine.theta_integralLift]

theorem theta_lift_pow
    (z : LocalGeometricFontaine.integerRing (InitialThetaCanonicalGeometricFontaine.coefficientField D w))
    (n : ℕ) : theta D w (lift D w z ^ n) = (z :
      InitialThetaCanonicalGeometricFontaine.coefficientField D w) ^ n := by
  rw [map_pow, theta_lift]

theorem evaluation_norm
    (z : LocalGeometricFontaine.integerRing (InitialThetaCanonicalGeometricFontaine.coefficientField D w))
    (n : ℕ) : ‖theta D w (lift D w z ^ n)‖ = ‖z‖ ^ n := by
  rw [theta_lift_pow, norm_pow]
  rfl

theorem lift_isUnit
    (z : LocalGeometricFontaine.integerRing (InitialThetaCanonicalGeometricFontaine.coefficientField D w))
    (hz : z ≠ 0) : IsUnit (lift D w z) := by
  rw [isUnit_iff, theta_lift]
  exact fun h => hz (Subtype.ext h)

theorem fiber
    (z : LocalGeometricFontaine.integerRing (InitialThetaCanonicalGeometricFontaine.coefficientField D w))
    (a : Ring D w) :
    theta D w a = z ↔ ∃ b : Ring D w, a = primitive D w * b + lift D w z := by
  constructor
  · intro ha
    have hk : a - lift D w z ∈ RingHom.ker (theta D w) := by
      change theta D w (a - lift D w z) = 0
      rw [map_sub, ha, theta_lift, sub_self]
    rw [kernel_eq_span, Ideal.mem_span_singleton] at hk
    obtain ⟨b, hb⟩ := hk
    exact ⟨b, sub_eq_iff_eq_add.mp hb⟩
  · rintro ⟨b, rfl⟩
    rw [map_add, map_mul, theta_primitive, zero_mul, zero_add, theta_lift]

theorem kernel_translate_pow
    (z : LocalGeometricFontaine.integerRing (InitialThetaCanonicalGeometricFontaine.coefficientField D w))
    (b : Ring D w) (n : ℕ) :
    theta D w ((primitive D w * b + lift D w z) ^ n) =
      (z : InitialThetaCanonicalGeometricFontaine.coefficientField D w) ^ n := by
  rw [map_pow, map_add, map_mul, theta_primitive, zero_mul, zero_add, theta_lift]

end
end JoshiTeich.Act1Scene1.InitialThetaDeRhamTeichmuller
