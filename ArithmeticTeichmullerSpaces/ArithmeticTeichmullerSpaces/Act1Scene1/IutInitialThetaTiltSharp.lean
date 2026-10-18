import ArithmeticTeichmullerSpaces.Act1Scene1.GeometricTiltSharp
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaTiltField

/-!
source-id: JT-SCENE1-INITIAL-THETA-TILT-SHARP
source: Joshi arithmetic holomorphic untilt data, the actual coefficient
field/tilt producers, and Mathlib Fontaine theta on Teichmuller elements.
fidelity: constructs sharp on the same actual tilt carrier, proves its norm
identity and surjectivity, relates it to the same canonical untilt/theta,
and derives the valuation range and a nontrivial contracting tilt element.
No sharp, norm or surjectivity certificate is input. Tilt completeness and
paper holomorphoid identification remain open. Original proofs; R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaTiltSharp

open JoshiTeich.Prologue
open scoped NNReal
universe u
noncomputable section
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)
local instance selectedPrime : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

def data :
    letI := InitialThetaCanonicalGeometricFontaine.primeNormFact D w
    GeometricTiltSharp.Data (InitialThetaCanonicalGeometricFontaine.coefficientField D w)
      (Arithmetic.residueChar w.1) (InitialThetaTiltField.data D w) := by
  let := InitialThetaCanonicalGeometricFontaine.primeNormFact D w
  exact GeometricTiltSharp.ofField (InitialThetaCanonicalGeometricFontaine.coefficientField D w)
    (Arithmetic.residueChar w.1)

/-- Sharp is defined on the previously constructed tilt field. -/
def sharp : InitialThetaTiltField.Carrier D w →*₀
    InitialThetaCanonicalGeometricFontaine.coefficientField D w := by
  let := InitialThetaCanonicalGeometricFontaine.primeNormFact D w
  exact (data D w).map

theorem sharp_norm (x : InitialThetaTiltField.Carrier D w) :
    ‖sharp D w x‖₊ = InitialThetaTiltField.valuation D w x := by
  let := InitialThetaCanonicalGeometricFontaine.primeNormFact D w
  exact (data D w).norm_map x

theorem sharp_norm_real (x : InitialThetaTiltField.Carrier D w) :
    ‖sharp D w x‖ = (InitialThetaTiltField.valuation D w x : ℝ) :=
  congrArg (fun r : ℝ≥0 => (r : ℝ)) (sharp_norm D w x)

theorem sharp_surjective : Function.Surjective (sharp D w) := by
  let := InitialThetaCanonicalGeometricFontaine.primeNormFact D w
  exact (data D w).surjective

theorem sharp_eq_zero_iff (x : InitialThetaTiltField.Carrier D w) : sharp D w x = 0 ↔ x = 0 := by
  constructor
  · intro h
    apply (InitialThetaTiltField.valuation_eq_zero_iff D w x).mp
    rw [← sharp_norm, h, nnnorm_zero]
  · rintro rfl
    exact map_zero _

theorem sharp_inclusion (x : InitialThetaTiltField.Source D w) :
    letI := InitialThetaCanonicalGeometricFontaine.primeNormFact D w
    sharp D w (InitialThetaTiltField.inclusion D w x) =
      (((InitialThetaCanonicalGeometricFontaine.placeData D w).data.untilt x :
        LocalGeometricFontaine.integerRing
          (InitialThetaCanonicalGeometricFontaine.coefficientField D w)) :
        InitialThetaCanonicalGeometricFontaine.coefficientField D w) := by
  let := InitialThetaCanonicalGeometricFontaine.primeNormFact D w
  exact (data D w).on_integral x

theorem untilt_norm (x : InitialThetaTiltField.Source D w) :
    letI := InitialThetaCanonicalGeometricFontaine.primeNormFact D w
    ‖(((InitialThetaCanonicalGeometricFontaine.placeData D w).data.untilt x :
        LocalGeometricFontaine.integerRing
          (InitialThetaCanonicalGeometricFontaine.coefficientField D w)) :
        InitialThetaCanonicalGeometricFontaine.coefficientField D w)‖₊ =
      InitialThetaTiltField.sourceValuation D w x := by
  let := InitialThetaCanonicalGeometricFontaine.primeNormFact D w
  rw [← sharp_inclusion, sharp_norm, InitialThetaTiltField.valuation_inclusion]

theorem theta_teichmuller_eq_sharp (x : InitialThetaTiltField.Source D w) :
    letI := InitialThetaCanonicalGeometricFontaine.primeNormFact D w
    (((InitialThetaCanonicalGeometricFontaine.placeData D w).data.theta
        (WittVector.teichmuller (Arithmetic.residueChar w.1) x) :
      LocalGeometricFontaine.integerRing
        (InitialThetaCanonicalGeometricFontaine.coefficientField D w)) :
      InitialThetaCanonicalGeometricFontaine.coefficientField D w) =
        sharp D w (InitialThetaTiltField.inclusion D w x) := by
  let := InitialThetaCanonicalGeometricFontaine.primeNormFact D w
  rw [sharp_inclusion]
  exact congrArg (fun z : LocalGeometricFontaine.integerRing
    (InitialThetaCanonicalGeometricFontaine.coefficientField D w) =>
      (z : InitialThetaCanonicalGeometricFontaine.coefficientField D w))
    (Perfectoid.thetaMap_teichmuller (p := Arithmetic.residueChar w.1) x)

theorem theta_teichmuller_norm (x : InitialThetaTiltField.Source D w) :
    letI := InitialThetaCanonicalGeometricFontaine.primeNormFact D w
    ‖(((InitialThetaCanonicalGeometricFontaine.placeData D w).data.theta
        (WittVector.teichmuller (Arithmetic.residueChar w.1) x) :
      LocalGeometricFontaine.integerRing
        (InitialThetaCanonicalGeometricFontaine.coefficientField D w)) :
      InitialThetaCanonicalGeometricFontaine.coefficientField D w)‖₊ =
        InitialThetaTiltField.sourceValuation D w x := by
  let := InitialThetaCanonicalGeometricFontaine.primeNormFact D w
  rw [theta_teichmuller_eq_sharp, sharp_norm, InitialThetaTiltField.valuation_inclusion]

theorem sharp_frobenius (x : InitialThetaTiltField.Carrier D w) :
    sharp D w (frobenius (InitialThetaTiltField.Carrier D w) (Arithmetic.residueChar w.1) x) =
      sharp D w x ^ Arithmetic.residueChar w.1 := by
  rw [frobenius_def, map_pow]

theorem sharp_inverseFrobenius_pow (x : InitialThetaTiltField.Carrier D w) :
    sharp D w ((frobeniusEquiv (InitialThetaTiltField.Carrier D w)
      (Arithmetic.residueChar w.1)).symm x) ^ Arithmetic.residueChar w.1 = sharp D w x := by
  rw [← map_pow]
  exact congrArg (sharp D w) ((frobeniusEquiv (InitialThetaTiltField.Carrier D w)
    (Arithmetic.residueChar w.1)).apply_symm_apply x)

theorem valuation_range : Set.range (InitialThetaTiltField.valuation D w) =
    Set.range (fun x : InitialThetaCanonicalGeometricFontaine.coefficientField D w => ‖x‖₊) := by
  ext r
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨sharp D w x, sharp_norm D w x⟩
  · rintro ⟨y, rfl⟩
    obtain ⟨x, hx⟩ := sharp_surjective D w y
    exact ⟨x, (sharp_norm D w x).symm.trans (congrArg (fun z => ‖z‖₊) hx)⟩

theorem exists_contracting : ∃ x : InitialThetaTiltField.Carrier D w,
    0 < InitialThetaTiltField.valuation D w x ∧ InitialThetaTiltField.valuation D w x < 1 := by
  obtain ⟨x, hx⟩ := sharp_surjective D w
    (Arithmetic.residueChar w.1 : InitialThetaCanonicalGeometricFontaine.coefficientField D w)
  refine ⟨x, ?_⟩
  have hv : InitialThetaTiltField.valuation D w x =
      ‖(Arithmetic.residueChar w.1 : InitialThetaCanonicalGeometricFontaine.coefficientField D w)‖₊ :=
    (sharp_norm D w x).symm.trans (congrArg (fun z => ‖z‖₊) hx)
  rw [hv]
  have hp := (InitialThetaCanonicalGeometricFontaine.primeNormFact D w).out
  constructor
  · exact_mod_cast hp.1
  · exact_mod_cast hp.2

end
end JoshiTeich.Act1Scene1.InitialThetaTiltSharp
