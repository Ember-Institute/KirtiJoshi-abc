import ArithmeticTeichmullerSpaces.Act1Scene1.UniformizerLocalization
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaDeRhamDVR

/-!
source-id: JT-SCENE1-INITIAL-THETA-DE-RHAM-FIELD
source: Joshi II primitive kernel and eta_K (838, 932), the inclusions into
B_dR (1069--1076), and Joshi III local Hodge rings; Mathlib BDeRham.
fidelity: retains the original Mathlib BDeRham of the same actual OΩ.
All original kernel generators become associates of the same primitive in
BDeRhamPlus. Their original localization is the localization at that primitive
and the fraction field of the same complete DVR, with an injective natural map.
No field/localization certificate, period norm or theta-locus identity is input.
Original proofs, no reference-engine copy; Prologue-R5 unchanged.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaDeRhamField

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

def completedGenerators : Set (Ring D w) :=
  AdicCompletion.of (sourceKernel D w) (Source D w) ''
    {a | sourceKernel D w = Ideal.span {a}}

def denominators : Submonoid (Ring D w) := Submonoid.closure (completedGenerators D w)

abbrev Carrier := BDeRham
  (LocalGeometricFontaine.integerRing (InitialThetaCanonicalGeometricFontaine.coefficientField D w))
  (Arithmetic.residueChar w.1)

instance commRing : CommRing (Carrier D w) :=
  inferInstanceAs (CommRing (Localization (denominators D w)))

instance algebra : Algebra (Ring D w) (Carrier D w) :=
  inferInstanceAs (Algebra (Ring D w) (Localization (denominators D w)))

instance localization : IsLocalization (denominators D w) (Carrier D w) :=
  inferInstanceAs (IsLocalization (denominators D w) (Localization (denominators D w)))

theorem sourceGenerator_associated (a : Source D w)
    (ha : sourceKernel D w = Ideal.span {a}) :
    Associated (AdicCompletion.of (sourceKernel D w) (Source D w) a : Ring D w) (primitive D w) := by
  apply (Ideal.span_singleton_eq_span_singleton (α := Ring D w)).mp
  have hk : RingHom.ker (theta D w) =
      Ideal.span {(AdicCompletion.of (sourceKernel D w) (Source D w) a : Ring D w)} :=
    AdicResidueEvaluation.kernel_eq_span (sourceKernel D w) (sourceQuotientEquiv D w) a ha
  exact hk.symm.trans (kernel_eq_span D w)

theorem primitive_mem_generators : primitive D w ∈ completedGenerators D w :=
  ⟨sourcePrimitive D w, sourceKernel_eq_span D w, rfl⟩

theorem generator_associated (a : Ring D w) (ha : a ∈ completedGenerators D w) :
    Associated a (primitive D w) := by
  obtain ⟨b, hb, rfl⟩ := ha
  exact sourceGenerator_associated D w b hb

def localizationEquiv : Carrier D w ≃ₐ[Ring D w] Localization.Away (primitive D w) := by
  let : IsLocalization (denominators D w) (Localization.Away (primitive D w)) :=
    UniformizerLocalization.generators_localization (primitive D w) (completedGenerators D w)
      (primitive_mem_generators D w) (generator_associated D w)
  exact IsLocalization.algEquiv (denominators D w) _ _

theorem localizationEquiv_algebraMap (a : Ring D w) :
    localizationEquiv D w (algebraMap (Ring D w) (Carrier D w) a) =
      algebraMap (Ring D w) (Localization.Away (primitive D w)) a :=
  (localizationEquiv D w).commutes a

instance away : IsLocalization.Away (primitive D w) (Carrier D w) :=
  IsLocalization.isLocalization_of_algEquiv (Submonoid.powers (primitive D w))
    (localizationEquiv D w).symm

instance fractionRing : IsFractionRing (Ring D w) (Carrier D w) :=
  UniformizerLocalization.fractionRing (primitive D w) (Carrier D w)
    (InitialThetaDeRhamDVR.primitive_ne_zero D w) (InitialThetaDeRhamDVR.factorization D w)

instance field : Field (Carrier D w) := IsFractionRing.toField (Ring D w)

theorem algebraMap_injective : Function.Injective (algebraMap (Ring D w) (Carrier D w)) :=
  IsFractionRing.injective (Ring D w) (Carrier D w)

theorem primitive_image_ne_zero :
    algebraMap (Ring D w) (Carrier D w) (primitive D w) ≠ 0 := by
  intro h
  exact InitialThetaDeRhamDVR.primitive_ne_zero D w
    (algebraMap_injective D w (h.trans (map_zero _).symm))

theorem primitive_image_isUnit :
    IsUnit (algebraMap (Ring D w) (Carrier D w) (primitive D w)) :=
  IsLocalization.Away.algebraMap_isUnit (primitive D w)

theorem exists_primitive_denominator (x : Carrier D w) :
    ∃ n : ℕ, ∃ a : Ring D w,
      x * algebraMap (Ring D w) (Carrier D w) (primitive D w) ^ n =
        algebraMap (Ring D w) (Carrier D w) a :=
  IsLocalization.Away.surj (primitive D w) x

def fractionEquiv : FractionRing (Ring D w) ≃ₐ[Ring D w] Carrier D w :=
  IsLocalization.algEquiv (nonZeroDivisors (Ring D w)) _ _

theorem fractionEquiv_algebraMap (a : Ring D w) :
    fractionEquiv D w (algebraMap (Ring D w) (FractionRing (Ring D w)) a) =
      algebraMap (Ring D w) (Carrier D w) a :=
  (fractionEquiv D w).commutes a

end
end JoshiTeich.Act1Scene1.InitialThetaDeRhamField
