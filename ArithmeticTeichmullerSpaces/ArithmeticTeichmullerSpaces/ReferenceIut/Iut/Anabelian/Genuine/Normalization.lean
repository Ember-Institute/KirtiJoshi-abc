import ArithmeticTeichmullerSpaces.Act1Scene1.FunctionFieldNormalization
import ArithmeticTeichmullerSpaces.ReferenceIut.Iut.Anabelian.Genuine.DivisionFields

/-!
source-id: JT-SCENE1-BOUNDARY-PRODUCER-CONTRACTS-20261021
source: IUT I Definition 3.1(d); Joshi III `ss:theta-data-fixing2`;
`refer/iut/Iut/Anabelian/Genuine/Realize.lean`, normalization in the finite fixed fields.
fidelity: constructs the actual integral closures of k[xG] in the already proved
fixed fields. The base-field change uses the proved baseField=xLine identity and
preserves the underlying ambient field. Finite, Dedekind, fraction-field and
non-field laws are proved, not fields of an interface.
boundary: Scene1/Derived. Etaleness, orbifold multiplicity, core and theta-root
identities remain open.
-/

namespace JoshiTeich.ReferenceIut.Anabelian.Genuine

open WeierstrassCurve
open scoped IntermediateField.algebraAdjoinAdjoin Classical
open JoshiTeich.Act1Scene1

universe u
noncomputable section
variable {k : Type u} [Field k] [CharZero k] (E : WeierstrassCurve k) [E.IsElliptic]

/-- The same actual fixed field, with the x-line as its named coefficient field. -/
def normalizationField (ℓ : ℕ) (M : AddSubgroup E.toAffine.Point) (pm : Bool) :
    IntermediateField (xLine E) (Ω E) :=
  FunctionFieldNormalization.rebaseField (baseField_eq_xLine E) (stabilizerField E ℓ M pm)

lemma mem_normalizationField (ℓ : ℕ) (M : AddSubgroup E.toAffine.Point) (pm : Bool) (x : Ω E) :
    x ∈ normalizationField E ℓ M pm ↔ x ∈ stabilizerField E ℓ M pm := Iff.rfl

instance finiteDimensional_normalizationField (ℓ : ℕ) (M : AddSubgroup E.toAffine.Point) (pm : Bool) :
    FiniteDimensional (xLine E) (normalizationField E ℓ M pm) :=
  FunctionFieldNormalization.finiteDimensional_rebaseField
    (baseField_eq_xLine E) (stabilizerField E ℓ M pm)

instance separable_normalizationField (ℓ : ℕ) (M : AddSubgroup E.toAffine.Point) (pm : Bool) :
    Algebra.IsSeparable (xLine E) (normalizationField E ℓ M pm) := by
  have : CharZero (xLine E) := charZero_of_injective_algebraMap (algebraMap k (xLine E)).injective
  exact Algebra.IsAlgebraic.isSeparable_of_perfectField

abbrev coverCoordinateRing (ℓ : ℕ) (M : AddSubgroup E.toAffine.Point) (pm : Bool) :=
  FunctionFieldNormalization.coordRing (xG E) (normalizationField E ℓ M pm)

instance dedekind_coverCoordinateRing (ℓ : ℕ) (M : AddSubgroup E.toAffine.Point) (pm : Bool) :
    IsDedekindDomain (coverCoordinateRing E ℓ M pm) :=
  FunctionFieldNormalization.dedekindRing (xG E) (transcendental_xG E) _

instance finite_coverCoordinateRing (ℓ : ℕ) (M : AddSubgroup E.toAffine.Point) (pm : Bool) :
    Module.Finite (FunctionFieldNormalization.polynomialBase k (xG E))
      (coverCoordinateRing E ℓ M pm) :=
  FunctionFieldNormalization.finiteRing (xG E) (transcendental_xG E) _

instance fractionField_coverCoordinateRing (ℓ : ℕ) (M : AddSubgroup E.toAffine.Point) (pm : Bool) :
    IsFractionRing (coverCoordinateRing E ℓ M pm) (normalizationField E ℓ M pm) :=
  FunctionFieldNormalization.fractionFieldRing (xG E) _

instance finiteType_coverCoordinateRing (ℓ : ℕ) (M : AddSubgroup E.toAffine.Point) (pm : Bool) :
    Algebra.FiniteType k (coverCoordinateRing E ℓ M pm) :=
  FunctionFieldNormalization.finiteTypeRing (xG E) (transcendental_xG E) _

lemma notField_coverCoordinateRing (ℓ : ℕ) (M : AddSubgroup E.toAffine.Point) (pm : Bool) :
    ¬ IsField (coverCoordinateRing E ℓ M pm) :=
  FunctionFieldNormalization.notFieldRing (xG E) (transcendental_xG E) _

lemma normalizationField_signed_le_unsigned (ℓ : ℕ) (M : AddSubgroup E.toAffine.Point) :
    normalizationField E ℓ M true ≤ normalizationField E ℓ M false :=
  FunctionFieldNormalization.rebaseField_mono (baseField_eq_xLine E)
    (stabilizerField_signed_le_unsigned E ℓ M)

/-- The actual inclusion on normalization rings, preserving the same ambient values. -/
def signedNormalizationRingMap (ℓ : ℕ) (M : AddSubgroup E.toAffine.Point) :
    coverCoordinateRing E ℓ M true →ₐ[k] coverCoordinateRing E ℓ M false :=
  FunctionFieldNormalization.ringMap (normalizationField_signed_le_unsigned E ℓ M)

lemma signedNormalizationRingMap_injective (ℓ : ℕ) (M : AddSubgroup E.toAffine.Point) :
    Function.Injective (signedNormalizationRingMap E ℓ M) :=
  FunctionFieldNormalization.ringMap_injective _

lemma signedNormalizationRingMap_isIntegral (ℓ : ℕ) (M : AddSubgroup E.toAffine.Point) :
    (signedNormalizationRingMap E ℓ M).toRingHom.IsIntegral :=
  FunctionFieldNormalization.ringMap_isIntegral _

end
end JoshiTeich.ReferenceIut.Anabelian.Genuine
