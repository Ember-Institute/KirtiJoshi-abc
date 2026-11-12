import ArithmeticTeichmullerSpaces.Act1Scene1.GenuineSignedGeometricPoints
import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.Smooth.Fiber

/-!
source-id: JT-SCENE1-BOUNDARY-PRODUCER-CONTRACTS-20261021
source: IUT I Definition 3.1(d); Joshi III `ss:theta-data-fixing2`;
Mathlib `Ideal.ramificationIdx_eq_one_iff`,
`Algebra.IsEtaleAt.of_isUnramifiedAt_of_flat`, and the etale locus.
fidelity: for the actual signed normalization inclusion, multiplicity one,
local etaleness and a trivial geometric point stabilizer are equivalent.
The free geometric locus is open and each free point has an etale basic-open
neighborhood. Finiteness, flatness and residue separability are proved inputs.
boundary: Scene1/Derived. This concerns the ordinary normalization cover.
Orbicurve realization and the orbicurve etale covering comparison remain open.
-/

namespace JoshiTeich.ReferenceIut.Anabelian.Genuine

open WeierstrassCurve JoshiTeich.Act1Scene1
open scoped Classical
universe u
noncomputable section
variable {k : Type u} [Field k] [CharZero k] (E : WeierstrassCurve k) [E.IsElliptic]

attribute [local instance] normalizationUnsignedNormal signedNormalizationAlgebra
  normSMul normModule normFinite normIntegral normFlat normSeparableResidues
  signedNormalizationGaloisAction normalizationPointAction

private theorem finitePresentation_of_moduleFinite {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [IsNoetherianRing R] [Module.Finite R S] :
    Algebra.FinitePresentation R S :=
  Algebra.FinitePresentation.of_finiteType.mp inferInstance

local instance etaleNormPresentation (ell : ℕ) (M : AddSubgroup E.toAffine.Point) :
    Algebra.FinitePresentation (coverCoordinateRing E ell M true)
      (coverCoordinateRing E ell M false) := finitePresentation_of_moduleFinite

private theorem unramified_iff_etale_of_flat {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.FinitePresentation R S] [Module.Flat R S]
    (P : Ideal S) [P.IsPrime] :
    Algebra.IsUnramifiedAt R P ↔ Algebra.IsEtaleAt R P := by
  constructor
  · intro h
    let := h
    exact Algebra.IsEtaleAt.of_isUnramifiedAt_of_flat P
  · intro h
    let := h
    infer_instance

/-- Multiplicity one is exactly local etaleness for the actual ring inclusion. -/
theorem normalization_multiplicity_one_iff_etaleAt (ell : ℕ)
    (M : AddSubgroup E.toAffine.Point)
    (p : Ideal (coverCoordinateRing E ell M true)) [p.IsPrime]
    (P : Ideal (coverCoordinateRing E ell M false)) [P.IsPrime] [P.LiesOver p] :
    FunctionFieldNormalization.ramificationMultiplicity
      (normalizationField_signed_le_unsigned E ell M) p = 1 ↔
        Algebra.IsEtaleAt (coverCoordinateRing E ell M true) P := by
  haveI : PerfectField (P.under (coverCoordinateRing E ell M true)).ResidueField :=
    normSeparableResidues E ell M (P.under (coverCoordinateRing E ell M true))
  exact ((Iff.of_eq (congrArg (fun n : ℕ => n = 1)
    (signedNormalizationMultiplicity_eq_ramificationIdx E ell M p P))).trans
      Ideal.ramificationIdx_eq_one_iff).trans (unramified_iff_etale_of_flat P)

/-- Geometric stabilizers are trivial exactly at the etale points of the cover. -/
theorem normalizationGeometricPoint_trivial_iff_etaleAt (ell : ℕ)
    (M : AddSubgroup E.toAffine.Point)
    (p : Ideal (coverCoordinateRing E ell M true)) [p.IsPrime]
    (P : Ideal (coverCoordinateRing E ell M false)) [P.IsPrime] [P.LiesOver p] :
    MulAction.stabilizer (signedGaloisGroup E ell M)
      (normalizationGeometricPoint E ell M P) = ⊥ ↔
        Algebra.IsEtaleAt (coverCoordinateRing E ell M true) P :=
  ((Subgroup.eq_bot_iff_card _).trans
    (Iff.of_eq (congrArg (fun n : ℕ => n = 1)
      (normalizationGeometricPoint_stabilizer_card E ell M p P)))).trans
        (normalization_multiplicity_one_iff_etaleAt E ell M p P)

@[instance_reducible] private def etaleAwayAlgebra {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] (f : S) : Algebra R (Localization.Away f) := inferInstance

/-- The standard localization algebra for the same signed normalization inclusion. -/
@[instance_reducible] def normalizationAwayAlgebra (ell : ℕ)
    (M : AddSubgroup E.toAffine.Point) (f : coverCoordinateRing E ell M false) :
    Algebra (coverCoordinateRing E ell M true) (Localization.Away f) :=
  etaleAwayAlgebra f

attribute [local instance] normalizationAwayAlgebra

/-- A free geometric point has a concrete etale localization neighborhood. -/
theorem normalizationGeometricPoint_exists_etaleNeighborhood (ell : ℕ)
    (M : AddSubgroup E.toAffine.Point)
    (p : Ideal (coverCoordinateRing E ell M true)) [p.IsPrime]
    (P : Ideal (coverCoordinateRing E ell M false)) [P.IsPrime] [P.LiesOver p]
    (h : MulAction.stabilizer (signedGaloisGroup E ell M)
      (normalizationGeometricPoint E ell M P) = ⊥) :
    ∃ f ∉ P, Algebra.Etale (coverCoordinateRing E ell M true) (Localization.Away f) := by
  have : Algebra.IsEtaleAt (coverCoordinateRing E ell M true) P :=
    (normalizationGeometricPoint_trivial_iff_etaleAt E ell M p P).mp h
  exact Algebra.exists_etale_of_isEtaleAt (R := coverCoordinateRing E ell M true) P

/-- A neighborhood generator and its proved etale law, as actual data. -/
def normalizationEtaleNeighborhood (ell : ℕ) (M : AddSubgroup E.toAffine.Point)
    (p : Ideal (coverCoordinateRing E ell M true)) [p.IsPrime]
    (P : Ideal (coverCoordinateRing E ell M false)) [P.IsPrime] [P.LiesOver p]
    (h : MulAction.stabilizer (signedGaloisGroup E ell M)
      (normalizationGeometricPoint E ell M P) = ⊥) :
    {f : coverCoordinateRing E ell M false //
      f ∉ P ∧ Algebra.Etale (coverCoordinateRing E ell M true) (Localization.Away f)} :=
  ⟨(normalizationGeometricPoint_exists_etaleNeighborhood E ell M p P h).choose,
    (normalizationGeometricPoint_exists_etaleNeighborhood E ell M p P h).choose_spec⟩

/-- The free geometric locus is a subset of the actual unsigned prime spectrum. -/
def normalizationFreeGeometricLocus (ell : ℕ) (M : AddSubgroup E.toAffine.Point) :
    Set (PrimeSpectrum (coverCoordinateRing E ell M false)) :=
  {x | MulAction.stabilizer (signedGaloisGroup E ell M)
    (normalizationGeometricPoint E ell M x.asIdeal) = ⊥}

theorem normalizationFreeGeometricLocus_eq_etaleLocus (ell : ℕ)
    (M : AddSubgroup E.toAffine.Point) :
    normalizationFreeGeometricLocus E ell M =
      Algebra.etaleLocus (coverCoordinateRing E ell M true) (coverCoordinateRing E ell M false) := by
  ext x
  exact normalizationGeometricPoint_trivial_iff_etaleAt E ell M
    (x.asIdeal.under (coverCoordinateRing E ell M true)) x.asIdeal

theorem normalizationFreeGeometricLocus_isOpen (ell : ℕ)
    (M : AddSubgroup E.toAffine.Point) :
    IsOpen (normalizationFreeGeometricLocus E ell M) := by
  rw [normalizationFreeGeometricLocus_eq_etaleLocus]
  exact Algebra.isOpen_etaleLocus

end
end JoshiTeich.ReferenceIut.Anabelian.Genuine
