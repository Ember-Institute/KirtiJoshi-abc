import Lean.LibrarySuggestions.Basic
import ArithmeticTeichmullerSpaces.Act1Scene1.GenuineSignedEtale
import ArithmeticTeichmullerSpaces.Act1Scene1.InitialThetaSignedGeometricPoints

/-!
source-id: JT-SCENE1-BOUNDARY-PRODUCER-CONTRACTS-20261021
source: IUT I Definition 3.1(d); Joshi III `ss:theta-data-fixing2`;
Mathlib's ramification/unramified criterion and flat etale criterion.
fidelity: for this seed's actual normalization inclusion, multiplicity one,
a trivial geometric stabilizer and local etaleness coincide. The corresponding
free locus is open, and free points have actual etale localization neighborhoods.
boundary: Scene1/Derived. The orbicurve realization and its etale covering
comparison, cartesianness, core and theta-root laws remain open.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaGeometrySeed

open WeierstrassCurve JoshiTeich.ReferenceIut JoshiTeich.ReferenceIut.Anabelian
open scoped Classical
universe u
noncomputable section

attribute [local instance 1100] AdmissiblePrimeData.instDecidableEqK
attribute [local instance] signedCoverNormalizationAlgebra signedCoverNormalizationGaloisAction
  coverNormalizationPointAction
variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}
variable (S : InitialThetaGeometrySeed AG TG)

theorem signedCoverNormalization_multiplicity_one_iff_etaleAt
    (p : Ideal (S.coverNormalizationRing true)) [p.IsPrime]
    (P : Ideal (S.coverNormalizationRing false)) [P.IsPrime] [P.LiesOver p] :
    S.signedCoverRamificationMultiplicity p = 1 ↔
      Algebra.IsEtaleAt (S.coverNormalizationRing true) P :=
  Genuine.normalization_multiplicity_one_iff_etaleAt S.prime.EK S.prime.ℓ S.prime.M p P

theorem coverNormalizationGeometricPoint_trivial_iff_etaleAt
    (p : Ideal (S.coverNormalizationRing true)) [p.IsPrime]
    (P : Ideal (S.coverNormalizationRing false)) [P.IsPrime] [P.LiesOver p] :
    MulAction.stabilizer S.signedCoverQuotientGroup (S.coverNormalizationGeometricPoint P) = ⊥ ↔
      Algebra.IsEtaleAt (S.coverNormalizationRing true) P :=
  Genuine.normalizationGeometricPoint_trivial_iff_etaleAt S.prime.EK S.prime.ℓ S.prime.M p P

@[instance_reducible] def coverNormalizationAwayAlgebra (f : S.coverNormalizationRing false) :
    Algebra (S.coverNormalizationRing true) (Localization.Away f) :=
  Genuine.normalizationAwayAlgebra S.prime.EK S.prime.ℓ S.prime.M f

attribute [local instance] coverNormalizationAwayAlgebra

theorem coverNormalizationGeometricPoint_exists_etaleNeighborhood
    (p : Ideal (S.coverNormalizationRing true)) [p.IsPrime]
    (P : Ideal (S.coverNormalizationRing false)) [P.IsPrime] [P.LiesOver p]
    (h : MulAction.stabilizer S.signedCoverQuotientGroup
      (S.coverNormalizationGeometricPoint P) = ⊥) :
    ∃ f ∉ P, Algebra.Etale (S.coverNormalizationRing true) (Localization.Away f) :=
  Genuine.normalizationGeometricPoint_exists_etaleNeighborhood S.prime.EK S.prime.ℓ S.prime.M p P h

/-- An actual etale neighborhood generator for this seed's free geometric point. -/
def coverNormalizationEtaleNeighborhood
    (p : Ideal (S.coverNormalizationRing true)) [p.IsPrime]
    (P : Ideal (S.coverNormalizationRing false)) [P.IsPrime] [P.LiesOver p]
    (h : MulAction.stabilizer S.signedCoverQuotientGroup
      (S.coverNormalizationGeometricPoint P) = ⊥) :
    {f : S.coverNormalizationRing false //
      f ∉ P ∧ Algebra.Etale (S.coverNormalizationRing true) (Localization.Away f)} :=
  Genuine.normalizationEtaleNeighborhood S.prime.EK S.prime.ℓ S.prime.M p P h

/-- The open free locus in the actual unsigned normalization spectrum. -/
def coverNormalizationFreeGeometricLocus : Set (PrimeSpectrum (S.coverNormalizationRing false)) :=
  Genuine.normalizationFreeGeometricLocus S.prime.EK S.prime.ℓ S.prime.M

theorem coverNormalizationFreeGeometricLocus_eq_etaleLocus :
    S.coverNormalizationFreeGeometricLocus =
      Algebra.etaleLocus (S.coverNormalizationRing true) (S.coverNormalizationRing false) :=
  Genuine.normalizationFreeGeometricLocus_eq_etaleLocus S.prime.EK S.prime.ℓ S.prime.M

theorem coverNormalizationFreeGeometricLocus_isOpen :
    IsOpen S.coverNormalizationFreeGeometricLocus :=
  Genuine.normalizationFreeGeometricLocus_isOpen S.prime.EK S.prime.ℓ S.prime.M

end
end JoshiTeich.Act1Scene1.InitialThetaGeometrySeed

/- Lean 4.33.1's symbol-frequency exporter stalls on these dependent wrapper
   types. Skip their suggestion index while retaining every declaration and proof. -/
open Lean in
run_cmd do
  for name in ["signedCoverNormalization_multiplicity_one_iff_etaleAt", "coverNormalizationGeometricPoint_trivial_iff_etaleAt", "coverNormalizationGeometricPoint_exists_etaleNeighborhood", "coverNormalizationFreeGeometricLocus_eq_etaleLocus", "coverNormalizationFreeGeometricLocus_isOpen"] do
    modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env name
