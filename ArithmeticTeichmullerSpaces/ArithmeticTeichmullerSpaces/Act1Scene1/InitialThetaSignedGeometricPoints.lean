import ArithmeticTeichmullerSpaces.Act1Scene1.GenuineSignedGeometricPoints
import ArithmeticTeichmullerSpaces.Act1Scene1.InitialThetaSignedNormalizationGalois
import Lean.LibrarySuggestions.Basic

/-!
source-id: JT-SCENE1-BOUNDARY-PRODUCER-CONTRACTS-20261021
source: IUT I Definition 3.1(d); Joshi III `ss:theta-data-fixing2`;
residue-field geometric points and the proved normalization inertia formula.
fidelity: constructs actual residue-closure points and their Spec morphisms for
the same seed. The geometric point stabilizer is inertia and its order is the
existing signed ramification multiplicity. The action fixes the signed restriction.
boundary: Scene1/Derived. This does not provide orbicurve realization, etale
covering comparison, cartesianness, core or theta-root laws.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaGeometrySeed

open CategoryTheory
open WeierstrassCurve JoshiTeich.ReferenceIut JoshiTeich.ReferenceIut.Anabelian
open scoped Classical
universe u
noncomputable section

attribute [local instance 1100] AdmissiblePrimeData.instDecidableEqK
attribute [local instance] signedCoverNormalizationAlgebra signedCoverNormalizationGaloisAction
variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}
variable (S : InitialThetaGeometrySeed AG TG)

@[instance_reducible] def coverNormalizationPointAction (C : Type u) [CommRing C] :
    MulAction S.signedCoverQuotientGroup (S.coverNormalizationRing false →+* C) :=
  Genuine.normalizationPointAction S.prime.EK S.prime.ℓ S.prime.M C

attribute [local instance] coverNormalizationPointAction

def coverNormalizationGeometricPoint (P : Ideal (S.coverNormalizationRing false)) [P.IsPrime] :
    S.coverNormalizationRing false →+* AlgebraicClosure P.ResidueField :=
  Genuine.normalizationGeometricPoint S.prime.EK S.prime.ℓ S.prime.M P

theorem coverNormalizationGeometricPoint_ker
    (P : Ideal (S.coverNormalizationRing false)) [P.IsPrime] :
    RingHom.ker (S.coverNormalizationGeometricPoint P) = P :=
  Genuine.normalizationGeometricPoint_ker S.prime.EK S.prime.ℓ S.prime.M P

/-- The actual Spec morphism defined by the residue-closure evaluation. -/
def coverNormalizationGeometricPointMorphism
    (P : Ideal (S.coverNormalizationRing false)) [P.IsPrime] :
    AlgebraicGeometry.Spec (CommRingCat.of (AlgebraicClosure P.ResidueField)) ⟶
      S.coverNormalizationScheme false :=
  AlgebraicGeometry.Spec.map (CommRingCat.ofHom (S.coverNormalizationGeometricPoint P))

theorem coverNormalizationGeometricPoint_stabilizer
    (P : Ideal (S.coverNormalizationRing false)) [P.IsPrime] :
    MulAction.stabilizer S.signedCoverQuotientGroup (S.coverNormalizationGeometricPoint P) =
      P.inertia S.signedCoverQuotientGroup :=
  Genuine.normalizationGeometricPoint_stabilizer S.prime.EK S.prime.ℓ S.prime.M P

theorem coverNormalizationGeometricPoint_stabilizer_card
    (p : Ideal (S.coverNormalizationRing true)) [p.IsPrime]
    (P : Ideal (S.coverNormalizationRing false)) [P.IsPrime] [P.LiesOver p] :
    Nat.card (MulAction.stabilizer S.signedCoverQuotientGroup
      (S.coverNormalizationGeometricPoint P)) = S.signedCoverRamificationMultiplicity p :=
  Genuine.normalizationGeometricPoint_stabilizer_card S.prime.EK S.prime.ℓ S.prime.M p P

theorem coverNormalizationPoint_preserves_signed (C : Type u) [CommRing C]
    (g : S.signedCoverQuotientGroup) (f : S.coverNormalizationRing false →+* C) :
    (GeometricPointInertia.translatePoint S.signedCoverQuotientGroup
      (S.coverNormalizationRing false) C g f).comp (Genuine.normalizationSignedRingHom S.prime.EK S.prime.ℓ S.prime.M) =
        f.comp (Genuine.normalizationSignedRingHom S.prime.EK S.prime.ℓ S.prime.M) :=
  Genuine.normalizationPoint_preserves_signed S.prime.EK S.prime.ℓ S.prime.M C g f

end
end JoshiTeich.Act1Scene1.InitialThetaGeometrySeed

/- Lean 4.33.1's symbol-frequency exporter spends several minutes analysing
   the dependent types of these forwarding theorems. Exclude their names from
   automatic library suggestions; declarations and kernel-checked proofs stay intact. -/
open Lean in
run_cmd do
  for name in ["coverNormalizationGeometricPoint_ker", "coverNormalizationGeometricPoint_stabilizer", "coverNormalizationGeometricPoint_stabilizer_card", "coverNormalizationPoint_preserves_signed"] do
    modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env name
