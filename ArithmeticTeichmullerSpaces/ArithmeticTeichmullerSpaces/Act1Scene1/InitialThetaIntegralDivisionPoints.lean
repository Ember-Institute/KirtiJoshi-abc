import ArithmeticTeichmullerSpaces.Act1Scene1.GenuineIntegralDivisionPoints
import ArithmeticTeichmullerSpaces.Act1Scene1.InitialThetaDivisionPoints

/-!
source-id: JT-SCENE1-BOUNDARY-PRODUCER-CONTRACTS-20261021
source: IUT I Definition 3.1(d); Joshi III `ss:theta-data-fixing2`;
`refer/iut/Iut/Anabelian/Genuine/Inertia.lean`, integral division coordinates.
fidelity: the same seed's existing division point has both coordinates integral
over its actual generic x-line. The admissible-level coordinates are elements
of the full division-coordinate normalization ring, with their ambient values.
boundary: Scene1/Derived. The full coordinate field uses the trivial torsion
subgroup; it is not identified with the seed's rank-one quotient field.
Unramified covering, the global cartesian square and the producer remain open.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaGeometrySeed

open WeierstrassCurve JoshiTeich.ReferenceIut JoshiTeich.ReferenceIut.Anabelian
open scoped Classical
universe u
noncomputable section
attribute [local instance 1100] AdmissiblePrimeData.instDecidableEqK
variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}
variable (S : InitialThetaGeometrySeed AG TG)

theorem functionFieldDivisionPoint_coordinates_isIntegral (n : ℕ) (hn : 0 < n) :
    IsIntegral (Algebra.adjoin ↥S.prime.torsionField {Genuine.xG S.prime.EK})
      (ptX (S.functionFieldDivisionPoint n)) ∧
    IsIntegral (Algebra.adjoin ↥S.prime.torsionField {Genuine.xG S.prime.EK})
      (ptY (S.functionFieldDivisionPoint n)) :=
  Genuine.divSys_coordinates_isIntegral S.prime.EK n hn

/-- The admissible-level x coordinate in the actual full division normalization. -/
def fullDivisionNormalizationX : Genuine.coverCoordinateRing S.prime.EK S.prime.ℓ ⊥ false :=
  Genuine.divisionNormalizationX S.prime.EK S.prime.ℓ

/-- The admissible-level y coordinate in the same normalization. -/
def fullDivisionNormalizationY : Genuine.coverCoordinateRing S.prime.EK S.prime.ℓ ⊥ false :=
  Genuine.divisionNormalizationY S.prime.EK S.prime.ℓ

@[simp] theorem coe_fullDivisionNormalizationX :
    ((S.fullDivisionNormalizationX : Genuine.normalizationField S.prime.EK S.prime.ℓ ⊥ false) :
      S.functionFieldClosure) = ptX (S.functionFieldDivisionPoint S.prime.ℓ) := by
  rw [fullDivisionNormalizationX, Genuine.coe_divisionNormalizationX,
    Genuine.Qpt_eq_divSys S.prime.EK S.prime.ℓ_prime.pos]
  rfl

@[simp] theorem coe_fullDivisionNormalizationY :
    ((S.fullDivisionNormalizationY : Genuine.normalizationField S.prime.EK S.prime.ℓ ⊥ false) :
      S.functionFieldClosure) = ptY (S.functionFieldDivisionPoint S.prime.ℓ) := by
  rw [fullDivisionNormalizationY, Genuine.coe_divisionNormalizationY,
    Genuine.Qpt_eq_divSys S.prime.EK S.prime.ℓ_prime.pos]
  rfl

end
end JoshiTeich.Act1Scene1.InitialThetaGeometrySeed
