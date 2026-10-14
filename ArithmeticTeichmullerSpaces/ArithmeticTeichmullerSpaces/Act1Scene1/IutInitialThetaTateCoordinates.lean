import ArithmeticTeichmullerSpaces.Act1Scene1.LocalKummerTateBasis
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaPadicKummer

/-!
source-id: JT-SCENE1-INITIAL-THETA-TATE-COORDINATES
source: Joshi III local Z_p(1)-valued Kummer class (3190--3208).
fidelity: supplies an actual topological Z_p basis at each local closure.
It gives continuous coordinates of the existing principal-unit cocycle and
proves reconstruction. These are coordinates, not a BK logarithm.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.PrincipalUnitKummer
open JoshiTeich.Prologue
open scoped Topology
universe u
noncomputable section
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)

local instance tateCoordinateResiduePrime
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    Fact (Arithmetic.residueChar s.1).Prime := ⟨Arithmetic.residueChar_prime s.1⟩

local instance tateCoordinateLocalCharZero
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    CharZero (localField D s) :=
  charZero_of_injective_ringHom (NumberField.FinitePlace.embedding s.1.maximalIdeal).injective

def tateBasis (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    ℤ_[Arithmetic.residueChar s.1] ≃L[ℤ_[Arithmetic.residueChar s.1]]
      Additive (LocalKummer.cyclotomicTateGroup (Arithmetic.residueChar s.1) (closure D s)) :=
  LocalKummer.TateBasis.equiv

def cocycleCoordinate (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    C((closure D s ≃ₐ[localField D s] closure D s), ℤ_[Arithmetic.residueChar s.1]) :=
  ⟨fun σ => (tateBasis D s).symm (Additive.ofMul (cocycle D s σ)),
    (tateBasis D s).symm.continuous.comp (continuous_ofMul.comp (continuous_cocycle D s))⟩

theorem cocycleCoordinate_reconstruct
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset)
    (σ : closure D s ≃ₐ[localField D s] closure D s) :
    tateBasis D s (cocycleCoordinate D s σ) = Additive.ofMul (cocycle D s σ) :=
  (tateBasis D s).apply_symm_apply _

end
end JoshiTeich.Act1Scene1.PrincipalUnitKummer
