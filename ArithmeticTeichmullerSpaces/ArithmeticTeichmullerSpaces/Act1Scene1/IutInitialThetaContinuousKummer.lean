import ArithmeticTeichmullerSpaces.Act1Scene1.LocalKummerContinuity
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaPrincipalUnitKummer

/-!
source-id: JT-SCENE1-INITIAL-THETA-CONTINUOUS-KUMMER
source: Joshi III principal-unit compatible roots and Kummer class (3190--3208).
fidelity: proves the actual p*-principal-unit Kummer cocycle continuous for
the Krull/inverse-limit topologies and constructs its continuous-map value.
The continuous cocycle still needs a continuous cohomology class and proof
of crystalline H^1_e membership and BK logarithm comparison.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.PrincipalUnitKummer
open JoshiTeich.Prologue
universe u
noncomputable section
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)

theorem cocycle_level_isLocallyConstant
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) (n : ℕ) :
    IsLocallyConstant (fun σ : closure D s ≃ₐ[localField D s] closure D s =>
      (cocycle D s σ).1 n) :=
  (rootTower D s).kummerCocycle_level_isLocallyConstant _ _ n

theorem continuous_cocycle (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    Continuous (cocycle D s) :=
  (rootTower D s).continuous_kummerCocycle _ _

def continuousCocycle (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    C((closure D s ≃ₐ[localField D s] closure D s),
      LocalKummer.cyclotomicTateGroup (Arithmetic.residueChar s.1) (closure D s)) :=
  ⟨cocycle D s, continuous_cocycle D s⟩

theorem continuousCocycle_isMulCocycle
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    groupCohomology.IsMulCocycle₁ (continuousCocycle D s) := isMulCocycle D s

end
end JoshiTeich.Act1Scene1.PrincipalUnitKummer
