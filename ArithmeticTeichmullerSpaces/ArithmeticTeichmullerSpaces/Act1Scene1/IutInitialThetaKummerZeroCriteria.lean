import ArithmeticTeichmullerSpaces.Act1Scene1.LocalKummerH1Equivalence
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaRationalKummer

/-!
source-id: JT-SCENE1-INITIAL-THETA-KUMMER-ZERO-CRITERIA
source: actual principal-unit Kummer classes before the H^1_e/BK comparison.
fidelity: zero of the actual integral or rational standard class is equivalent
to a pointwise coboundary equation. No class nonvanishing or H^1_e identity
is assumed or inferred from the nonvanishing of an ordinary logarithm.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.PrincipalUnitKummer
open JoshiTeich.Prologue
universe u
noncomputable section
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)

local instance kummerZeroResiduePrime
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    Fact (Arithmetic.residueChar s.1).Prime := ⟨Arithmetic.residueChar_prime s.1⟩

local instance kummerZeroCharZero
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    CharZero (localField D s) :=
  charZero_of_injective_ringHom (NumberField.FinitePlace.embedding s.1.maximalIdeal).injective

theorem padicClass_eq_zero_iff
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    padicClass D s = 0 ↔
      ∃ t : LocalKummer.cyclotomicTateGroup (Arithmetic.residueChar s.1) (closure D s),
        ∀ σ : closure D s ≃ₐ[localField D s] closure D s, cocycle D s σ = σ • t / t :=
  LocalKummer.padicClassOfCocycle_eq_zero_iff (Arithmetic.residueChar s.1) (continuousCocycleValue D s)

theorem rationalClass_eq_zero_iff
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    rationalClass D s = 0 ↔
      ∃ t : LocalKummer.Rational.topRep (K := localField D s) (Ω := closure D s)
          (Arithmetic.residueChar s.1),
        ∀ σ : closure D s ≃ₐ[localField D s] closure D s,
          rationalCocycle D s σ =
            (LocalKummer.Rational.topRep (K := localField D s) (Ω := closure D s)
              (Arithmetic.residueChar s.1)).ρ σ t - t :=
  ContinuousH1Recognition.classOf_eq_zero_iff _ (rationalCocycle D s)
    (LocalKummer.Rational.cocycle_law (Arithmetic.residueChar s.1) (continuousCocycleValue D s))

end
end JoshiTeich.Act1Scene1.PrincipalUnitKummer
