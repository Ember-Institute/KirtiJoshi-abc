import ArithmeticTeichmullerSpaces.Act1Scene1.LocalKummerRootTower
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaPaperLogWitnessHull
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
source-id: JT-SCENE1-INITIAL-THETA-PRINCIPAL-UNIT-KUMMER
source: Joshi III compatible roots of the actual principal unit (3190--3208).
fidelity: constructs the compatible root tower and algebraic Kummer cocycle
of the actual p*-principal unit at every full-support torsion place. The
closure is that of the local completion, not the global field. This does
not construct continuous cohomology, H^1_e, period rings or BK comparison.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.PrincipalUnitKummer
open JoshiTeich.Prologue
universe u
noncomputable section
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)

abbrev localField (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :=
  s.1.maximalIdeal.adicCompletion ↥D.prime.torsionField

abbrev closure (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :=
  AlgebraicClosure (localField D s)

theorem principalUnit_ne_zero (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    PaperLogWitnessHull.principalUnit D s ≠ 0 := by
  intro h
  have hn := PaperLogWitnessHull.principalUnit_norm_sub_one_lt_one D s
  simpa only [h, zero_sub, norm_neg, norm_one, lt_self_iff_false] using hn

def rootTower (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    LocalKummer.RootTower (Ω := closure D s) (Arithmetic.residueChar s.1)
      (PaperLogWitnessHull.principalUnit D s) :=
  LocalKummer.rootTower _ (Arithmetic.residueChar_prime s.1).pos _

theorem rootTower_pow_eq (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) (n : ℕ) :
    (rootTower D s).root n ^ (Arithmetic.residueChar s.1 ^ n) =
      algebraMap (localField D s) (closure D s) (PaperLogWitnessHull.principalUnit D s) :=
  (rootTower D s).root_pow_eq n

def cocycle (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    (closure D s ≃ₐ[localField D s] closure D s) →
      LocalKummer.cyclotomicTateGroup (Arithmetic.residueChar s.1) (closure D s) :=
  (rootTower D s).kummerCocycle (Arithmetic.residueChar_prime s.1).pos (principalUnit_ne_zero D s)

theorem cocycle_apply (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset)
    (σ : closure D s ≃ₐ[localField D s] closure D s) (n : ℕ) :
    ((cocycle D s σ).1 n : closure D s) = σ ((rootTower D s).root n) / (rootTower D s).root n := rfl

theorem isMulCocycle (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    groupCohomology.IsMulCocycle₁ (cocycle D s) :=
  (rootTower D s).isMulCocycle_kummerCocycle _ _

end
end JoshiTeich.Act1Scene1.PrincipalUnitKummer
