import ArithmeticTeichmullerSpaces.Act1Scene1.LocalKummerRootDescent
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaKummerZeroCriteria

/-!
source-id: JT-SCENE1-INITIAL-THETA-KUMMER-ROOT-DESCENT
source: the actual principal-unit integral Kummer class, Joshi III (3190--3208).
fidelity: class zero is equivalent to a compatible p-power root tower in
the actual local field. It implies a root at every finite level; a missing
root proves class nonzero. No actual missing-root witness is supplied here.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.PrincipalUnitKummer
open JoshiTeich.Prologue
universe u
noncomputable section
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)

local instance rootDescentResiduePrime
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    Fact (Arithmetic.residueChar s.1).Prime := ⟨Arithmetic.residueChar_prime s.1⟩

local instance rootDescentCharZero
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    CharZero (localField D s) :=
  charZero_of_injective_ringHom (NumberField.FinitePlace.embedding s.1.maximalIdeal).injective

theorem padicClass_eq_zero_iff_baseRootTower
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    padicClass D s = 0 ↔
      Nonempty (LocalKummer.RootTower (K := localField D s) (Ω := localField D s)
        (Arithmetic.residueChar s.1) (PaperLogWitnessHull.principalUnit D s)) :=
  (rootTower D s).padicClass_eq_zero_iff_baseTower (principalUnit_ne_zero D s)

theorem exists_local_root_of_padicClass_eq_zero
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset)
    (h : padicClass D s = 0) (n : ℕ) :
    ∃ b : localField D s, b ^ (Arithmetic.residueChar s.1 ^ n) = PaperLogWitnessHull.principalUnit D s :=
  (rootTower D s).exists_root_of_padicClass_eq_zero (principalUnit_ne_zero D s) h n

theorem padicClass_ne_zero_of_no_local_root
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) (n : ℕ)
    (h : ¬ ∃ b : localField D s,
      b ^ (Arithmetic.residueChar s.1 ^ n) = PaperLogWitnessHull.principalUnit D s) :
    padicClass D s ≠ 0 :=
  (rootTower D s).padicClass_ne_zero_of_no_root (principalUnit_ne_zero D s) n h

end
end JoshiTeich.Act1Scene1.PrincipalUnitKummer
