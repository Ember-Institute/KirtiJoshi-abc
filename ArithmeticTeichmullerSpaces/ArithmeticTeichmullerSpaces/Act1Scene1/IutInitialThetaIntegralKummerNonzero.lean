import ArithmeticTeichmullerSpaces.Act1Scene1.LocalPadicKummerNonvanishing
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaKummerRootDescent
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaPrincipalUnitLogLaws

/-!
source-id: JT-SCENE1-INITIAL-THETA-INTEGRAL-KUMMER-NONZERO
source: the actual principal-unit Kummer class in Joshi III (3190--3208).
fidelity: nonzero ordinary log and discrete local-field norms exclude some
finite p-power root and hence a base-field compatible tower. The actual
standard integral Kummer class is nonzero. Rational nonvanishing and H^1_e/BK
comparison remain separate obligations.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.PrincipalUnitKummer
open JoshiTeich.Prologue
open scoped Valued
universe u
noncomputable section
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)

local instance integralNonzeroResiduePrime
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    Fact (Arithmetic.residueChar s.1).Prime := ⟨Arithmetic.residueChar_prime s.1⟩

local instance integralNonzeroCharZero
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    CharZero (localField D s) :=
  charZero_of_injective_ringHom (NumberField.FinitePlace.embedding s.1.maximalIdeal).injective

theorem exists_no_local_prime_power_root
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    ∃ n : ℕ, ¬ ∃ b : localField D s,
      b ^ (Arithmetic.residueChar s.1 ^ n) = PaperLogWitnessHull.principalUnit D s :=
  LocalPadicLog.exists_no_prime_power_root_of_log_ne_zero (Arithmetic.residueChar_prime s.1)
    (InitialThetaLogWitness.norm_residueChar_lt_one s.1)
    (PaperLogWitnessHull.principalUnit_norm_sub_one_lt_one D s) (log_principalUnit_ne_zero D s)

theorem no_local_baseRootTower
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    ¬ Nonempty (LocalKummer.RootTower (K := localField D s) (Ω := localField D s)
      (Arithmetic.residueChar s.1) (PaperLogWitnessHull.principalUnit D s)) := by
  obtain ⟨n, hn⟩ := exists_no_local_prime_power_root D s
  rintro ⟨S⟩
  exact hn ⟨S.root n, by simpa only [Algebra.algebraMap_self_apply] using S.root_pow_eq n⟩

theorem padicClass_ne_zero
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) : padicClass D s ≠ 0 := by
  obtain ⟨n, hn⟩ := exists_no_local_prime_power_root D s
  exact padicClass_ne_zero_of_no_local_root D s n hn

end
end JoshiTeich.Act1Scene1.PrincipalUnitKummer
