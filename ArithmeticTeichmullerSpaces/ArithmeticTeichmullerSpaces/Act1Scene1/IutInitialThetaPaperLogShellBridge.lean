import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaPaperLogWitnessHull
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalPadicLogHomomorphism

/-!
source-id: JT-SCENE1-PAPER-LOG-WITNESS-LOG-SHELL
source: Joshi III p*-normalized logarithm and log-shell (3226), with the
existing ordinary logarithm image definition.
fidelity: proves that the paper-normalized local logarithm lies in the existing
ordinary log-shell. At odd p the square of the principal unit compensates the
factor between p* = p and the shell normalization 2p; at p = 2 the formulas
coincide. This is a local carrier identity only, not a Bloch--Kato comparison.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.LocalPadicLog
open scoped Valued
universe u
noncomputable section

variable {k : Type u} [Field k]
  [Valued k (WithZero (Multiplicative ℤ))]
  [Valuation.RankOne (Valued.v : Valuation k (WithZero (Multiplicative ℤ)))]
  [CharZero k] [CompleteSpace k]

theorem paperNormalizedLog_mem_logShell {p : ℕ} (hp : p.Prime)
    (hpk : ‖(p : k)‖ < 1) {y : k} (hy : ‖y‖ ≤ 1) :
    paperNormalizedLog p y ∈ logShell p := by
  by_cases hp2 : p = 2
  · subst p
    have hu : ‖paperPrincipalUnit 2 y - 1‖ < 1 :=
      paperPrincipalUnit_norm_sub_one_lt_one hp hpk hy
    refine ⟨paperPrincipalUnit 2 y, hu, ?_⟩
    simp only [paperNormalizedLog, paperPrincipalUnit, paperScale, if_pos,
      normalizedLog]
    field_simp
    ring
  · let u : k := paperPrincipalUnit p y
    have hu : ‖u - 1‖ < 1 :=
      paperPrincipalUnit_norm_sub_one_lt_one hp hpk hy
    have hu2 : ‖u ^ 2 - 1‖ < 1 := by
      rw [show u ^ 2 = u * u by ring]
      exact norm_mul_sub_one_lt hu hu
    refine ⟨u ^ 2, hu2, ?_⟩
    have hlog := padicLog_pow hp hpk hu 2
    simp only [Nat.cast_ofNat, Nat.cast_one, one_mul] at hlog
    have hu_eq : u = 1 + (p : k) * y := by
      simp [u, paperPrincipalUnit, paperScale, hp2]
    unfold paperNormalizedLog u
    simp only [paperPrincipalUnit, paperScale, hp2, if_false]
    have hlog' : padicLog ((1 + (p : k) * y) ^ 2) =
        2 * padicLog (1 + (p : k) * y) := by
      rw [← hu_eq]
      exact hlog
    rw [hlog']
    field_simp [Nat.cast_ne_zero.mpr hp.ne_zero]

end
end JoshiTeich.Act1Scene1.LocalPadicLog

namespace JoshiTeich.Act1Scene1.PaperLogWitnessHull
open JoshiTeich.Prologue
open scoped Valued
universe u
noncomputable section
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)

local instance paperShellCharZero
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    CharZero (s.1.maximalIdeal.adicCompletion ↥D.prime.torsionField) :=
  charZero_of_injective_ringHom (NumberField.FinitePlace.embedding s.1.maximalIdeal).injective

theorem value_mem_logShell
    (s : (iutInitialThetaOddSupportTorsionQRootSource D).badFinset) :
    value D s ∈ LocalPadicLog.logShell (k :=
      s.1.maximalIdeal.adicCompletion ↥D.prime.torsionField)
      (Arithmetic.residueChar s.1) :=
  LocalPadicLog.paperNormalizedLog_mem_logShell
    (Arithmetic.residueChar_prime s.1)
    (InitialThetaLogWitness.norm_residueChar_lt_one s.1)
    (iutInitialThetaFullQRoot_norm_lt_one D s).le

end
end JoshiTeich.Act1Scene1.PaperLogWitnessHull
