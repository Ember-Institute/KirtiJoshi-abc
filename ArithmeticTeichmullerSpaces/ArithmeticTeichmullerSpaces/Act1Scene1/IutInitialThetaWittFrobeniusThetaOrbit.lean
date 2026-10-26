import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittThetaPrincipalKernel
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittAllRadiusFrobenius
import Mathlib.Algebra.Ring.Aut
import Mathlib.RingTheory.Ideal.Operations

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITT-FROBENIUS-THETA-ORBIT
source: Joshi II `se:ff-rings`, `pr:primitive-elements1` and
`pr:teichmuller-lift-A`, primitive maximal ideals and Frobenius periods.
fidelity: computes the actual positive Frobenius orbit of the original
primitive xi=[p-flat]-p. Its n-th member has original theta value
p^(p^n)-p. For n>0 this is nonzero by the original untilt norm.
The proved maximal theta kernel then gives pairwise coprimality of
the actual orbit factors in the same common complete ring.
Original proofs; no reference implementation copied.
boundary: Scene1/Derived; no coprimality or orbit-separation law is
input. No infinite product, full eigen kernel or paper B identity
is asserted. Original topology and Prologue R5 retained.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittFrobeniusThetaOrbit

open JoshiTeich.Prologue InitialThetaWittAllRadiusCompletion
open InitialThetaWittAllRadiusFrobenius InitialThetaWittThetaPrincipalKernel
open InitialThetaWittThetaEvaluation InitialThetaWittThetaBound
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

local instance selectedPrime : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

def teichPrime : Carrier D w :=
  InitialThetaWittAllRadiusExpansion.ainfMap D w
    (InitialThetaBoundedWittLocalization.teichVarpi D w)

theorem primitive_eq_teichPrime_sub :
    primitive D w = teichPrime D w - Arithmetic.residueChar w.1 := by
  change InitialThetaWittAllRadiusExpansion.ainfMap D w
    (InitialThetaBoundedWittLocalization.teichVarpi D w - Arithmetic.residueChar w.1) = _
  rw [map_sub, map_natCast]
  rfl

theorem frobenius_teichPrime : frobeniusEquiv D w (teichPrime D w) =
    teichPrime D w ^ Arithmetic.residueChar w.1 := by
  change frobeniusEquiv D w (inclusion D w
    (InitialThetaBoundedWittLocalization.inclusion D w _)) = _
  rw [frobenius_inclusion]
  change inclusion D w (InitialThetaBoundedWittLocalization.frobenius D w
    (InitialThetaBoundedWittLocalization.inclusion D w _)) = _
  rw [InitialThetaBoundedWittLocalization.frobenius_inclusion]
  have h := congrArg (InitialThetaWittAllRadiusExpansion.ainfMap D w)
    (InitialThetaBoundedWittLocalization.sourceFrobenius_teichVarpi D w)
  simpa only [teichPrime, InitialThetaWittAllRadiusExpansion.ainfMap,
    RingHom.comp_apply, map_pow] using h

theorem iterate_teichPrime (n : ℕ) :
    (frobeniusEquiv D w ^ n) (teichPrime D w) =
      teichPrime D w ^ (Arithmetic.residueChar w.1 ^ n) := by
  induction n with
  | zero => simp only [pow_zero, RingAut.one_apply, pow_one]
  | succ n ih =>
    rw [pow_succ', RingAut.mul_apply, ih, map_pow, frobenius_teichPrime,
      ← pow_mul, ← pow_succ']

def primitiveOrbit (n : ℕ) : Carrier D w :=
  (frobeniusEquiv D w ^ n) (primitive D w)

theorem primitiveOrbit_zero : primitiveOrbit D w 0 = primitive D w := by
  simp only [primitiveOrbit, pow_zero, RingAut.one_apply]

theorem primitiveOrbit_succ (n : ℕ) :
    primitiveOrbit D w (n + 1) = frobeniusEquiv D w (primitiveOrbit D w n) := by
  simp only [primitiveOrbit, pow_succ', RingAut.mul_apply]

theorem primitiveOrbit_add (m n : ℕ) :
    primitiveOrbit D w (m + n) = (frobeniusEquiv D w ^ m) (primitiveOrbit D w n) := by
  simp only [primitiveOrbit, pow_add, RingAut.mul_apply]

theorem primitiveOrbit_ne_zero (n : ℕ) : primitiveOrbit D w n ≠ 0 := by
  intro h
  change (frobeniusEquiv D w ^ n) (primitive D w) = 0 at h
  apply primitive_ne_zero D w
  exact (frobeniusEquiv D w ^ n).injective (h.trans (map_zero _).symm)

theorem primitiveOrbit_eq (n : ℕ) :
    primitiveOrbit D w n = teichPrime D w ^ (Arithmetic.residueChar w.1 ^ n) -
      Arithmetic.residueChar w.1 := by
  rw [primitiveOrbit, primitive_eq_teichPrime_sub, map_sub, map_natCast, iterate_teichPrime]

theorem evaluation_teichPrime : evaluation D w (teichPrime D w) = Arithmetic.residueChar w.1 := by
  change evaluation D w (inclusion D w (InitialThetaBoundedWittLocalization.inclusion D w
    (InitialThetaBoundedWittLocalization.teichVarpi D w))) = _
  rw [evaluation_inclusion, InitialThetaBoundedWittLocalization.evaluation_inclusion,
    InitialThetaBoundedWittLocalization.theta_teichVarpi]
  rfl

theorem evaluation_primitiveOrbit (n : ℕ) :
    evaluation D w (primitiveOrbit D w n) =
      (Arithmetic.residueChar w.1 : Untilt D w) ^ (Arithmetic.residueChar w.1 ^ n) -
        Arithmetic.residueChar w.1 := by
  rw [primitiveOrbit_eq, map_sub, map_pow, evaluation_teichPrime, map_natCast]

theorem evaluation_primitiveOrbit_ne_zero (n : ℕ) (hn : 0 < n) :
    evaluation D w (primitiveOrbit D w n) ≠ 0 := by
  rw [evaluation_primitiveOrbit]
  intro h
  have he := congrArg norm (sub_eq_zero.mp h)
  rw [norm_pow] at he
  have hp := (InitialThetaCanonicalGeometricFontaine.primeNormFact D w).out
  exact (ne_of_lt (pow_lt_self_of_lt_one₀ hp.1 hp.2
    (one_lt_pow₀ (Arithmetic.residueChar_prime w.1).one_lt hn.ne')) ) he

theorem primitive_isCoprime_orbit (n : ℕ) (hn : 0 < n) :
    IsCoprime (primitive D w) (primitiveOrbit D w n) := by
  apply (Ideal.sup_eq_top_iff_isCoprime _ _).mp
  by_contra htop
  have hm : (Ideal.span {primitive D w} : Ideal (Carrier D w)).IsMaximal := by
    rw [← kernel_eq_span]
    exact InitialThetaWittThetaSurjective.kernel_isMaximal D w
  have heq := hm.eq_of_le htop le_sup_left
  have hx : primitiveOrbit D w n ∈ (Ideal.span {primitive D w} : Ideal (Carrier D w)) := by
    rw [heq]
    exact (show Ideal.span {primitiveOrbit D w n} ≤
      Ideal.span {primitive D w} ⊔ Ideal.span {primitiveOrbit D w n} from le_sup_right)
        (Ideal.subset_span (Set.mem_singleton _))
  exact evaluation_primitiveOrbit_ne_zero D w n hn
    ((evaluation_eq_zero_iff_dvd D w _).mpr (Ideal.mem_span_singleton.mp hx))

theorem primitiveOrbit_isCoprime_of_lt (m n : ℕ) (hmn : m < n) :
    IsCoprime (primitiveOrbit D w m) (primitiveOrbit D w n) := by
  have h := (primitive_isCoprime_orbit D w (n - m) (Nat.sub_pos_of_lt hmn)).map
    (frobeniusEquiv D w ^ m).toRingHom
  change IsCoprime (primitiveOrbit D w m)
    ((frobeniusEquiv D w ^ m) (primitiveOrbit D w (n - m))) at h
  rwa [← primitiveOrbit_add, Nat.add_sub_of_le hmn.le] at h

theorem primitiveOrbit_pairwise_isCoprime :
    Pairwise (fun m n => IsCoprime (primitiveOrbit D w m) (primitiveOrbit D w n)) := by
  intro m n hmn
  rcases lt_or_gt_of_ne hmn with h | h
  · exact primitiveOrbit_isCoprime_of_lt D w m n h
  · exact (primitiveOrbit_isCoprime_of_lt D w n m h).symm

end
end JoshiTeich.Act1Scene1.InitialThetaWittFrobeniusThetaOrbit
