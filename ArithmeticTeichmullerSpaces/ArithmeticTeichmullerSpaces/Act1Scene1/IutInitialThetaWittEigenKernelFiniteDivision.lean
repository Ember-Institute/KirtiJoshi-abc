import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittFrobeniusThetaOrbit
import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittEigenRadiusDynamics
import Mathlib.Algebra.Divisibility.Units
import Mathlib.RingTheory.Coprime.Lemmas

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITT-EIGEN-KERNEL-FINITE-DIVISION
source: Joshi II `se:ff-rings` and `pr:teichmuller-lift-A`, the
full B^{phi=p} evaluation kernel and the Tate-period term.
fidelity: every actual phi=p element killed by original theta is
divisible by every positive Frobenius translate of actual xi. This
follows from the proved principal theta kernel, actual eigen equation,
and invertibility of p. Pairwise coprimality gives divisibility by any
finite product of distinct translates, with a unique actual quotient.
Original proofs; no reference implementation copied.
boundary: Scene1/Derived; no period representation or full Tate-kernel
identity is input or asserted. Infinite-product division remains separate.
Original carrier, uniformity and Prologue R5 retained.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittEigenKernelFiniteDivision

open JoshiTeich.Prologue InitialThetaWittAllRadiusCompletion
open InitialThetaWittAllRadiusFrobenius InitialThetaWittThetaPrincipalKernel
open InitialThetaWittFrobeniusThetaOrbit InitialThetaWittEigenRadiusDynamics
open InitialThetaWittThetaEvaluation
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

local instance selectedPrime : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

theorem prime_isUnit : IsUnit (Arithmetic.residueChar w.1 : Carrier D w) := by
  have h := (InitialThetaBoundedWittLocalization.prime_isUnit D w).map (inclusion D w)
  simpa only [map_natCast] using h

theorem primitiveOrbit_dvd_eigen (x : Eigen D w) (hx : evaluation D w x.val = 0) (n : ℕ) :
    primitiveOrbit D w n ∣ x.val := by
  induction n with
  | zero =>
    rw [primitiveOrbit_zero]
    exact (evaluation_eq_zero_iff_dvd D w x.val).mp hx
  | succ n ih =>
    have h := map_dvd (frobeniusEquiv D w).toRingHom ih
    have he : frobeniusEquiv D w x.val = (Arithmetic.residueChar w.1 : Carrier D w) * x.val := by
      have hEigen : frobeniusEquiv D w x.val =
          (Arithmetic.residueChar w.1 : Padic (Arithmetic.residueChar w.1)) • x.val := x.property
      simpa only [Nat.cast_smul_eq_nsmul, nsmul_eq_mul] using hEigen
    change frobeniusEquiv D w (primitiveOrbit D w n) ∣ frobeniusEquiv D w x.val at h
    rw [he, ← primitiveOrbit_succ] at h
    exact (prime_isUnit D w).dvd_mul_left.mp h

def finiteProduct (s : Finset ℕ) : Carrier D w :=
  ∏ n ∈ s, primitiveOrbit D w n

theorem finiteProduct_ne_zero (s : Finset ℕ) : finiteProduct D w s ≠ 0 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro hzero
    have h := congrArg (evaluation D w) hzero
    exact (one_ne_zero : (1 : InitialThetaWittThetaBound.Untilt D w) ≠ 0)
      (by simpa only [finiteProduct, Finset.prod_empty, map_one, map_zero] using h)
  | @insert n s hn ih =>
    intro hzero
    apply ih
    apply (InitialThetaWittPrincipalIdealClosed.multiplication_isUniformEmbedding D w
      (primitiveOrbit D w n) (primitiveOrbit_ne_zero D w n)).injective
    change primitiveOrbit D w n * finiteProduct D w s = primitiveOrbit D w n * 0
    simpa only [finiteProduct, Finset.prod_insert hn, mul_zero] using hzero

theorem finiteProduct_dvd_eigen (s : Finset ℕ) (x : Eigen D w)
    (hx : evaluation D w x.val = 0) : finiteProduct D w s ∣ x.val := by
  exact Finset.prod_dvd_of_coprime ((primitiveOrbit_pairwise_isCoprime D w).set_pairwise _)
    (fun n _ => primitiveOrbit_dvd_eigen D w x hx n)

theorem existsUnique_finiteProduct_quotient (s : Finset ℕ) (x : Eigen D w)
    (hx : evaluation D w x.val = 0) :
    ∃! y : Carrier D w, finiteProduct D w s * y = x.val := by
  obtain ⟨y, hy⟩ := finiteProduct_dvd_eigen D w s x hx
  refine ⟨y, hy.symm, ?_⟩
  intro z hz
  apply (InitialThetaWittPrincipalIdealClosed.multiplication_isUniformEmbedding D w
    (finiteProduct D w s) (finiteProduct_ne_zero D w s)).injective
  exact hz.trans hy

end
end JoshiTeich.Act1Scene1.InitialThetaWittEigenKernelFiniteDivision
