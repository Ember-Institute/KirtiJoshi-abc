import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittEigenEvaluationFullKernel

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITT-TATE-BANACH-QUOTIENT-FULL-KERNEL
source: Joshi II `pr:teichmuller-lift-A`, the displayed Tate-period
sequence, and the actual rational Tate period/full-kernel constructions.
fidelity: connects injectivity of the actual Tate Banach quotient evaluation
to the exact equality between the full actual theta kernel and the rational
Tate period range. No injectivity or equality is assumed.
boundary: Scene1/Derived; paper B and cross-source period comparison remain
open.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittTateBanachQuotientFullKernel

open JoshiTeich.Prologue InitialThetaWittAllRadiusCompletion
open InitialThetaWittRationalTatePeriod
open InitialThetaWittTateBanachQuotient
open InitialThetaWittEigenEvaluationFullKernel
open InitialThetaWittEigenKernelTwistedComparison
open InitialThetaWittEigenRadiusDynamics
open scoped Topology
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

local instance selectedPrime : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

theorem tateLine_mem_iff_periodMap_range (x : Eigen D w) :
    x ∈ tateLine D w ↔ x.1 ∈ (periodMap D w).range := by
  constructor
  · rintro ⟨v, hv⟩
    exact ⟨v, congrArg (fun z : Eigen D w => z.1) hv⟩
  · rintro ⟨v, hv⟩
    refine ⟨v, ?_⟩
    exact Subtype.ext hv

theorem eigenKernel_eq_tateLine_iff_fullKernel_eq_periodMapRange :
    (eigenEvaluation D w).ker = tateLine D w ↔
      fullKernel D w = (periodMap D w).range := by
  constructor
  · intro h
    apply le_antisymm
    · intro x hx
      have hphi := (mem_fullKernel D w x).mp hx |>.1
      have hEigen : x ∈ Eigen D w := by
        change InitialThetaWittAllRadiusFrobenius.frobeniusEquiv D w x =
          (Arithmetic.residueChar w.1 : Padic (Arithmetic.residueChar w.1)) • x
        simpa only [Nat.cast_smul_eq_nsmul, nsmul_eq_mul] using hphi
      let y : Eigen D w := ⟨x, hEigen⟩
      have hy : y ∈ (eigenEvaluation D w).ker := by
        change eigenEvaluation D w y = 0
        exact (eigenEvaluation_zero_iff_fullKernel D w y).mpr hx
      have hy' : y ∈ tateLine D w := h ▸ hy
      exact (tateLine_mem_iff_periodMap_range D w y).mp hy'
    · intro x hx
      exact ⟨(periodMap_range_le_frobeniusPrime D w) hx, (periodMap_range_le_kernel D w) hx⟩
  · intro h
    apply le_antisymm ?_ (tateLine_le_kernel D w)
    intro y hy
    have hx : y.1 ∈ (periodMap D w).range := by
      rw [← h]
      exact (eigenEvaluation_zero_iff_fullKernel D w y).mp hy
    exact (tateLine_mem_iff_periodMap_range D w y).mpr hx

theorem quotientEvaluation_injective_iff_fullKernel_eq_periodMapRange :
    Function.Injective (quotientEvaluation D w) ↔
      fullKernel D w = (periodMap D w).range :=
  (quotientEvaluation_injective_iff D w).trans
    (eigenKernel_eq_tateLine_iff_fullKernel_eq_periodMapRange D w)

end
end JoshiTeich.Act1Scene1.InitialThetaWittTateBanachQuotientFullKernel
