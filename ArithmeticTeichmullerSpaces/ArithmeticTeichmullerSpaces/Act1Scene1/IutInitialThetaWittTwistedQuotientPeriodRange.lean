import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittTwistedQuotientClassification

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITT-TWISTED-QUOTIENT-PERIOD-RANGE
source: Joshi II `eq:tate-module-of-lubin-tate` and the actual rational
Tate-period map and full eigen theta kernel constructed in Scene1.
fidelity: identifies triviality of the full residual quotient with the
precise equality between the full actual theta kernel and the rational Tate
period range. This is an equivalence and does not assert either side.
boundary: Scene1/Derived; no paper B, cross-source transport, or global
Tate-kernel classification is supplied.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittTwistedQuotientPeriodRange

open JoshiTeich.Prologue InitialThetaWittAllRadiusCompletion
open InitialThetaWittRationalTatePeriod
open InitialThetaWittTwistedTatePeriod InitialThetaWittTwistedQuotient
open InitialThetaWittTwistedQuotientClassification
open InitialThetaWittEigenKernelTwistedComparison
open scoped Topology
noncomputable section
universe u
variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}
variable (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
variable (w : (iutInitialThetaTateParameterData D).places)

local instance selectedPrime : Fact (Arithmetic.residueChar w.1).Prime :=
  ⟨Arithmetic.residueChar_prime w.1⟩

theorem fullPeriodLine_top_iff_fullKernel_eq_periodRange :
    fullPeriodLine D w = ⊤ ↔
      fullKernel D w = (periodMap D w).range := by
  constructor
  · intro h
    apply le_antisymm
    · intro x hx
      let sx : fullKernel D w := ⟨x, hx⟩
      have hs : sx ∈ fullPeriodLine D w := by
        rw [h]
        trivial
      obtain ⟨v, hv⟩ := hs
      refine ⟨v, ?_⟩
      exact congrArg Subtype.val hv
    · intro x hx
      obtain ⟨v, rfl⟩ := hx
      exact periodMap_mem_fullKernel D w v
  · intro h
    apply top_unique
    intro sx _
    have hx : sx.1 ∈ (periodMap D w).range := by
      rw [← h]
      exact sx.2
    obtain ⟨v, hv⟩ := hx
    refine ⟨v, ?_⟩
    exact Subtype.ext hv

theorem fullQuotient_subsingleton_iff_fullKernel_eq_periodRange :
    Subsingleton (fullKernel D w ⧸ fullPeriodLine D w) ↔
      fullKernel D w = (periodMap D w).range :=
  (quotient_subsingleton_iff_eq_top (fullPeriodLine D w)).trans
    (fullPeriodLine_top_iff_fullKernel_eq_periodRange D w)

end
end JoshiTeich.Act1Scene1.InitialThetaWittTwistedQuotientPeriodRange
