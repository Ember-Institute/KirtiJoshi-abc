import ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaWittTwistedQuotient

/-!
source-id: JT-SCENE1-INITIAL-THETA-WITT-TWISTED-QUOTIENT-CLASSIFICATION
source: Joshi II `eq:tate-module-of-lubin-tate` and
`pr:teichmuller-lift-A`, together with the actual Tate-period and
twisted-space comparison already proved in Scene1.
fidelity: identifies the remaining classification claim with the
subsingleton property of either residual quotient. The statement is an
equivalence; no side is asserted unconditionally.
boundary: Scene1/Derived; original carrier, topology, scalar action and R5
remain. No paper B or cross-source identity is introduced.
-/

namespace JoshiTeich.Act1Scene1.InitialThetaWittTwistedQuotientClassification

open JoshiTeich.Prologue InitialThetaWittAllRadiusCompletion
open InitialThetaWittTwistedTatePeriod InitialThetaWittTwistedQuotient
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

theorem quotient_subsingleton_iff_eq_top
    {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    (S : Submodule R M) :
    (Subsingleton (M ⧸ S)) ↔ S = ⊤ := by
  constructor
  · intro h
    apply top_unique
    intro x _
    have hx : S.mkQ x = S.mkQ 0 :=
      @Subsingleton.elim (M ⧸ S) h _ _
    have hx0 : S.mkQ x = 0 := by
      simpa only [map_zero] using hx
    exact (Submodule.Quotient.mk_eq_zero _).mp hx0
  · intro h
    constructor
    intro a b
    obtain ⟨x, rfl⟩ := S.mkQ_surjective a
    obtain ⟨y, rfl⟩ := S.mkQ_surjective b
    apply (Submodule.Quotient.eq _).mpr
    rw [h]
    trivial

theorem twistedQuotient_subsingleton_iff_surjective :
    Subsingleton (Twisted D w ⧸ twistedPeriodLine D w) ↔
      Function.Surjective (twistedPeriodMap D w) := by
  rw [quotient_subsingleton_iff_eq_top]
  constructor
  · intro h y
    obtain ⟨v, hv⟩ := (show y ∈ twistedPeriodLine D w from by
      rw [h]
      trivial)
    exact ⟨v, hv⟩
  · intro hs
    apply le_antisymm le_top
    rintro y _
    obtain ⟨v, rfl⟩ := hs y
    exact ⟨v, rfl⟩

theorem twistedQuotient_subsingleton_iff_unique_scalar :
    Subsingleton (Twisted D w ⧸ twistedPeriodLine D w) ↔
      (∀ y : twistedSubmodule D w, ∃! a : Padic (Arithmetic.residueChar w.1),
        a • canonicalSolution D w = y) :=
  (twistedQuotient_subsingleton_iff_surjective D w).trans
    (unique_scalar_representation_iff_surjective D w).symm

theorem residualQuotients_subsingleton_iff :
    Subsingleton (fullKernel D w ⧸ fullPeriodLine D w) ↔
      Subsingleton (twistedSubmodule D w ⧸ twistedPeriodLine D w) := by
  constructor
  · intro h
    letI : Subsingleton (fullKernel D w ⧸ fullPeriodLine D w) := h
    constructor
    intro a b
    apply (quotientContinuousLinearEquiv D w).symm.injective
    exact Subsingleton.elim _ _
  · intro h
    letI : Subsingleton (twistedSubmodule D w ⧸ twistedPeriodLine D w) := h
    constructor
    intro a b
    apply (quotientContinuousLinearEquiv D w).injective
    exact Subsingleton.elim _ _

theorem fullQuotient_subsingleton_iff_unique_scalar :
    Subsingleton (fullKernel D w ⧸ fullPeriodLine D w) ↔
      (∀ y : twistedSubmodule D w, ∃! a : Padic (Arithmetic.residueChar w.1),
        a • canonicalSolution D w = y) :=
  (residualQuotients_subsingleton_iff D w).trans
    (twistedQuotient_subsingleton_iff_unique_scalar D w)

end
end JoshiTeich.Act1Scene1.InitialThetaWittTwistedQuotientClassification
