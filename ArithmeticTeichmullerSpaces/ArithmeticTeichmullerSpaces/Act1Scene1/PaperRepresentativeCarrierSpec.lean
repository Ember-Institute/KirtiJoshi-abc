/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import ArithmeticTeichmullerSpaces.Act1Scene1.PaperQRepresentativeAccounting
import ArithmeticTeichmullerSpaces.Act1Scene1.ProducerContracts

/-!
source-id: JT-SCENE1-PAPER-REPRESENTATIVE-CARRIER-SPEC
source: Joshi III `ss:weighted-vol`, `pr:general-cohomology-set-const`, and
the representative/multiplicity data required by `cor:cor312`; local generic
consumer `PaperQRepresentativeAccounting`.
fidelity: separates the paper carrier (`V_p^oss` support and `L'` representatives)
from the actual q-pilot carrier. The source map, local term identity, fiber
mass law, and representative multiplicity are explicit fields. No inhabitant is
constructed from the current canonical q-pilot data.
boundary: Scene1/Candidate. This is a specification and conditional consumer;
it does not prove paper representative existence or theta-volume identity.
-/

namespace JoshiTeich.Act1Scene1

open JoshiTeich.Prologue
open NumberField
open scoped BigOperators

universe u
noncomputable section

variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}

structure PaperRepresentativeCarrierSpec
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    (p : ℕ) {O : Type u} [CommRing O]
    [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
    [IsAdicComplete (Ideal.span {(p : O)}) O]
    (T : Corollary312Data D.F O p)
    (P : Corollary312QPilotData p T) where
  /-- The finite place support called `V_p^oss` by the paper. -/
  Voss : Set (NumberField.FinitePlace D.F)
  /-- The paper's finite representative carrier, corresponding to `L'`. -/
  representative : Type u
  [representativeFintype : Fintype representative]
  [representativeDecidableEq : DecidableEq representative]
  representativePlace : representative → NumberField.FinitePlace D.F
  representativePlace_mem_Voss : ∀ r, representativePlace r ∈ Voss
  /-- Fiber multiplicity retained as data instead of hidden in a coercion. -/
  multiplicity : representative → ℕ
  multiplicity_pos : ∀ r, 0 < multiplicity r
  representativeTerm : representative → ℝ
  representativeOfSource : P.badFinset → representative
  sourceTerm_eq : ∀ w : P.badFinset,
    -Real.log
        (Corollary312PaperNormalizedSourceQFactor p T
          (show Corollary312SourceQIndex p T from
            ⟨w.1, P.mem_bad p w.2⟩)) =
      representativeTerm (representativeOfSource w)
  /-- The exact mass-one law needed for an unweighted paper sum. -/
  weight_fiber_sum_eq_one : ∀ r : representative,
    (∑ w : P.badFinset,
      if representativeOfSource w = r then
        Arithmetic.qPilotWeight w.1
      else 0) = 1

namespace PaperRepresentativeCarrierSpec

variable {O : Type u} [CommRing O] (p : ℕ)
variable [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
variable [IsAdicComplete (Ideal.span {(p : O)}) O]
variable {D : JoshiTeich.ReferenceIut.InitialThetaData AG TG}
variable {T : Corollary312Data D.F O p}
variable {P : Corollary312QPilotData p T}

noncomputable def toAccounting
    (C : PaperRepresentativeCarrierSpec D p T P) :
    Corollary312QPilotPaperRepresentativeAccounting p T P where
  representative := C.representative
  representativeFintype := C.representativeFintype
  representativeDecidableEq := C.representativeDecidableEq
  representativeTerm := C.representativeTerm
  representativeOfSource := C.representativeOfSource
  sourceTerm_eq := C.sourceTerm_eq
  weight_fiber_sum_eq_one := C.weight_fiber_sum_eq_one

theorem absLogQ_eq_unweightedPaperCarrierSum
    (C : PaperRepresentativeCarrierSpec D p T P)
    (hOrder : TateOrderNormCompatibility T.scene1.data.link)
    (hNorm : Corollary312RawQNormDegreeNormalization p T hOrder P)
    (hEll : 0 < T.ell) :
    letI : Fintype C.representative := C.representativeFintype
    P.absLogQ p =
      ∑ r : C.representative, C.representativeTerm r := by
  letI : Fintype C.representative := C.representativeFintype
  letI : Fintype (C.toAccounting p).representative := C.representativeFintype
  exact Corollary312QPilotPaperRepresentativeAccounting.absLogQ_eq_unweightedRepresentativeSum
    p (C.toAccounting p) hOrder hNorm hEll

theorem representative_support
    (C : PaperRepresentativeCarrierSpec D p T P) (r : C.representative) :
    C.representativePlace r ∈ C.Voss :=
  C.representativePlace_mem_Voss r

theorem representative_multiplicity_positive
    (C : PaperRepresentativeCarrierSpec D p T P) (r : C.representative) :
    0 < C.multiplicity r :=
  C.multiplicity_pos r

end PaperRepresentativeCarrierSpec

end
end JoshiTeich.Act1Scene1
