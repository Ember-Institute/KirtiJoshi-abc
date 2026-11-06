/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import ArithmeticTeichmullerSpaces.Act1Scene1.PaperQRepresentativeFiberMass
import ArithmeticTeichmullerSpaces.Act1Scene1.ProducerContracts

/-!
source-id: JT-SCENE1-PAPER-WEIGHTED-REPRESENTATIVE-CARRIER-SPEC
source: Joshi III `ss:weighted-vol`, `eq:weights`, and the actual q-pilot
fiber-mass accounting in `PaperQRepresentativeFiberMass.lean`.
fidelity: keeps the computed q-pilot mass of each paper representative fiber
explicit. This matches the weighted-volume route and avoids replacing a
strictly subprobability fiber by mass one. The source map, residue-characteristic
label, paper term and representative multiplicity remain explicit fields.
boundary: Scene1/Candidate. No paper `L'` representative inhabitant or
theta-volume identity is constructed.
-/

namespace JoshiTeich.Act1Scene1

open JoshiTeich.Prologue
open NumberField
open scoped BigOperators

universe u
noncomputable section

variable {AG : JoshiTeich.ReferenceIut.AnabelianGeometry.{u}}
variable {TG : JoshiTeich.ReferenceIut.TemperedGeometry AG}

structure PaperWeightedRepresentativeCarrierSpec
    (D : JoshiTeich.ReferenceIut.InitialThetaData AG TG)
    (p : ℕ) {O : Type u} [CommRing O]
    [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
    [IsAdicComplete (Ideal.span {(p : O)}) O]
    (T : Corollary312Data D.F O p)
    (P : Corollary312QPilotData p T) where
  Voss : Set (NumberField.FinitePlace D.F)
  representative : Type u
  [representativeFintype : Fintype representative]
  [representativeDecidableEq : DecidableEq representative]
  representativePlace : representative → NumberField.FinitePlace D.F
  representativePlace_mem_Voss : ∀ r, representativePlace r ∈ Voss
  multiplicity : representative → ℕ
  multiplicity_pos : ∀ r, 0 < multiplicity r
  representativeTerm : representative → ℝ
  representativeOfSource : P.badFinset → representative
  primeLabel : representative → ℕ
  source_primeLabel_eq : ∀ w : P.badFinset,
    Arithmetic.residueChar w.1 = primeLabel (representativeOfSource w)
  sourceTerm_eq : ∀ w : P.badFinset,
    -Real.log
        (Corollary312PaperNormalizedSourceQFactor p T
          (show Corollary312SourceQIndex p T from
            ⟨w.1, P.mem_bad p w.2⟩)) =
      representativeTerm (representativeOfSource w)

namespace PaperWeightedRepresentativeCarrierSpec

variable {O : Type u} [CommRing O] (p : ℕ)
variable [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
variable [IsAdicComplete (Ideal.span {(p : O)}) O]
variable {D : JoshiTeich.ReferenceIut.InitialThetaData AG TG}
variable {T : Corollary312Data D.F O p}
variable {P : Corollary312QPilotData p T}

theorem absLogQ_eq_fiberMassWeightedRepresentativeSum
    (C : PaperWeightedRepresentativeCarrierSpec D p T P)
    (hOrder : TateOrderNormCompatibility T.scene1.data.link)
    (hNorm : Corollary312RawQNormDegreeNormalization p T hOrder P)
    (hEll : 0 < T.ell) :
    letI : Fintype C.representative := C.representativeFintype
    letI : DecidableEq C.representative := C.representativeDecidableEq
    P.absLogQ p =
      ∑ r : C.representative,
        qPilotRepresentativeFiberMass p P C.representativeOfSource r *
          C.representativeTerm r := by
  letI : Fintype C.representative := C.representativeFintype
  letI : DecidableEq C.representative := C.representativeDecidableEq
  exact Corollary312QPilotData.absLogQ_eq_fiberMassRepresentativeSum
    p P C.representativeOfSource C.representativeTerm C.sourceTerm_eq
      hOrder hNorm hEll

theorem representative_fiber_mass_mem_unitInterval
    (C : PaperWeightedRepresentativeCarrierSpec D p T P)
    (r : C.representative) :
    letI : Fintype C.representative := C.representativeFintype
    letI : DecidableEq C.representative := C.representativeDecidableEq
    0 ≤ qPilotRepresentativeFiberMass p P C.representativeOfSource r ∧
      qPilotRepresentativeFiberMass p P C.representativeOfSource r ≤ 1 := by
  letI : Fintype C.representative := C.representativeFintype
  letI : DecidableEq C.representative := C.representativeDecidableEq
  exact qPilotRepresentativeFiberMass_mem_unitInterval p P C.representativeOfSource
    C.primeLabel C.source_primeLabel_eq r

theorem representative_support
    (C : PaperWeightedRepresentativeCarrierSpec D p T P) (r : C.representative) :
    C.representativePlace r ∈ C.Voss :=
  C.representativePlace_mem_Voss r

theorem representative_multiplicity_positive
    (C : PaperWeightedRepresentativeCarrierSpec D p T P) (r : C.representative) :
    0 < C.multiplicity r :=
  C.multiplicity_pos r

end PaperWeightedRepresentativeCarrierSpec

end
end JoshiTeich.Act1Scene1
