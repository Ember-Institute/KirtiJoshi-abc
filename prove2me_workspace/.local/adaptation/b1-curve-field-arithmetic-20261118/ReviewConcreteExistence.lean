import ArithmeticTeichmullerSpaces.Prologue.Audit.Checks
import ArithmeticTeichmullerSpaces.Prologue.Audit.ImportAudit
import ArithmeticTeichmullerSpaces.Act1Scene1
import ArithmeticTeichmullerSpaces.Prologue.Audit.AxiomAudit
import Solutions.Source_ReferenceIutCurveConcreteExistence
import Theorems.Thm_AbcAdaptation_Reference_Iut_Corollary22Inputs_c2

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut

universe u v

variable {T : Genl.HeightTheory} {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}
variable {K : T.CBS} {d : ℕ}

#check IsConcrete
#check ConcreteThetaDataExistence
#check ConcreteThetaDataExistence.toThetaDataExistence
#check CurveInputs.concreteThetaDataExistence

#print axioms IsConcrete
#print axioms ConcreteThetaDataExistence
#print axioms ConcreteThetaDataExistence.toThetaDataExistence
#print axioms CurveInputs.concreteThetaDataExistence

example (D : InitialThetaData AG TG) (LT : LocalTheory.{u, v} D.Kt)
    (TL : ThetaLocalData D LT) (QI : QPilotInputs D) (TA : TowerArithmetic D LT TL)
    (h7 : 7 ≤ D.ℓ) :
    let X := concreteVariantData D LT TL QI
    let inv : Theorem110Invariants X := TL.invariants QI
    IsConcrete X ∧ Theorem110Certificate inv ∧ Nonempty inv.LocalEstimate :=
  ⟨⟨D, LT, TL, QI, rfl⟩, TA.certificate (QI := QI) h7, ⟨TA.localEstimate (QI := QI)⟩⟩

private theorem review_c2_of_concrete (I : Corollary22Inputs T K d)
    (ex : ConcreteThetaDataExistence.{u, v} (AG := AG) (TG := TG) I)
    (hd : 1 ≤ d) (cheb : ChebyshevBound) (pnt : PrimeCountingBound)
    (h312 : ∀ (D : InitialThetaData AG TG) (LT : LocalTheory.{u, v} D.Kt)
      (TL : ThetaLocalData D LT) (QI : QPilotInputs D),
      Corollary312Variant (concreteVariantData D LT TL QI))
    (x : T.Pt T.tripod) (hx : x ∈ T.cbsSet K ∩ T.ptLE T.tripod d)
    (hxe : x ∉ I.excCore) (hH : I.threshold cheb ≤ I.h x) :
    1 / 6 * I.h x ≤ (1 + epsilonE (deltaBound d) (I.h x)) *
        (T.logDiff T.tripod x + T.logCond T.tripod x) + (40 * pnt.η + I.B / 3) ∧
      epsilonE (deltaBound d) (I.h x) ≤ 1 ∧
      0 ≤ T.logDiff T.tripod x + T.logCond T.tripod x :=
  I.c2 (P := IsConcrete) hd ex.toThetaDataExistence cheb pnt
    (fun _ ⟨D, LT, TL, QI, hX⟩ => hX ▸ h312 D LT TL QI) x hx hxe hH

#print axioms review_c2_of_concrete

end AbcAdaptation.Reference.Iut
