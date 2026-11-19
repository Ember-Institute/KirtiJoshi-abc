import ArithmeticTeichmullerSpaces.Prologue.Audit.Checks
import ArithmeticTeichmullerSpaces.Prologue.Audit.ImportAudit
import ArithmeticTeichmullerSpaces.Act1Scene1
import ArithmeticTeichmullerSpaces.Prologue.Audit.AxiomAudit
import Solutions.Source_ReferenceIutConcreteInvariants
import Solutions.Source_ReferenceIutConcreteLocalArithmetic

open AbcAdaptation.Reference.Iut

#check concreteVariantData
#check ThetaLocalData.invariants
#check TowerArithmetic.certificate
#print axioms ThetaLocalData.thetaComponent_admissible
#print axioms ThetaLocalData.thetaComponent_eq_integral
#print axioms ThetaLocalData.thetaPilot
#print axioms ThetaLocalData.rhsData
#print axioms concreteVariantData
#print axioms LocalTheory.logDK_nonneg
#print axioms ThetaLocalData.dst_prime
#print axioms ThetaLocalData.logDK_eq_zero
#print axioms ThetaLocalData.invariants
#print axioms TowerArithmetic.certificate
#print axioms LocalConstruct.fiber_finite
#print axioms LocalConstruct.localDeg_pos
#print axioms LocalConstruct.ramIdx_pos
#print axioms LocalConstruct.sum_localDeg
#print axioms LocalConstruct.sum_mult
#print axioms LocalConstruct.ordp_eq_of_valued
#print axioms LocalConstruct.ordp_p
#print axioms LocalConstruct.ordp_mul
#print axioms LocalConstruct.ramified_finite
#print axioms LocalConstruct.ordDifferent_eq_zero
