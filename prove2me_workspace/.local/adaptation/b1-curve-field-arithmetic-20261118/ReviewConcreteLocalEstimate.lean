import ArithmeticTeichmullerSpaces.Prologue.Audit.Checks
import ArithmeticTeichmullerSpaces.Prologue.Audit.ImportAudit
import ArithmeticTeichmullerSpaces.Act1Scene1
import ArithmeticTeichmullerSpaces.Prologue.Audit.AxiomAudit
import Solutions.Source_ReferenceIutConcreteLocalEstimate

set_option autoImplicit false

open AbcAdaptation.Reference.Iut

#check TowerArithmetic.localEstimate

#print axioms LocalTheory.ordp_pow
#print axioms LocalTheory.logDK_prime
#print axioms LocalTheory.packetVol_scaledIntegral
#print axioms LocalTheory.card_labelType
#print axioms TowerArithmetic.prop14
#print axioms TowerArithmetic.contScalar_spec
#print axioms TowerArithmetic.isUnit_archScalar
#print axioms TowerArithmetic.logQAt_eq
#print axioms TowerArithmetic.ramTerm_le
#print axioms TowerArithmetic.cont_isHullRegion
#print axioms TowerArithmetic.cont_mem_hullRegions
#print axioms TowerArithmetic.thetaPilot_subset
#print axioms TowerArithmetic.vol_finite
#print axioms TowerArithmetic.vol_infinite
#print axioms TowerArithmetic.packetVol_mono
#print axioms TowerArithmetic.localEstimate
