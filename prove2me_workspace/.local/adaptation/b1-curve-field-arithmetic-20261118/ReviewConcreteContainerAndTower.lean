import ArithmeticTeichmullerSpaces.Prologue.Audit.Checks
import ArithmeticTeichmullerSpaces.Prologue.Audit.ImportAudit
import ArithmeticTeichmullerSpaces.Act1Scene1
import ArithmeticTeichmullerSpaces.Prologue.Audit.AxiomAudit
import Solutions.Source_ReferenceIutConcreteContainer
import Solutions.Source_ReferenceIutTowerLocalFacts

open AbcAdaptation.Reference.Iut

#check LocalTheory.container
#check LocalTheory.vol
#check LocalTheory.hull
#check TowerLocalFacts
#check RelRamIdxModLeTwo
#print axioms LocalTheory.container
#print axioms LocalTheory.proj_productRegion
#print axioms LocalTheory.vol
#print axioms LocalTheory.exists_leastHullRegion
#print axioms LocalTheory.hull
#print axioms wildConst_eq_zero
#print axioms fieldOfModuli_le_tripodalFieldOf
#print axioms instAlgebraFieldOfModuliTripodal
#print axioms algebraMap_fieldOfModuli_tripodal_apply
#print axioms instIsScalarTowerFieldOfModuliTripodal
#print axioms instIsScalarTowerRatFieldOfModuliTripodal
#print axioms instFiniteDimensionalFieldOfModuliTripodal
#print axioms finrank_tripodal_eq_mul
#print axioms liesOver_placeTpd
#print axioms residueChar_placeTpd
#print axioms ramIdx_eq_ramIdx_placeTpd_mul
#print axioms inertDeg_eq_inertDeg_placeTpd_mul
#print axioms RelRamIdxModLeTwo
#print axioms TowerLocalFacts
