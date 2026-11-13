import Definitions.Def_TripodFermatComposition

set_option autoImplicit false

#check AbcAdaptation.Tripod.Fermat.Pt
#check AbcAdaptation.Tripod.Fermat.fieldOf
#check AbcAdaptation.Tripod.Fermat.degree
#check AbcAdaptation.Tripod.Fermat.toTripod
#check AbcAdaptation.Tripod.Fermat.projectiveHeight
#check AbcAdaptation.Tripod.Fermat.canonicalHeight
#check AbcAdaptation.Tripod.Fermat.HeightNormalization
#check AbcAdaptation.Tripod.Fermat.LiftDifferent
#check AbcAdaptation.Tripod.Fermat.CanonicalEstimate
#check AbcAdaptation.Tripod.statementI_of_fermat_children
#print axioms AbcAdaptation.Tripod.statementI_of_fermat_children

example
    (hNorm : AbcAdaptation.Tripod.Fermat.HeightNormalization)
    (hLift : AbcAdaptation.Tripod.Fermat.LiftDifferent)
    (hFermat : AbcAdaptation.Tripod.Fermat.CanonicalEstimate)
    (hII : AbcAdaptation.Tripod.StatementII) :
    AbcAdaptation.Tripod.StatementI :=
  AbcAdaptation.Tripod.statementI_of_fermat_children hNorm hLift hFermat hII
