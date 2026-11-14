from scheduler_common import run
u='.local/adaptation/polar-presentation-height-sourceproof-20261114/'
run('direct-solution-leaf',u+'Solution_polarPresentationHeightSum_of_principalRelation.lean')
run('solution-type-axioms-review',u+'AuditSolution.lean','review')
run('production-gates-review',u+'ProductionGates.lean','review')
