from scheduler_common import run
u='.local/adaptation/canonical-differential-sourceproof-20261114/'
run('direct-solution-leaf',u+'Solution_canonicalDifferentialChange.lean')
run('solution-type-axioms-review',u+'AuditSolution.lean','review')
run('production-gates-review',u+'ProductionGates.lean','review')
