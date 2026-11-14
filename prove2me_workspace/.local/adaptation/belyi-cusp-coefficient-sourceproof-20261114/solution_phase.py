from scheduler_common import run
u='.local/adaptation/belyi-cusp-coefficient-sourceproof-20261114/'
run('direct-solution-leaf',u+'Solution_belyiCanonicalCuspCoefficientIdentity.lean')
run('solution-type-axioms-review',u+'AuditSolution.lean','review')
run('production-gates-review',u+'ProductionGates.lean','review')
