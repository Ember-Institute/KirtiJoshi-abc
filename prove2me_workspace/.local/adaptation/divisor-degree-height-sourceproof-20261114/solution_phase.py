from scheduler_common import run
u='.local/adaptation/divisor-degree-height-sourceproof-20261114/'
run('direct-solution-leaf',u+'Solution_divisorDegreeHeightComparison.lean')
run('solution-type-axioms-review',u+'AuditSolution.lean','review')
run('production-gates-review',u+'ProductionGates.lean','review')
run('consumer-review',u+'ChecksDegreeHeightConsumer.lean','review')
