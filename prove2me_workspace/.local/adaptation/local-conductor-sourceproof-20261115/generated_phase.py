from scheduler_common import run
u='.local/adaptation/local-conductor-sourceproof-20261115/'
run('solution-leaf',u+'Solution_belyiActualFieldLocalConductorComparison.lean')
run('types-leaf',u+'AuditSolution.lean')
run('consumer-review',u+'ChecksLocalConductorConsumer.lean',kind='review')
run('production-gates-review',u+'ProductionGates.lean',kind='review')
