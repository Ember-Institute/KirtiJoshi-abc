from scheduler_common import run
u='.local/adaptation/different-accounting-sourceproof-20261115/'
run('solution-leaf',u+'Solution_belyiActualFieldDifferentAccounting.lean')
run('types-leaf',u+'AuditSolution.lean')
run('consumer-review',u+'ChecksDifferentAccountingConsumer.lean',kind='review')
run('production-gates-review',u+'ProductionGates.lean',kind='review')
