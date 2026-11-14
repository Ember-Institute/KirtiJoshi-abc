from scheduler_common import run
u='.local/adaptation/different-accounting-sourceproof-20261115/'
run('source-graph-leaf',u+'ExtractDifferentAccountingGraph.lean')
run('syntax-leaf',u+'ExtractDifferentAccountingSyntax.lean')
run('all-constants-review',u+'AuditAllConstants.lean',kind='review')
