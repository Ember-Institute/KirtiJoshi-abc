from scheduler_common import run
u='.local/adaptation/local-conductor-sourceproof-20261115/'
run('source-graph-leaf',u+'ExtractLocalConductorGraph.lean')
run('syntax-leaf',u+'ExtractLocalConductorSyntax.lean')
run('all-constants-review',u+'AuditAllConstants.lean',kind='review')
