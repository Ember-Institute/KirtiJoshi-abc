from scheduler_common import run
u='.local/adaptation/conductor-extension-split-20261114/'
run('source-graph-leaf',u+'ExtractConductorExtensionGraph.lean')
run('syntax-leaf',u+'ExtractConductorExtensionSyntax.lean')
run('all-constants-leaf',u+'AuditAllConstants.lean')
