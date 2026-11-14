from scheduler_common import run
u='.local/adaptation/belyi-different-conductor-split-20261114/'
run("source-graph-leaf",u+"ExtractConductorGraph.lean")
run("syntax-leaf",u+"ExtractConductorSyntax.lean")
run("all-constants-leaf",u+"AuditAllConstants.lean")
