from scheduler_common import run
u='.local/adaptation/canonical-differential-sourceproof-20261114/'
run("source-graph-leaf",u+"ExtractDifferentialGraph.lean")
run("syntax-leaf",u+"ExtractDifferentialSyntax.lean")
run("all-constants-review",u+"AuditAllConstants.lean","review")
