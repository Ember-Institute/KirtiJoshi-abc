from scheduler_common import run
u='.local/adaptation/polar-presentation-height-sourceproof-20261114/'
run("source-graph-leaf",u+"ExtractPolarHeightGraph.lean")
run("syntax-leaf",u+"ExtractPolarHeightSyntax.lean")
run("all-constants-review",u+"AuditAllConstants.lean","review")
