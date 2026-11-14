from scheduler_common import run
u='.local/adaptation/belyi-cusp-coefficient-sourceproof-20261114/'
run("source-graph-leaf",u+"ExtractCoefficientGraph.lean")
run("syntax-leaf",u+"ExtractCoefficientSyntax.lean")
run("all-constants-review",u+"AuditAllConstants.lean","review")
