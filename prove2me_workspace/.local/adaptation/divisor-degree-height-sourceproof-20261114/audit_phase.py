from scheduler_common import run
u=".local/adaptation/divisor-degree-height-sourceproof-20261114/"
run("source-graph-leaf",u+"ExtractDegreeHeightGraph.lean")
run("syntax-leaf",u+"ExtractDegreeHeightSyntax.lean")
run("all-constants-review",u+"AuditAllConstants.lean","review")
