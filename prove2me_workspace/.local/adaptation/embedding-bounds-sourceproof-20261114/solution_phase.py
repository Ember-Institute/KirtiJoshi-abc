from pathlib import Path
import importlib.util
b=Path('/home/admin-wsl/Coq/abc/prove2me_workspace/.local/adaptation/embedding-bounds-sourceproof-20261114')
spec=importlib.util.spec_from_file_location('ci',b/'ci.py');ci=importlib.util.module_from_spec(spec);spec.loader.exec_module(ci)
u='.local/adaptation/embedding-bounds-sourceproof-20261114/'
ci.run('direct-solution-leaf',u+'Solution_embeddingBoundsToSet.lean')
ci.run('solution-type-axioms-review',u+'AuditSolution.lean','review')
ci.run('production-gates-review',u+'ProductionGates.lean','review')
