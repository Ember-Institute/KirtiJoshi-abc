from pathlib import Path
import importlib.util
b=Path('/home/admin-wsl/Coq/abc/prove2me_workspace/.local/adaptation/belyi-height-split-20261114')
spec=importlib.util.spec_from_file_location('ci',b/'ci.py');ci=importlib.util.module_from_spec(spec);spec.loader.exec_module(ci)
u='.local/adaptation/belyi-height-split-20261114/'
ci.run('solution-leaf',u+'Solution_belyiHeightRelation.lean')
ci.run('types-leaf',u+'AuditSolution.lean')
ci.run('production-gates-review',u+'ProductionGates.lean','review')
