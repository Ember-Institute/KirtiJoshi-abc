from pathlib import Path
import importlib.util
b=Path('/home/admin-wsl/Coq/abc/prove2me_workspace/.local/adaptation/canonical-cusp-split-20261114')
spec=importlib.util.spec_from_file_location('ci',b/'ci.py');ci=importlib.util.module_from_spec(spec);spec.loader.exec_module(ci)
u='.local/adaptation/canonical-cusp-split-20261114/'
ci.run('source-graph-leaf',u+'ExtractCanonicalCuspGraph.lean')
ci.run('syntax-leaf',u+'ExtractCanonicalCuspSyntax.lean')
ci.run('all-constants-leaf',u+'AuditAllConstants.lean')
