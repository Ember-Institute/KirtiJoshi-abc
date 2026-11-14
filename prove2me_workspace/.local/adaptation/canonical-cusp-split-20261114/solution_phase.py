from pathlib import Path
import importlib.util
b=Path('/home/admin-wsl/Coq/abc/prove2me_workspace/.local/adaptation/canonical-cusp-split-20261114')
spec=importlib.util.spec_from_file_location('ci',b/'ci.py');ci=importlib.util.module_from_spec(spec);spec.loader.exec_module(ci)
u='.local/adaptation/canonical-cusp-split-20261114/'
for i in range(2):
    ci.run('upload-type-'+str(i)+'-leaf',u+'UploadType'+str(i)+'.lean',memory='6GiB' if i==0 else '16GiB')
ci.run('solution-leaf',u+'Solution_canonicalCuspPolarLinearEquivalence.lean')
ci.run('types-leaf',u+'AuditSolution.lean',duration='65s',memory='7GiB')
ci.run('production-gates-review',u+'ProductionGates.lean','review')
