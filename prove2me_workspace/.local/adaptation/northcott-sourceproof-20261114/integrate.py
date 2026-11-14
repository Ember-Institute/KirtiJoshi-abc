from pathlib import Path
import hashlib,json,shutil,subprocess
r=Path('/home/admin-wsl/Coq/abc');w=r/'prove2me_workspace';d=Path('/tmp/p2m-northcott-next-20261114');b=w/'.local/adaptation/northcott-sourceproof-20261114';b.mkdir(exist_ok=True)
manifest=json.loads((d/'SOURCE_MANIFEST.json').read_text())
for row in manifest['existing_definition_and_consumer_inputs']:
 p=Path(row['path']);assert hashlib.sha256(p.read_bytes()).hexdigest()==row['sha256'],str(p)
for row in manifest['reference_iut']['source_files']+manifest['platform_mathlib']['source_files']:
 p=Path(row['path']);assert hashlib.sha256(p.read_bytes()).hexdigest()==row['sha256'],str(p)
files={}
for folder in ['Definitions','Theorems']:
 for p in (d/folder).glob('*.lean'):
  rel=str(p.relative_to(d));q=w/rel;assert not q.exists() or rel=='Theorems/Thm_AbcAdaptation_Tripod_boundedDegreeFiniteness.lean',rel
  shutil.copy2(p,q);files[rel]=hashlib.sha256(q.read_bytes()).hexdigest()
for n in ['README.md','SOURCE_LEDGER.md','SOURCE_MANIFEST.json']:shutil.copy2(d/n,b/n)
shutil.copytree(d/'licenses',b/'licenses',dirs_exist_ok=True)
(b/'reference').mkdir(exist_ok=True)
for name in ['Northcott.lean','Basic.lean']:shutil.copy2(r/'refer/iut/Iut/Tripod'/name,b/'reference'/name)
shutil.copy2(d/'audit/Checks.lean',w/'Solutions/Checks_TripodNorthcottSourceProofs.lean');f='Solutions/Checks_TripodNorthcottSourceProofs.lean';files[f]=hashlib.sha256((w/f).read_bytes()).hexdigest()
old=w/'.local/adaptation/derivative-finite-sourceproof-20261114';graph=(old/'ExtractDerivativeProofGraph.lean').read_text().replace('import Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_noncriticalDerivativeBadPlacesFinite','import Theorems.Thm_AbcAdaptation_Tripod_boundedDegreeFiniteness').replace('derivative-finite-sourceproof-20261114','northcott-sourceproof-20261114');(b/'ExtractNorthcottProofGraph.lean').write_text(graph);shutil.copy2(old/'ProductionGates.lean',b/'ProductionGates.lean')
(b/'integration.json').write_text(json.dumps({'input_head':subprocess.check_output(['git','-C',str(r),'rev-parse','HEAD'],text=True).strip(),'files':files,'scope':'Complete exact archived Northcott source proof reuse and five meaningful mathematical nodes; no new open debt','parent_target_preserved':True,'reference_revision_limit':manifest['reference_iut']['upstream_revision_verification']},ensure_ascii=False,indent=2)+'\n')
print(json.dumps({'integrated':list(files),'evidence':str(b)},ensure_ascii=False))
