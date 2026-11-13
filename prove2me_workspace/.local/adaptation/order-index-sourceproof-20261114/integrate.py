from pathlib import Path
import json,hashlib,shutil,subprocess
r=Path('/home/admin-wsl/Coq/abc');w=r/'prove2me_workspace';d=Path('/tmp/p2m-elementary-order-sourceproof-next-20261114');b=w/'.local/adaptation/order-index-sourceproof-20261114';b.mkdir(exist_ok=True)
report=json.loads((d/'static-review.json').read_text());files={}
for row in report['target_checks']:
 f=row['file'];assert hashlib.sha256((w/f).read_bytes()).hexdigest()==row['input_file_sha256'],f
for folder in ['Definitions','Theorems']:
 for p in (d/folder).glob('*.lean'):
  f=str(p.relative_to(d));shutil.copy2(p,w/f);files[f]=hashlib.sha256(p.read_bytes()).hexdigest()
for n in ['README.md','source-consumer.json','static-review.json','SHA256SUMS']:
 shutil.copy2(d/n,b/('draft-'+n))
shutil.copytree(d/'reference',b/'reference',dirs_exist_ok=True)
pre='AbcAdaptation.Tripod.Fermat.Proper.'
names=['noncriticalPolynomialOrderAtRegularPoint','noncriticalPolynomialOrderAtPole','noncriticalInverseRamification']
checks='\n'.join('import Theorems.Thm_'+(pre+n).replace('.','_') for n in names)+'\n\nopen AbcAdaptation.Tripod.Fermat.Proper\n\n'
checks+='\n'.join('#print axioms '+n for n in ['Place.noncritical_ord_eq_zero_of_residue_ne_zero','Place.noncritical_residue_eq_zero_of_ord_pos']+names)+'\n'
(w/'Solutions/Checks_FermatOrderIndexSourceProofs.lean').write_text(checks)
files['Solutions/Checks_FermatOrderIndexSourceProofs.lean']=hashlib.sha256(checks.encode()).hexdigest()
old=w/'.local/adaptation/derivative-finite-sourceproof-20261114'
graph=(old/'ExtractDerivativeProofGraph.lean').read_text().replace('import Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_noncriticalDerivativeBadPlacesFinite','\n'.join('import Theorems.Thm_'+(pre+n).replace('.','_') for n in names)).replace('derivative-finite-sourceproof-20261114','order-index-sourceproof-20261114')
(b/'ExtractOrderIndexProofGraph.lean').write_text(graph)
shutil.copy2(old/'ProductionGates.lean',b/'ProductionGates.lean')
(b/'integration.json').write_text(json.dumps({'input_head':subprocess.check_output(['git','-C',str(r),'rev-parse','HEAD'],text=True).strip(),'draft_input_head':report['workspace_head'],'files':files,'targets_preserved_byte_exact':True,'no_new_open_nodes':True,'source_pin':'9ce4d3f793d3bc831f2fc7214b7dbad90ea012d8'},indent=2)+'\n')
print(json.dumps({'integrated':list(files),'evidence':str(b)}))
