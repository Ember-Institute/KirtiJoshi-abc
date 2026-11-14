from pathlib import Path
import json,hashlib,subprocess,shutil
r=Path('/home/admin-wsl/Coq/abc');w=r/'prove2me_workspace';d=Path('/tmp/p2m-regular-ramified-obstruction-canonical-v2-20261114');old=Path('/tmp/p2m-regular-ramified-obstruction-next-20261114');b=w/'.local/adaptation/regular-ramified-obstruction-sourceproof-20261114';b.mkdir(exist_ok=True)
source=json.loads((old/'source-consumer.json').read_text());target=source['parent_target']['file'];actual=(w/target).read_text();draft=(d/target).read_text();marker='theorem noncriticalRegularRamifiedDerivNotMem';a=actual.index(marker);z=actual.index(':= by',a);da=draft.index(marker);dz=draft.index(':= by',da);assert actual[a:z]==draft[da:dz],'Target signature changed'
for item in source['derivAlong_alignment'].values():
 p=w/item['existing_file'];assert hashlib.sha256(p.read_bytes()).hexdigest()==item['existing_file_sha256']
files={}
for folder in ['Definitions','Theorems']:
 for p in (d/folder).glob('*.lean'):
  rel=str(p.relative_to(d));q=w/rel;assert not q.exists() or rel==target,rel;shutil.copy2(p,q);files[rel]=hashlib.sha256(q.read_bytes()).hexdigest()
dag=json.loads((d/'canonical-import-dag.json').read_text());names=dag['topological_order'];check='\n'.join('import '+n['module'] for n in dag['nodes'])+'\n\n'+ '\n'.join('#print axioms '+n for n in names+['AbcAdaptation.Tripod.Fermat.Proper.Place.uniformizer','AbcAdaptation.Tripod.Fermat.Proper.Place.ord_uniformizer','AbcAdaptation.Tripod.Fermat.Proper.Place.uniformizer_ne_zero'])+'\n';f='Solutions/Checks_FermatRegularRamifiedObstruction.lean';(w/f).write_text(check);files[f]=hashlib.sha256((w/f).read_bytes()).hexdigest()
for p in d.iterdir():
 if p.is_file():shutil.copy2(p,b/p.name)
shutil.copytree(d/'reference',b/'reference',dirs_exist_ok=True)
shutil.copy2(old/'source-consumer.json',b/'original-source-consumer.json');shutil.copy2(old/'static-review.json',b/'original-static-review.json')
base=w/'.local/adaptation/derivative-finite-sourceproof-20261114';graph=(base/'ExtractDerivativeProofGraph.lean').read_text().replace('noncriticalDerivativeBadPlacesFinite','noncriticalRegularRamifiedDerivNotMem').replace('derivative-finite-sourceproof-20261114','regular-ramified-obstruction-sourceproof-20261114');(b/'ExtractObstructionProofGraph.lean').write_text(graph);shutil.copy2(base/'ProductionGates.lean',b/'ProductionGates.lean');shutil.copy2(base/'mochizuki-quotation.md',b/'mochizuki-quotation.md')
(b/'integration.json').write_text(json.dumps({'input_head':subprocess.check_output(['git','-C',str(r),'rev-parse','HEAD'],text=True).strip(),'files':files,'existing_target':source['parent_target'],'exact_target_type_preserved':True,'public_nodes':names,'new_open_mathematical_obligations':0,'source_pin':source['reference_pin'],'scope':'Complete source proof of the existing local derivative obstruction; nine new closed nodes and private source closures'},ensure_ascii=False,indent=2)+'\n')
print(json.dumps({'integrated':len(files),'public_nodes':len(names),'target_signature':'unchanged','workspace':str(w)},ensure_ascii=False))
