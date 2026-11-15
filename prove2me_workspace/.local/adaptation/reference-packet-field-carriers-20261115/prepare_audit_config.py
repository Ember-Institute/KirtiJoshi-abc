#!/usr/bin/env python3
"""Produce configurable audit inputs; no compile, CI, Git, API or main writes."""
from pathlib import Path
import argparse,hashlib,json
HERE=Path(__file__).resolve().parent
BASE=Path('/home/admin-wsl/Coq/abc/prove2me_workspace/.local/adaptation/foundation-reference-carriers-20261115')
DEFAULT_INV=Path('/tmp/p2m-next-carrier-inventory-v3-20261115')
STANDARD=['Init','Lean','Std','Mathlib','Batteries','Aesop','Qq','Plausible','ProofWidgets','ImportGraph','Cli','LeanSearchClient']
ALLOWED_AXIOMS={'propext','Classical.choice','Quot.sound'}
def load(p):return json.loads(Path(p).read_text())
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def name(n):
 v=[]
 for part in n.split('.'):v=[v,'str',part]
 return v
def target_module(n):return 'Definitions.Def_AbcAdaptation_Reference_'+n.replace('.','_')
def dump(p,v):Path(p).write_text(json.dumps(v,indent=2,ensure_ascii=False)+'\n')
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--inventory-dir',type=Path,default=DEFAULT_INV);ap.add_argument('--output',type=Path,default=HERE/'audit-config.json');ap.add_argument('--original-exprs',type=Path);ap.add_argument('--audit-output',type=Path);ap.add_argument('--wrapper-report',type=Path);a=ap.parse_args()
 invpath=a.inventory_dir/'inventory.json';inv=load(invpath);ex=load(a.inventory_dir/'export-config.json');imports=load(a.inventory_dir/'imports.json');dep=load(a.inventory_dir/'dependency-closure.json')
 assert sha(invpath)==ex['inventorySha256']
 assert inv['graphSha256']==ex['graphSha256']==dep['graphSha256']
 prior_config=load(BASE/'audit-config.json');prior_inv=load(BASE/'inventory.json');prior_audit=load(dep['priorKernelAuditPath'])
 receipt_path=BASE/'kernel-audit-v2-result.json';receipt=load(receipt_path)
 assert receipt['job_id']=='ci-013377-98675e26' and receipt['status']=='succeeded' and receipt['result']['exit_code']==0
 assert receipt['result']['snapshot']['workspace_mode']=='exclusive_worktree' and receipt['result']['snapshot']['snapshot_id'] is None
 assert prior_audit['hasSorryAx'] is False
 for bundle in dep['importedBundles']:
  assert sha(bundle['file'])==bundle['sha256'],('current delivered source hash changed',bundle['file'])
 assert sha(dep['priorKernelAuditPath'])==dep['priorKernelAuditSha256']
 assert sha(dep['priorInventory'])==dep['priorInventorySha256']
 assert sha(dep['priorMap'])==dep['priorMapSha256']
 previous={d['name']:d for m in prior_inv['modules'] for d in m['declarations']}
 current={d['name']:d for m in inv['modules'] for d in m['declarations']}
 assert not set(previous)&set(current)
 graph={**previous,**current}
 pm=[]
 for row in prior_config['projectMap']:
  r=dict(row);d=previous[r['original']];r['mappingRole']='prior-delivered-candidate';r['expectedSourceAxioms']=[name(ax) for ax in d['axioms']];pm.append(r)
 for record in ex['records']:
  n=record['name'];d=current[n];target='AbcAdaptation.Reference.'+n
  assert not d['hasSorryAx'] and set(d['axioms'])<=ALLOWED_AXIOMS
  pm.append({'original':n,'originalName':record['nameExpr'],'target':target,'targetName':name(target),'required':record['selected'],'mappingRole':'current-unit','targetToSourceUniverseIndices':None,'expectedIsInstance':d['isInstance'],'expectedSourceAxioms':[name(ax) for ax in d['axioms']]})
 assert len(pm)==len({r['original'] for r in pm})==len({r['target'] for r in pm})==347
 prior_available={p['original'] for p in prior_audit['comparisons']}
 assert set(dep['requiredPriorConstants'])<=prior_available
 for r in pm:
  if r['mappingRole'].startswith('prior'):
   r['previouslyAcceptedPresent']=r['original'] in prior_available
   if r['previouslyAcceptedPresent']:r['mappingRole']='prior-delivered-present'
 bymodule={r['module']:r for r in imports}
 wrapper={r['module']:r for r in load(a.wrapper_report)['bundles']} if a.wrapper_report else None
 modules=[]
 for m in inv['modules']:
  planned=list(dict.fromkeys(bymodule[m['module']]['platform433Candidates']))
  actual=wrapper[m['module']]['platformImports'] if wrapper else planned
  assert len(actual)==len(set(actual)) and 'Mathlib' not in actual
  assert all(p in planned for p in actual),('unreviewed module',m['module'],set(actual)-set(planned))
  modules.append({'original':m['module'],'source':m['source'],'sourceSha256':m['sourceSha256'],'normalizedSha256':m['normalizedSha256'],'target':target_module(m['module']),'allowedDirectImports':actual,'importPolicy':'exact explicit module set; implicit Init imports are accounted for separately','sourceProvenance':m['provenance']})
 evidence=[{'path':str(p.resolve()),'sha256':sha(p)} for p in [invpath,a.inventory_dir/'export-config.json',a.inventory_dir/'imports.json',a.inventory_dir/'dependency-closure.json',BASE/'audit-config.json',Path(dep['priorKernelAuditPath']),Path(dep['priorMap']),receipt_path]+[Path(b['file']) for b in dep['importedBundles']]]
 if a.wrapper_report:evidence.append({'path':str(a.wrapper_report.resolve()),'sha256':sha(a.wrapper_report)})
 config={'schema':'next-carrier-kernel-audit-config-v3','inventorySha256':ex['inventorySha256'],'graphSha256':ex['graphSha256'],'expectedRecordCount':ex['expectedRecordCount'],'expectedSelectedCount':ex['expectedSelectedCount'],'expectedModuleCount':len(modules),'outputDir':str((a.audit_output or HERE/'kernel-audit').resolve()),'originalExprFile':str((a.original_exprs or Path(ex['outputFile'])).resolve()),'modules':modules,'allowedDependencyModules':[name(m['target']) for m in prior_config['modules']],'standardModulePrefixes':[name(n) for n in STANDARD],'projectPrefixes':[name(n) for n in ['Iut','TateCurvesTheta','Genl','AbcAdaptation','Definitions','Theorems','Solutions']],'originalProjectPrefixes':[name(n) for n in ['Iut','TateCurvesTheta','Genl']],'targetProjectPrefix':name('AbcAdaptation.Reference'),'projectMap':pm,'standardRenames':[],'standardRenamePolicy':'No standard constant renames accepted; use separate reviewed compiler/source evidence before adding one.','priorBundleEvidence':{'originalConstantCandidates':151,'acceptedPresentConstants':len(prior_available),'absentUnselectedCandidates':151-len(prior_available),'requiredPriorConstants':dep['requiredPriorConstants'],'bundles':dep['importedBundles'],'acceptedKernelJob':receipt['job_id'],'acceptedKernelReceipt':{'path':str(receipt_path),'sha256':sha(receipt_path)},'acceptedAuditJson':{'path':dep['priorKernelAuditPath'],'sha256':dep['priorKernelAuditSha256']}},'inputEvidence':evidence,'importPlanStatus':'bound to wrapper report' if wrapper else 'candidate plan; regenerate with --wrapper-report after accepting exact imports'}
 assert all(not d['hasSorryAx'] and set(d['axioms'])<=ALLOWED_AXIOMS for d in graph.values())
 a.output=a.output.resolve();assert HERE==a.output.parent or HERE in a.output.parents,'output outside task directory'
 dump(a.output,config)
 axiom_inventory={'schema':'next-carrier-source-axiom-inventory-v3','graphSha256':ex['graphSha256'],'inventorySha256':ex['inventorySha256'],'standardAxioms':sorted(ALLOWED_AXIOMS),'hasSorryAx':False,'newModuleCount':len(modules),'newDeclarationCount':len(current),'newSelectedDeclarationCount':sum(bool(d['selectedForBundle']) for d in current.values()),'declarations':[{'name':n,'module':d['module'],'selected':d['selectedForBundle'],'isInstance':d['isInstance'],'axioms':d['axioms'],'hasSorryAx':d['hasSorryAx']} for n,d in sorted(current.items())]}
 dump(HERE/'source-axiom-inventory.json',axiom_inventory)
 print(json.dumps({'config':str(a.output),'sha256':sha(a.output),'newDeclarations':len(current),'projectMap':len(pm),'priorAcceptedPresent':len(prior_available),'newSelected':ex['expectedSelectedCount'],'moduleDirectImportCounts':{m['original']:len(m['allowedDirectImports']) for m in modules}},indent=2))
if __name__=='__main__':main()
