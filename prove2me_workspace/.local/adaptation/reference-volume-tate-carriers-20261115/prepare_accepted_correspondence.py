#!/usr/bin/env python3
"""Bind accepted identities to an actual successful audit. No compiler, CI, API, network, or Git calls."""
import argparse,hashlib,json,math
from pathlib import Path

SELECTED=100
NAMED_SELECTED=98
PROOF_PARENTS={
 'TateCurvesTheta.OrderedTateParameter.decidable._proof_1':'TateCurvesTheta.OrderedTateParameter.decidable',
 'TateCurvesTheta.PrimeToOrder.decidable._proof_1':'TateCurvesTheta.PrimeToOrder.decidable'}
TARGET_ONLY={
 'AbcAdaptation.Reference.TateCurvesTheta.OrderedTateParameter.decidable._aux_1',
 'AbcAdaptation.Reference.TateCurvesTheta.PrimeToOrder.decidable._aux_1'}
STANDARD={'propext','Classical.choice','Quot.sound'}

def read(p):return json.loads(Path(p).read_text())
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def axiom_name(s):
 result=[]
 for part in s.split('.'):
  result=[result,'str',part]
 return result
def json_sha(x):return hashlib.sha256(json.dumps(x,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode()).hexdigest()
def require(ok,msg):
 if not ok:raise ValueError(msg)
def unique(rows,key,label):
 result={}
 for row in rows:
  require(row[key] not in result,'Duplicate '+label+': '+row[key]);result[row[key]]=row
 return result

def prepare(unit,receipt_path,audit_path,wrapper_path,expected_job=None):
 unit=unit.resolve();workspace=unit.parents[2]
 receipt=read(receipt_path);audit=read(audit_path);config=read(unit/'audit-config.json');wrappers=read(wrapper_path)
 require(receipt['status']=='succeeded' and receipt['result']['exit_code']==0,'Audit receipt did not succeed')
 if expected_job:require(receipt['job_id']==expected_job,'Unexpected audit job')
 req=receipt['request'];result=receipt['result'];snapshot=result['snapshot']
 require(Path(req['workspace']).resolve()==workspace and req['exclusive'] is True,'Wrong audit workspace/exclusivity')
 require(req['task_type']=='review' and req['target']=='file','Wrong audit task type or target')
 require(snapshot['workspace_mode']=='exclusive_worktree' and snapshot['snapshot_id'] is None,'Wrong audit workspace mode')
 source=(workspace/req['parameters']['source']).resolve()
 require(source==unit/'AuditNextCarriers.lean','Wrong audited source')
 manifest=req['worktree_manifest'];require(sha(source)==manifest['source_sha256'],'Auditor source changed')
 for p,h in manifest['input_hashes'].items():require(sha(p)==h,'Audit input changed: '+p)
 require(str(unit/'audit-config.json') in manifest['input_hashes'],'Receipt does not bind audit configuration')
 require(str(unit/'original-exprs.json') in manifest['input_hashes'],'Receipt does not bind original expressions')
 require(audit['configuration']==config,'Actual audit configuration differs from frozen current configuration')
 require(audit['schema']=='next-carrier-kernel-audit-v3','Unexpected audit schema')
 require(audit['compilerVersion']=='4.33.1' and audit['originalCompilerVersion']=='4.35.0-rc3','Wrong compiler versions')
 require(not audit['hasSorryAx'] and audit['allOwnedTypeValueClosuresStandardAxiomsOnly'],'Audit axiom closure failed')
 expected_dimensions={'requiredSourceDeclarationCount':SELECTED,'requiredResolvedCount':SELECTED,
  'requiredEliminatedInternalProofCount':2,'requiredNamedComparedCount':NAMED_SELECTED,
  'requiredProofValueResolutionCount':2,'requiredComparedCount':SELECTED}
 for k,v in expected_dimensions.items():require(audit[k]==v,'Wrong actual dimension '+k)
 require(config['expectedRecordCount']==147 and config['expectedSelectedCount']==SELECTED and config['expectedNamedSelectedCount']==NAMED_SELECTED and config['expectedProofValueResolutionCount']==2,'Wrong configured dimensions')
 original=read(unit/'original-exprs.json');sources=unique(original['records'],'name','original record')
 require(len(sources)==147 and original['selectedCount']==SELECTED,'Wrong original declaration inventory')
 require(original['inventorySha256']==config['inventorySha256'] and original['graphSha256']==config['graphSha256'],'Original inventory provenance changed')
 selected={n for n,r in sources.items() if r['selected']};require(len(selected)==SELECTED,'Wrong actual selected set')
 comparisons=unique(audit['comparisons'],'original','compared original');targets=unique(audit['comparisons'],'target','compared target')
 resolutions=unique(audit['proofValueResolutions'],'original','proof value')
 require(set(resolutions)==set(PROOF_PARENTS),'Wrong genuine original proof value set')
 require(not set(resolutions)&set(comparisons),'A proof value is incorrectly given a standalone target identity')
 require({n for n in comparisons if sources[n]['selected']}==selected-set(resolutions),'Selected named/proof-value partition is incomplete')
 require(len(selected-set(resolutions))==NAMED_SELECTED,'Wrong named selected count')
 owned=unique(audit['ownedDeclarations'],'name','owned target')
 for n,r in owned.items():
  require(not r['hasSorryAx'],'Owned declaration contains sorryAx: '+n)
  for k in ['axioms','typeAxioms','valueAxioms']:require(set(r[k])<=STANDARD,'Unexpected owned axiom: '+n)
 require(set(audit['targetOnlyCompilerDeclarations'])==TARGET_ONLY and len(audit['targetOnlyCompilerDeclarations'])==2,'Wrong exact target-only declarations')
 require(set(owned)==set(targets)|TARGET_ONLY and not set(targets)&TARGET_ONLY,'Actual target-owned partition differs')
 require(set(config['expectedTargetOnlyCompilerDeclarations'])==TARGET_ONLY,'Wrong target-only configuration')
 require(set(audit['missingUnselectedOriginalDeclarations'])==set(sources)-set(comparisons)-set(resolutions),'Missing optional originals are not exact')
 require(not set(audit['missingUnselectedOriginalDeclarations'])&selected,'Selected declaration is missing')
 for n,r in comparisons.items():
  require(r['sourceRecord']==sources[n],'Compared source record differs: '+n)
  for k in ['kernelTypeEqual','allExpressionBinderInfoEqual','binderInfoPlacementEqual','computationShapeEqual','completeStructureMetadataEqual','instanceRegistryMatchesAcceptedGraph','sourceAxiomInventoryMatchesAcceptedGraph']:
   require(r[k] is True,'Actual comparison check failed '+k+': '+n)
  require(r['expectedIsInstance']==sources[n]['isInstance'],'Instance status differs: '+n)
  if not r['proofDeclaration'] and sources[n]['valueExpr'] is not None:
   require(r['computationalValueEqualityChecked'] and (r['kernelValueEqual'] or r['kernelPropositionalValueEquality']),'Whole computational value not compared: '+n)
  require(len(sources[n]['recursorRuleRhs'])==r['recursorRulesCompared'],'Recursor rules not fully compared: '+n)
  require(r['target'] in owned,'Compared target has no owned audit: '+n)
 for n,r in resolutions.items():
  require(r['sourceRecord']==sources[n] and sources[n]['selected'],'Genuine proof source differs: '+n)
  require(r['resolution']=='genuine-exported-original-proof-value' and r['standaloneTargetIdentity'] is None,'Invented proof-to-target identity: '+n)
  require(r['parentOriginal']==PROOF_PARENTS[n],'Wrong proof parent: '+n)
  for k in ['originalTypeBinderInfoPreserved','exactOriginalTypeKernelChecked','genuineOriginalValueInhabitsExactOriginalType','parentWholeValueEqualityRequired','expandedDependenciesHaveAllowedOwners']:
   require(r[k] is True,'Genuine proof value check failed '+k+': '+n)
  require(r['hasSorryAx'] is False and set(r['expandedTypeAxioms'])<=STANDARD and set(r['expandedValueAxioms'])<=STANDARD,'Genuine proof axiom check failed: '+n)
  parent=comparisons[r['parentOriginal']]
  require(parent['computationalValueEqualityChecked'] and (parent['kernelValueEqual'] or parent['kernelPropositionalValueEquality']),'Proof parent lacks whole-value equality: '+n)
 provenance=unique(config['targetOnlyCompilerProvenance'],'target','target-only provenance')
 require(set(provenance)==TARGET_ONLY,'Target-only provenance differs')
 for n,r in provenance.items():
  require(r['targetIdentityForSourceProof'] is False and r['ownerAxiomAuditRequired'] is True and r['wholeParentValueEqualityRequired'] is True,'Target-only helper falsely identifies a source proof: '+n)
  require(r['sourceParentOriginal'] in comparisons,'Target-only parent is not actually compared: '+n)
 # Save identities from comparisons only. Preserve optional actual comparisons separately.
 named=[]
 for n,r in comparisons.items():
  s=sources[n]
  named.append({'original':n,'originalName':r['originalName'],'target':r['target'],'targetName':r['targetName'],
   'targetToSourceUniverseIndices':r['targetToSourceUniverseIndices'],'expectedIsInstance':r['expectedIsInstance'],
   'expectedSourceAxioms':[axiom_name(ax) for ax in s['axioms']],'sourceAxiomNames':s['axioms'],'sourceOwner':s['module'],'acceptedJob':receipt['job_id'],
   'sourceSelected':s['selected'],'comparisonScope':'mandatory-selected' if s['selected'] else 'actual-unselected-compiler-declaration'})
 selected_pairs=[r for r in named if r['sourceSelected']];unselected_pairs=[r for r in named if not r['sourceSelected']]
 for r in wrappers['bundles']:
  require(sha(r['path'])==r['sha256'],'Final wrapper changed: '+r['module'])
  require((workspace/'Definitions'/Path(r['path']).name).read_bytes()==Path(r['path']).read_bytes(),'Installed wrapper differs: '+r['module'])
 resources=receipt.get('resources') or {};cpu,user,system=[resources.get(k) for k in ['cpu_time_seconds','cpu_user_seconds','cpu_system_seconds']]
 if cpu is not None and user is not None and system is not None:require(math.isclose(cpu,user+system,abs_tol=0.1),'CPU total differs from user plus system')
 return {'schema':'reference-volume-tate-accepted-compiler-correspondence-v1','status':'accepted-kernel-audit',
  'job_id':receipt['job_id'],'receipt':str(receipt_path.resolve()),'receiptSha256':sha(receipt_path),
  'audit':str(audit_path.resolve()),'auditSha256':sha(audit_path),'sourceSelectedCount':SELECTED,
  'actualNamedComparisons':len(named),'selectedNamedComparisons':len(selected_pairs),'unselectedNamedComparisons':len(unselected_pairs),
  'internalProofValueResolutions':len(resolutions),'sourceObligationsResolved':len(selected_pairs)+len(resolutions),
  'namedPairs':named,'selectedNamedPairs':selected_pairs,'unselectedNamedPairs':unselected_pairs,
  'proofValueResolutions':audit['proofValueResolutions'],'missingUnselectedOriginalDeclarations':audit['missingUnselectedOriginalDeclarations'],
  'targetOnlyCompilerDeclarations':audit['targetOnlyCompilerDeclarations'],
  'targetOnlyCompilerProvenance':[{k:v for k,v in r.items() if k!='actualCompilerRecord'}|{'actualCompilerRecordSha256':json_sha(r['actualCompilerRecord'])} for r in provenance.values()],
  'proofIdentityPolicy':'The two genuine original _proof_1 values have no standalone target identity. The two target _aux_1 declarations are independently owned target-only helpers. No _proof_1 to _aux_1 rename is asserted.',
  'candidateMapPolicy':'Only actual compiler comparisons establish named identities. Unselected actual comparisons remain distinct from mandatory selected obligations; raw candidate maps establish no identity.',
  'wrapperReport':{'path':str(wrapper_path.resolve()),'sha256':sha(wrapper_path)},
  'auditSource':{'path':str(source),'sha256':sha(source)},'auditConfiguration':{'path':str(unit/'audit-config.json'),'sha256':sha(unit/'audit-config.json')},
  'actualArguments':result['actual_arguments'],'workspaceMode':snapshot['workspace_mode'],
  'resources':{k:resources.get(k) for k in ['wall_time_seconds','cpu_time_seconds','cpu_user_seconds','cpu_system_seconds','peak_rss_bytes','peak_pss_bytes','source','degraded']}}

def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--unit',required=True,type=Path);p.add_argument('--receipt',required=True,type=Path);p.add_argument('--audit',type=Path);p.add_argument('--wrapper-report',type=Path);p.add_argument('--expected-job');p.add_argument('--out',required=True,type=Path);a=p.parse_args()
 require(not a.out.exists(),'Refuse to overwrite an accepted correspondence')
 data=prepare(a.unit,a.receipt,a.audit or a.unit/'kernel-audit/next-carrier-kernel-audit.json',a.wrapper_report or a.unit/'generated-wrapped/foundation-wrapper-report.json',a.expected_job)
 a.out.parent.mkdir(parents=True,exist_ok=True);a.out.write_text(json.dumps(data,ensure_ascii=False,indent=2)+'\n')
 print(json.dumps({k:data[k] for k in ['status','job_id','sourceSelectedCount','actualNamedComparisons','selectedNamedComparisons','unselectedNamedComparisons','internalProofValueResolutions','sourceObligationsResolved']}))

if __name__=='__main__':main()
