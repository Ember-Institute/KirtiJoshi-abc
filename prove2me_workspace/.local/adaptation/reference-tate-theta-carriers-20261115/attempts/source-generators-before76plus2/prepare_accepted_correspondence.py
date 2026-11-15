#!/usr/bin/env python3
"""Bind this four-module unit to a real successful kernel audit only.

No compiler, CI, API, network or Git calls. Raw original Expr JSON is streamed
for SHA256 only. The compiler audit binds the lossless compact Expr input.
No candidate mapping or proposed generated declaration Name establishes identity.
"""
import argparse,hashlib,json,math
from pathlib import Path
SELECTED=78
RECORDS=117
STANDARD={'propext','Classical.choice','Quot.sound'}
MODULES={'TateCurvesTheta.TateCurve.JInvariant','TateCurvesTheta.TateCurve.Parametrization','Iut.Cor312.ThetaData.AdmissiblePrime','Iut.Cor312.ThetaData.TateStructure'}
def read(p):return json.loads(Path(p).read_text())
def sha(p):
 h=hashlib.sha256()
 with Path(p).open('rb') as f:
  for block in iter(lambda:f.read(8*1024*1024),b''):h.update(block)
 return h.hexdigest()
def require(ok,msg):
 if not ok:raise ValueError(msg)
def unique(rows,key,label):
 out={}
 for r in rows:
  require(r[key] not in out,'Duplicate '+label+': '+r[key]);out[r[key]]=r
 return out
def axiom_name(s):
 result=[]
 for part in s.split('.'):result=[result,'str',part]
 return result
def name_parts(n):
 if n==[]:return []
 require(isinstance(n,list) and len(n)==3 and n[1] in ['str','num'],'Invalid actual structural Name')
 require(isinstance(n[2],str) if n[1]=='str' else isinstance(n[2],int) and n[2]>=0,'Invalid actual Name component')
 return name_parts(n[0])+[(n[1],n[2])]
def name_text(n):return '.'.join(str(v) for k,v in name_parts(n))

def prepare(unit,receipt_path,audit_path,wrapper_path,expected_job=None):
 unit=unit.resolve();workspace=unit.parents[2]
 receipt=read(receipt_path);config=read(unit/'audit-config.json');wrappers=read(wrapper_path);inv=read(unit/'inventory.json')
 require({m['module'] for m in inv['modules']}==MODULES,'Wrong unit modules')
 require(receipt['status']=='succeeded' and receipt['result']['exit_code']==0,'Actual audit receipt did not succeed')
 if expected_job:require(receipt['job_id']==expected_job,'Unexpected actual audit job')
 req=receipt['request'];result=receipt['result'];snapshot=result['snapshot']
 require(Path(req['workspace']).resolve()==workspace and req['exclusive'] is True,'Wrong workspace/exclusivity')
 require(req['task_type']=='review' and req['target']=='file','Wrong audit task type/target')
 require(snapshot['workspace_mode']=='exclusive_worktree' and snapshot['snapshot_id'] is None,'Wrong workspace mode')
 source=(workspace/req['parameters']['source']).resolve();require(source==unit/'AuditNextCarriers.lean','Wrong audited Lean source')
 manifest=req['worktree_manifest'];require(sha(source)==manifest['source_sha256'],'Auditor source changed')
 for path,expected in manifest['input_hashes'].items():require(sha(path)==expected,'Frozen audit input changed: '+path)
 require(str(unit/'audit-config.json') in manifest['input_hashes'],'Receipt does not bind audit configuration')
 require(Path(config['originalExprFile']).resolve()==unit/'original-exprs.compact.json','Unexpected actual Expr input')
 require(config['originalExprFile'] in manifest['input_hashes'],'Receipt does not bind actual compact Expr input')
 view=config['originalExprSerializationView'];acceptance=read(unit/'original-exprs-acceptance.json')
 require(view['status']=='lossless-serialization-view-not-new-compiler-evidence','Unexpected serialization view status')
 require(view['preservation']['completeLexicalTokenStreamsCompared'] and view['preservation']['onlyWhitespaceOutsideJsonStringsRemoved'] and view['preservation']['allExprNameBinderMetadataAndRecordValuesUnchanged'],'Lossless serialization proof missing')
 for role in ['raw','compact']:require(sha(view[role]['path'])==view[role]['sha256'],'Expr '+role+' bytes changed')
 require(view['compact']['path']==config['originalExprFile'],'Audit compact input differs from proven view')
 require(acceptance['status']=='accepted' and acceptance['originalExprsSha256']==view['raw']['sha256'],'Original source Expr acceptance differs')
 require(sha(acceptance['compilerReceiptPath'])==acceptance['compilerReceiptSha256'],'Original compiler receipt changed')
 original_receipt=read(acceptance['compilerReceiptPath']);require(original_receipt['status']=='succeeded' and original_receipt['result']['exit_code']==0 and original_receipt['job_id']==acceptance['job_id'],'Original compiler export did not succeed')
 require(sha(unit/'inventory.json')==config['inventorySha256']==acceptance['inventorySha256'] and sha(inv['graph'])==config['graphSha256'],'Source inventory/graph provenance changed')
 require(config['expectedRecordCount']==RECORDS and config['expectedSelectedCount']==config['expectedNamedSelectedCount']==SELECTED and config['expectedProofValueResolutionCount']==0 and config['expectedModuleCount']==4,'Wrong configured declaration dimensions')
 require(config['standardRenames']==[] and config['expectedTargetOnlyCompilerDeclarations']==[],'This reviewed unit permits no standard rename or target-only exceptions')
 audit=read(audit_path)
 require(audit['schema']=='next-carrier-kernel-audit-v3' and audit['configuration']==config,'Actual audit schema/config differs')
 require(audit['compilerVersion']=='4.33.1' and audit['originalCompilerVersion']=='4.35.0-rc3','Unexpected compiler versions')
 require(not audit['hasSorryAx'] and audit['allOwnedTypeValueClosuresStandardAxiomsOnly'],'Owned axiom closure failed')
 expected={'requiredSourceDeclarationCount':SELECTED,'requiredResolvedCount':SELECTED,'requiredEliminatedInternalProofCount':0,'requiredNamedComparedCount':SELECTED,'requiredProofValueResolutionCount':0,'requiredComparedCount':SELECTED}
 for k,v in expected.items():require(audit[k]==v,'Actual audit dimension differs: '+k)
 sources={d['name']:dict(d,sourceModule=m['module'],sourceSha256=m['sourceSha256']) for m in inv['modules'] for d in m['declarations']}
 require(len(sources)==RECORDS,'Not 117 source originals');selected={n for n,r in sources.items() if r['selected']};require(len(selected)==SELECTED,'Not 78 selected originals')
 comparisons=unique(audit['comparisons'],'original','actual compared original');targets=unique(audit['comparisons'],'target','actual compared target')
 require(audit['proofValueResolutions']==[],'Unexpected proof-value exceptions require a new explicit review; never invent a target identity')
 require(set(comparisons)<=set(sources) and {n for n in comparisons if sources[n]['selected']}==selected,'Selected actual named comparison partition differs')
 owned=unique(audit['ownedDeclarations'],'name','owned actual target')
 require(audit['targetOnlyCompilerDeclarations']==[] and set(owned)==set(targets),'Actual target ownership partition differs')
 for n,r in owned.items():
  require(not r['hasSorryAx'],'Owned sorryAx: '+n)
  for k in ['axioms','typeAxioms','valueAxioms']:require(set(r[k])<=STANDARD,'Unexpected owned axiom: '+n)
 missing=set(sources)-set(comparisons)
 require(set(audit['missingUnselectedOriginalDeclarations'])==missing and not missing&selected,'Actual missing optional set differs')
 # All originals, including unselected private numeric Names, stay in the source scope.
 private=[r for r in config['excludedOriginalDeclarations']]
 require(len(private)==6 and all(r['target'] is None and not sources[r['original']]['selected'] and ('num',0) in name_parts(r['originalName']) for r in private),'Six original numeric-private exclusions differ')
 named=[]
 for n,r in comparisons.items():
  original=sources[n];s=r['sourceRecord']
  require(s['name']==n and s['module']==original['sourceModule'] and s['sourceSha256']==original['sourceSha256'] and s['selected']==original['selected'],'Compared source provenance differs: '+n)
  require(s['isInstance']==original['isInstance'] and set(s['axioms'])==set(original['axioms']),'Compared source instance/axiom metadata differs: '+n)
  require(name_text(r['originalName'])==n and name_text(r['targetName'])==r['target'],'Actual compiler Name serialization differs: '+n)
  require(s['nameExpr']==r['originalName'],'Actual source compiler Name differs: '+n)
  for k in ['kernelTypeEqual','allExpressionBinderInfoEqual','binderInfoPlacementEqual','computationShapeEqual','completeStructureMetadataEqual','instanceRegistryMatchesAcceptedGraph','sourceAxiomInventoryMatchesAcceptedGraph']:require(r[k] is True,'Actual comparison failed '+k+': '+n)
  require(r['expectedIsInstance']==s['isInstance'],'Actual instance status differs: '+n)
  if not r['proofDeclaration'] and s['valueExpr'] is not None:require(r['computationalValueEqualityChecked'] and (r['kernelValueEqual'] or r['kernelPropositionalValueEquality']),'Whole computational value not compared: '+n)
  require(len(s['recursorRuleRhs'])==r['recursorRulesCompared'],'Recursor rules not fully compared: '+n)
  named.append({'original':n,'originalName':r['originalName'],'target':r['target'],'targetName':r['targetName'],'targetToSourceUniverseIndices':r['targetToSourceUniverseIndices'],'expectedIsInstance':r['expectedIsInstance'],'expectedSourceAxioms':[axiom_name(ax) for ax in s['axioms']],'sourceAxiomNames':s['axioms'],'sourceOwner':s['module'],'acceptedJob':receipt['job_id'],'sourceSelected':s['selected'],'comparisonScope':'mandatory-selected' if s['selected'] else 'actual-unselected-compiler-declaration'})
 require(wrappers['definitionsBundleCount']==len(wrappers['bundles'])==4 and wrappers['selectedConstantCount']==SELECTED,'Wrapper dimensions differ')
 for w in wrappers['bundles']:
  require(sha(w['path'])==w['sha256'],'Audited wrapper changed: '+w['module'])
  require((workspace/'Definitions'/Path(w['path']).name).read_bytes()==Path(w['path']).read_bytes(),'Installed wrapper differs: '+w['module'])
 resources=receipt.get('resources') or {};cpu,user,system=[resources.get(k) for k in ['cpu_time_seconds','cpu_user_seconds','cpu_system_seconds']]
 if cpu is not None and user is not None and system is not None:require(math.isclose(cpu,user+system,abs_tol=0.1),'CPU total differs from user plus system')
 selected_pairs=[r for r in named if r['sourceSelected']];unselected_pairs=[r for r in named if not r['sourceSelected']]
 return {'schema':'reference-tate-theta-accepted-compiler-correspondence-v1','status':'accepted-kernel-audit','job_id':receipt['job_id'],
  'receipt':str(receipt_path.resolve()),'receiptSha256':sha(receipt_path),'audit':str(audit_path.resolve()),'auditSha256':sha(audit_path),
  'sourceSelectedCount':SELECTED,'actualNamedComparisons':len(named),'selectedNamedComparisons':len(selected_pairs),'unselectedNamedComparisons':len(unselected_pairs),'internalProofValueResolutions':0,'sourceObligationsResolved':len(selected_pairs),
  'namedPairs':named,'selectedNamedPairs':selected_pairs,'unselectedNamedPairs':unselected_pairs,'proofValueResolutions':[],
  'missingUnselectedOriginalDeclarations':audit['missingUnselectedOriginalDeclarations'],'targetOnlyCompilerDeclarations':[],'targetOnlyCompilerProvenance':[],
  'proofIdentityPolicy':'This actual accepted audit has no internal proof-value exceptions and no target-only declarations. Only actual compiler comparisons establish named identities.',
  'candidateMapPolicy':'Raw candidate generated-name maps establish no identity. Actual optional unselected comparisons remain separate from 78 mandatory selected source obligations.',
  'wrapperReport':{'path':str(wrapper_path.resolve()),'sha256':sha(wrapper_path)},'auditSource':{'path':str(source),'sha256':sha(source)},'auditConfiguration':{'path':str(unit/'audit-config.json'),'sha256':sha(unit/'audit-config.json')},
  'originalExprSerializationView':view,'actualArguments':result['actual_arguments'],'workspaceMode':snapshot['workspace_mode'],
  'resources':{k:resources.get(k) for k in ['wall_time_seconds','cpu_time_seconds','cpu_user_seconds','cpu_system_seconds','peak_rss_bytes','peak_pss_bytes','source','degraded']}}
def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--unit',required=True,type=Path);p.add_argument('--receipt',required=True,type=Path);p.add_argument('--audit',type=Path);p.add_argument('--wrapper-report',type=Path);p.add_argument('--expected-job');p.add_argument('--out',required=True,type=Path);a=p.parse_args()
 require(not a.out.exists(),'Refuse to overwrite accepted correspondence')
 data=prepare(a.unit,a.receipt,a.audit or a.unit/'kernel-audit/next-carrier-kernel-audit.json',a.wrapper_report or a.unit/'generated-wrapped/foundation-wrapper-report.json',a.expected_job)
 a.out.parent.mkdir(parents=True,exist_ok=True);a.out.write_text(json.dumps(data,ensure_ascii=False,indent=2)+'\n')
 print(json.dumps({k:data[k] for k in ['status','job_id','sourceSelectedCount','actualNamedComparisons','selectedNamedComparisons','unselectedNamedComparisons','internalProofValueResolutions','sourceObligationsResolved']}))
if __name__=='__main__':main()
