#!/usr/bin/env python3
"""Finalize two conditional finiteness proofs only after both four-role reviews and Proved GETs.
Writes only this /tmp directory; no CI, compiler, API, Git, deletion, or workspace edits.
"""
from pathlib import Path
import json,hashlib,tarfile,gzip
W=Path('/home/admin-wsl/Coq/abc/prove2me_workspace');A=W/'.local/adaptation';H=A/'main-chain-open-20261116';O=Path('/tmp/p2m-b1-field-finiteness-delivery-v154-20261117');DEST=A/'b1-field-finiteness-delivery-v154-20261117'
SRC=Path('/tmp/p2m-b1-curveof-field-properties-v148-20261117');BLIND=Path('/tmp/p2m-b1-torsion-field-finite-fresh-blind-v148-20261117');PUB=A/'b1-field-finiteness-publication-v151-20261117';AUD=A/'b1-field-finiteness-audit-v151-20261117'
LABELS=['torsionCoords_finite','finiteDimensional_fieldOfPrime']
def read(p):return json.loads(p.read_text())
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1024*1024),b''):h.update(b)
 return h.hexdigest()
def dump(p,j):p.write_text(json.dumps(j,ensure_ascii=False,indent=2)+'\n')
def nm(n):return '' if not n else (nm(n[0])+'.' if n[0] else '')+str(n[2])
def main():
 # All required final evidence is checked before archive creation.
 proven=read(SRC/'source-provenance.json');sourcewanted={t['sourceName']:t for t in proven['theorems']};assert len(sourcewanted)==2
 sourcefull={};reviewsummary={};pubsummary={};payloadEdits={}
 for label in LABELS:
  d=PUB/label;verify=read(d/'verify-result.json');get=read(d/'proved-readback.json');post=read(d/'publish-result.json')
  assert verify['status']=='ACCEPTED' and get['status']=='Proved' and verify['theorem_id']==get['theorem_id']==post['theorem_id']
  assert post['status']=='PUBLISHED' and get['visibility']=='private' and post['visibility']=='private'
  payload=read(d/'payload-final.json');original=read(d/'payload.json');cfg=read(AUD/label/'review.config.json');review=read(AUD/label/'actual/four-role-result.json')
  assert payload['formal_statement']==get['formal_statement']==cfg['exactFormalStatement']
  assert payload['preamble']==get['preamble']==cfg['exactPreamble']
  assert payload['private'] and payload['env']==get['mathlib_rev']=='0df444a360eaa60ab8c11dca51a86af692955474'
  assert review['allFourTYPEAndFullProofChecksPassed'] and review['allFourProofsSorryAxFree'] and len(review['fourRoles'])==4
  assert all(r['standardAxiomsOnly'] and not r['hasSorryAx'] for r in review['fourRoles'])
  # Preserve editorial original separately. Final binding changed only exact frozen Lean preamble/formal text.
  edits=[k for k in set(payload)|set(original) if payload.get(k)!=original.get(k)];assert set(edits)<={'preamble','formal_statement'},edits
  payloadEdits[label]={'changedFields':edits,'originalSHA256':sha(d/'payload.json'),'finalSHA256':sha(d/'payload-final.json'),'frozenExactPreambleAndFormalBoundByActualFourRole':True,'hypothesesPreserved':True,'failedAPISubmissionPerformed':False}
  sr=read(AUD/label/'source-root-full-actual-fact.json');assert sr==read(SRC/label/'source-root-full-actual-fact.json')
  assert sr['valueRead'] and sr['kernelValueTypeMatchesActualTYPE'];sourcefull[sr['name']]=sr
  reviewsummary[label]={'fourRoleTYPEAndFullProofChecksPassed':True,'sourceName':sr['name'],'sourceOriginalFullRecordSHA256':sha(AUD/label/'source-root-full-actual-fact.json'),'projectMapCount':len(cfg['projectMap']),'actualRoles':[{'role':r['role'],'standardAxiomsOnly':r['standardAxiomsOnly'],'hasSorryAx':r['hasSorryAx']} for r in review['fourRoles']]}
  pubsummary[label]={'theoremId':get['theorem_id'],'publicationJobId':post['id'],'proofSubmissionId':verify['id'],'proofStatus':'ACCEPTED','finalGETStatus':'Proved','formalName':get['theorem_name']}
 assert set(sourcefull)==set(sourcewanted)
 # Verify full original source JSON records against the old accepted closure, without duplicating its 136MB blob.
 closure=Path(next(x['path'] for x in proven['inputs'] if x['path'].endswith('closure-v111/actual-facts.jsonl')));matched=set()
 for line in closure.open():
  r=json.loads(line)
  if r.get('name') in sourcefull:assert r==sourcefull[r['name']];matched.add(r['name'])
 assert matched==set(sourcefull)
 original=Path(next(x['path'] for x in proven['inputs'] if x['path'].endswith('CurveOf.normalized.lean'))).read_bytes();byteChecks=[]
 for label,t in zip(LABELS,proven['theorems']):
  rr=t['sourceASTRange'];raw=original[rr['start']['offset']:rr['end']['offset']];assert hashlib.sha256(raw).hexdigest()==t['sourceCommandSHA256']
  canonical=W/f'Theorems/Thm_AbcAdaptation_Tripod_{label}.lean';solution=W/f'Solutions/Sol_AbcAdaptation_Tripod_{label}.lean'
  assert raw in canonical.read_bytes() and t['acceptedReplayHashMatches']
  e=t['solutionOnlyDeclIdReplacement'];assert raw[e['startWithinCommand']:e['endWithinCommand']].decode()==e['source']
  solraw=raw[:e['startWithinCommand']]+e['target'].encode()+raw[e['endWithinCommand']:];assert solraw in solution.read_bytes()
  byteChecks.append({'sourceName':t['sourceName'],'originalCommandSHA256':t['sourceCommandSHA256'],'canonicalFullStatementProofBytesRetained':True,'solutionOnlyDeclarationIdReplaced':True,'sourceFullActualRecordMatchesOldAcceptedClosure':True})
 blind=read(BLIND/'manifest.json');assert blind['english_original_frozen'] and sha(BLIND/'readback.en.raw.md')==blind['english_original_sha256']
 for f,h in blind['artifacts'].items():assert sha(BLIND/f)==h
 for r in blind['inputs'].values():assert sha(Path(r['path']))==r['sha256']
 files={}
 def add(p,m):
  assert p.is_file(),str(p)
  if m in files:assert files[m]==p
  files[m]=p
 for root,prefix in [(SRC,'source-draft'),(BLIND,'fresh-blind'),(PUB,'publication'),(AUD,'four-role-audit')]:
  for p in sorted(root.rglob('*')):
   if p.is_file() and '__pycache__' not in str(p) and p.name!='next-source-exact-dependency-facts.jsonl':add(p,prefix+'/'+str(p.relative_to(root)))
 for label in LABELS:
  for kind,prefix in [('Theorems','Thm'),('Solutions','Sol')]:
   p=W/kind/f'{prefix}_AbcAdaptation_Tripod_{label}.lean';add(p,'integrated-sources/'+str(p.relative_to(W)))
 for r in proven['inputs']:
  p=Path(r['path']);assert sha(p)==r['sha256']
  if r['bytes']<3_000_000:add(p,'small-source-inputs/'+p.name)
 # Include all actual leaf/artifact/four-role receipts and source hashes, including any eventual retry history.
 resultpaths=sorted(set(H.glob('b1-torsioncoords-finite*-result.json'))|set(H.glob('b1-fieldofprime-finite*-result.json')));assert len(resultpaths)>=10
 ci=[];prebuilt={}
 for p in resultpaths:
  j=read(p);label=p.name.removesuffix('-result.json');r=j['result'];snap=r['snapshot'];assert j['request']['exclusive'] and snap['workspace_mode']=='exclusive_worktree' and snap['snapshot_id'] is None
  for typ in ['request','submit','result']:add(H/(label+'-'+typ+'.json'),'ci/'+label+'-'+typ+'.json')
  for x in r.get('artifacts',[]):
   q=Path(x);add(q,'ci/artifacts/'+j['job_id']+'/'+q.name)
  res=j.get('resources',r.get('resources',{}));ci.append({'label':label,'jobId':j['job_id'],'status':j['status'],'exitCode':r['exit_code'],'inputSHA256':snap['manifest'].get('source_sha256'),'workspace':j['request']['workspace'],'workspaceMode':snap['workspace_mode'],'snapshotId':None,'exclusive':True,'actualArguments':r['actual_arguments'],'resources':{k:res.get(k) for k in ['wall_time_seconds','cpu_time_seconds','cpu_user_seconds','cpu_system_seconds','peak_rss_bytes','peak_pss_bytes']},'receiptMember':'ci/'+p.name,'receiptSHA256':sha(p),'diagnostics':r.get('diagnostics',[])})
  for path,h in snap['manifest'].get('input_hashes',{}).items():
   if path.endswith(('.olean','.ilean','.ir')):prebuilt[path]=h
  if res.get('cpu_time_seconds') is not None:assert abs(res['cpu_time_seconds']-res['cpu_user_seconds']-res['cpu_system_seconds'])<1e-7
 # Each theorem needs four successes (canonical/Sol leaf+artifact) and an accepted final four-role review.
 for token in ['torsioncoords-finite','fieldofprime-finite']:
  selected=[x for x in ci if token in x['label']];passed=[x for x in selected if x['status']=='succeeded' and x['exitCode']==0]
  assert len(passed)>=5
  assert any('four-role-review' in x['label'] and x['status']=='succeeded' for x in selected)
 prior=[]
 for unit,arcname in [('b1-existing-and-elliptic-delivery-v123-20261117','b1-existing-and-elliptic-evidence-v123.tar.gz'),('b1-arithmetic-delivery-v129-20261117','b1-arithmetic-evidence-v129.tar.gz')]:
  p=A/unit/arcname;mp=A/unit/'archive-manifest.json';mj=read(mp);assert sha(p)==mj['archiveSHA256']
  refs=[x for x in mj['files'] if any(z in x['path'] for z in ['root-source-facts-v106.json','closure-v111/actual-facts.jsonl','closure-v111/actual-edges.jsonl'])];prior.append({'archive':str(p),'archiveSHA256':mj['archiveSHA256'],'requiredMembers':refs,'priorLargeBlobsRepacked':False});add(mp,'prior-manifests/'+unit+'.json')
 gates={'schema':'B1-two-conditional-finiteness-gates/v154','complete':True,'scope':'Only conditional torsionCoords_finite and finiteDimensional_fieldOfPrime sourceproofs','twoFullSourceRecordsMatchAcceptedClosure':True,'canonicalOriginalCommandAndProofBytesRetained':True,'twoFullFourRoleReviewsPassed':True,'twoProofsACCEPTED':True,'twoFinalGETsProved':True,'originalEditorialPayloadsRetained':True,'finalExactLeanShapesBoundByReview':True,'torsionFinitenessItselfProved':False,'unconditionalProviderExistenceProved':False,'B1Completed':False,'S204Completed':False,'archiveReopenedSHA256Verified':False}
 dump(O/'gates.json',gates);dump(O/'ci-history.json',{'schema':'B1-conditional-finiteness-ci-history/v154','attempts':ci,'resourceSource':'MCP-CI process-tree physical RSS/PSS; null unknown','narrowResultsDoNotCloseB1':True});dump(O/'prebuilt-pins.json',{'schema':'B1-conditional-finiteness-prebuilt-pins/v154','inputs':prebuilt,'cacheDeletionAllowed':False});dump(O/'source-byte-checks.json',{'schema':'B1-conditional-finiteness-source-byte-checks/v154','checks':byteChecks});dump(O/'prior-archive-references.json',{'references':prior,'restoreRequiresExistingPriorArchives':True});dump(O/'payload-shape-edits.json',payloadEdits)
 for f in ['gates.json','ci-history.json','prebuilt-pins.json','source-byte-checks.json','prior-archive-references.json','payload-shape-edits.json']:add(O/f,'delivery/'+f)
 contents={m:{'sha256':sha(p),'bytes':p.stat().st_size,'originalPath':str(p)} for m,p in files.items()};dump(O/'archive-manifest.json',{'schema':'B1-conditional-finiteness-archive/v154','members':contents,'priorLargeSourceBlobsRepacked':False})
 archive=O/'b1-field-finiteness-evidence-v154.tar.gz';assert not archive.exists(),'Existing frozen archive must be retained'
 with archive.open('wb') as raw:
  with gzip.GzipFile(fileobj=raw,mode='wb',mtime=0,compresslevel=6) as gz:
   with tarfile.open(fileobj=gz,mode='w') as t:
    for m,p in sorted({**files,'archive-manifest.json':O/'archive-manifest.json'}.items()):
     inf=t.gettarinfo(str(p),arcname=m);inf.mtime=0;inf.uid=inf.gid=0;inf.uname=inf.gname=''
     with p.open('rb') as f:t.addfile(inf,f)
 with tarfile.open(archive,'r:gz') as t:
  for m,x in contents.items():assert hashlib.sha256(t.extractfile(m).read()).hexdigest()==x['sha256'],m
 arcsha=sha(archive)
 def ref(m,pointer=''):return {'archive':str(DEST/archive.name),'archiveSHA256':arcsha,'member':m,'memberSHA256':contents[m]['sha256'],'jsonPointer':pointer}
 ledger={'schema':'B1-two-conditional-finiteness-source-ledger/v154','status':'PROVED_TWO_CONDITIONAL_FINITE_COORDINATE_AND_FINITE_EXTENSION_RESULTS_ONLY','complete':True,'archive':{'path':str(DEST/archive.name),'sha256':arcsha,'bytes':archive.stat().st_size,'members':len(contents)+1},'sourceRoles':reviewsummary,'publication':pubsummary,'payloadShapeEdits':payloadEdits,'sourceProofTermIdentityClaimed':False,'producerConsumers':[{'producer':'Iut.Tripod.torsionCoords_finite','actualSourceConsumer':"Iut.Tripod.finiteDimensional_fieldOf'",'actualTargetConsumer':"AbcAdaptation.Tripod.finiteDimensional_fieldOf'",'consumption':'actual proof invokes torsionCoords_finite h3 and h5','assumption':'h:TorsionFinite l n retained'},{'producer':"Iut.Tripod.finiteDimensional_fieldOf'",'platformProofConsumer':pubsummary['finiteDimensional_fieldOfPrime']['theoremId'],'downstreamB1ProviderConsumer':'PENDING_NOT_COUNTED_AS_CONSUMED','assumptions':'h3:TorsionFinite l 3 and h5:TorsionFinite l 5 retained'}],'actualReviews':{label:ref('four-role-audit/'+label+'/actual/four-role-result.json') for label in LABELS},'originalFullSourceRecords':{label:ref('source-draft/'+label+'/source-root-full-actual-fact.json') for label in LABELS},'finalProvedGETs':{label:ref('publication/'+label+'/proved-readback.json') for label in LABELS},'freshBlindManifest':ref('fresh-blind/manifest.json'),'paperBackground':ref('publication/paper-context-background.json'),'priorArchives':prior,'torsionFinitenessItselfProved':False,'unconditionalProviderExistenceProved':False,'B1Completed':False,'S204Completed':False}
 dump(O/'SOURCE_LEDGER.json',ledger)
 cleanup={'schema':'B1-two-conditional-finiteness-cleanup-whitelist/v154','cleanupPerformed':False,'deleteAllowedOnlyAfterMainAgentAcceptance':True,'entries':[{'path':str(W/f'Solutions/Sol_AbcAdaptation_Tripod_{label}.lean'),'sha256':sha(W/f'Solutions/Sol_AbcAdaptation_Tripod_{label}.lean'),'archiveSource':ref(f'integrated-sources/Solutions/Sol_AbcAdaptation_Tripod_{label}.lean')} for label in LABELS],'mustKeep':[{'path':str(W/f'Theorems/Thm_AbcAdaptation_Tripod_{label}.lean'),'sha256':sha(W/f'Theorems/Thm_AbcAdaptation_Tripod_{label}.lean')} for label in LABELS],'cacheDeletionAllowed':False,'otherSolutionDeletionAllowed':False,'recursiveDeletionAllowed':False};dump(O/'cleanup-whitelist.json',cleanup)
 dump(O/'registry.patch.json',[{'op':'add','path':'/reference_source_preparation/b1_two_conditional_field_finiteness_unit','value':{'status':ledger['status'],'complete':True,'sourceLedger':str(DEST/'SOURCE_LEDGER.json'),'archive':ledger['archive'],'publication':pubsummary,'fullFourRoleResultsPassed':True,'torsionFinitenessItselfProved':False,'unconditionalProviderExistenceProved':False,'B1Completed':False,'S204Completed':False}}])
 (O/'plan-addition.txt').write_text('- [x] 完成两条条件有限性来源证明迁移及四角色完整类型／证明／公理核对：保留 TorsionFinite 假设及 h3、h5，由坐标有限性推出相应生成域有限维；两条证明均获私有平台 ACCEPTED 并回读为 Proved，完整来源证明、独立三语和原始 payload／最终形状差异已归档。此结果不证明实际挠点有限性或无条件 provider 存在性，不关闭 B1 或 S2-04。\n')
 gates['archiveReopenedSHA256Verified']=True;gates['archiveSHA256']=arcsha;dump(O/'gates.json',gates);dump(O/'delivery-manifest.json',{p.name:{'sha256':sha(p),'bytes':p.stat().st_size} for p in O.iterdir() if p.is_file() and p.name!='delivery-manifest.json'})
 print(json.dumps({'archive':str(archive),'sha256':arcsha,'bytes':archive.stat().st_size,'members':len(contents)+1,'complete':True},indent=2))
if __name__=='__main__':main()
