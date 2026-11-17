#!/usr/bin/env python3
"""Build the narrow membership/generator archive after the parent binds final receipts.
Only writes this /tmp task directory. No CI, compiler, API, Git or deletion.
"""
from pathlib import Path
import argparse, gzip, hashlib, json, tarfile
W=Path('/home/admin-wsl/Coq/abc/prove2me_workspace')
A=W/'.local/adaptation'; H=A/'main-chain-open-20261116'
O=Path('/tmp/p2m-b1-curveof-generator-delivery-v161-20261117')
DEST=A/O.name.removeprefix('p2m-')
V153=Path('/tmp/p2m-b1-curveof-generator-v153-20261117')
V154=Path('/tmp/p2m-b1-curveof-generator-v154-20261117')
FACTS=A/'b1-curveof-generator-v157-20261117'
BLIND=Path('/tmp/p2m-b1-mem-gen-fresh-blind-v157-20261117')
EDITORIAL=Path('/tmp/p2m-b1-curveof-generator-publication-v158-20261117')
PUB=A/'b1-curveof-generator-publication-v161-20261117'
AUD=A/'b1-curveof-generator-review-v161-20261117'
SLUG='AbcAdaptation_Tripod_mem_fieldOfExtended_self'
CAN=W/f'Theorems/Thm_{SLUG}.lean'; SOL=W/f'Solutions/Sol_{SLUG}.lean'
GEN=W/'Definitions/Def_AbcAdaptation_Reference_Iut_Tripod_CurveOfGenerator.lean'
ARC=O/'b1-curveof-generator-evidence-v161.tar.gz'
STANDARD={'propext','Classical.choice','Quot.sound'}
LIMITS={'torsionFinitenessItselfProved':False,'unconditionalProviderExistenceProved':False,'B1Completed':False,'S204Completed':False}
def read(p):return json.loads(Path(p).read_text())
def dump(p,j):Path(p).write_text(json.dumps(j,ensure_ascii=False,indent=2)+'\n')
def sha(p):
 h=hashlib.sha256()
 with Path(p).open('rb') as f:
  for block in iter(lambda:f.read(1024*1024),b''):h.update(block)
 return h.hexdigest()
def pin(p):return {'path':str(p),'sha256':sha(p),'bytes':Path(p).stat().st_size}
def exact(p,expected):assert sha(p)==expected,(str(p),expected,sha(p))
def main(finalize):
 e=read(O/'final-evidence.json')
 assert e['parentFinalEvidenceReady'] is True,'Parent final evidence has not been bound; no compression permitted'
 expected=read(V154/'frozen-expected-platform-payload-input.json')
 payload=read(PUB/e['theoremPayload']); post=read(PUB/e['theoremPublication']); verify=read(PUB/e['theoremVerify']); got=read(PUB/e['theoremGET'])
 assert all(payload[k]==expected[k]==got[k] for k in ['theorem_name','preamble','formal_statement'])
 assert verify['status']=='ACCEPTED' and got['status']=='Proved' and post['status']=='PUBLISHED'
 assert verify['theorem_id']==got['theorem_id']==post['theorem_id']
 assert payload['private'] and post['visibility']==got['visibility']=='private'
 assert payload['env']==got['mathlib_rev']=='0df444a360eaa60ab8c11dca51a86af692955474'
 dp=read(PUB/e['definitionPayload']); dg=read(PUB/e['definitionGET']); dr=read(PUB/e['definitionPublication'])
 assert dp['definition']==GEN.read_text()==dg['definition']
 assert dp['definition_name']==dg['definition_name']=='AbcAdaptation_Reference_Iut_Tripod_CurveOfGenerator'
 assert dp['private'] and dg['visibility']=='private'
 assert dr[e['definitionPublicationStatusField']]==e['definitionPublicationExpectedStatus']
 assert dr.get('definition_id',dr.get('theorem_id'))==dg['definition_id'] and dr['visibility']=='private'
 for kind,submitted,received in [('theorem',payload,got),('definition',dp,dg)]:
  valid=read(PUB/kind/'publication-validation.json');assert valid['allSubmittedFieldsExactlyReadBack'] and valid['private']
  for k in valid['fieldNames']:assert submitted[k]==received[k]
  assert read(PUB/kind/'publish-intent.json')['payloadSHA256']==sha(PUB/(e['theoremPayload'] if kind=='theorem' else e['definitionPayload']))
 intent=read(PUB/'theorem/verify-intent.json');assert intent['solutionSHA256']==sha(SOL)
 reportPath=AUD/e['auditReport']; report=read(reportPath)
 for k in ['allRequiredCorrespondenceChecksPassed','namedMembershipTheoremConsumedByPureGenerator','sourceMembershipCanonicalSolutionPlatformFourRolesCompared','compiledPlatformShapeComparedAgainstCompleteSourceTYPEAndProof','platformTheoremNameEqualsActualCanonicalFullName']:assert report[k] is True,k
 assert report['sourceBinderRestrictedToPt'] is False and report['newAssumptionsIntroduced'] is False
 assert report['expectedPlatformPayload']==expected
 roles=report['reports']; assert len(roles)==4
 assert {r['role'] for r in roles}=={'canonical-membership-theorem','global-solution','compiled-exact-platform-formal-shape','pure-generator-data'}
 for r in roles:
  assert not r['hasSorryAx'] and set(r['axioms'])<=STANDARD
  assert all(r[k] for k in ['completeTYPEKernelEqual','strictTYPEBinderInfoEqual','completeProofOrDataValueKernelEqual'])
 # Original source records are retained in full and checked against the old accepted closure.
 records={}
 for filename in ['source-membership-full-actual-fact.json','source-generator-full-actual-fact.json']:
  actual=read(FACTS/filename);assert actual==read(V153/filename)
  assert actual['valueRead'] and actual['kernelValueTypeMatchesActualTYPE']
  assert not actual['hasSorryAx'] and set(actual['axioms'])<=STANDARD and set(actual['typeAxioms'])<=STANDARD and set(actual['valueAxioms'])<=STANDARD
  records[actual['name']]=actual
 closure=A/'b1-source-replay-v104-20261117/actual/closure-v111/actual-facts.jsonl'
 matched=set()
 for line in closure.open():
  r=json.loads(line)
  if r.get('name') in records:assert r==records[r['name']];matched.add(r['name'])
 assert matched==set(records)=={"Iut.Tripod.mem_fieldOf'_self","Iut.Tripod.gen'"}
 assert report['configuration']['boundInputsBinding']['contents']['sourceRecords']==read(V154/'generator-audit.bound-inputs.json')['sourceRecords']
 ready=read(V153/'minimal-source-ready.json'); ast=Path(ready['sourceASTBinding']['path']);source=Path(ready['sourceNormalizedBytes']['path'])
 exact(ast,ready['sourceASTBinding']['sha256']);exact(source,ready['sourceNormalizedBytes']['sha256'])
 rows={r['commandIndex']:r for r in map(json.loads,ast.read_text().splitlines()) if r.get('commandSyntax')}
 raw=source.read_bytes(); rewrites=read(FACTS/'ast-bound-identifier-rewrites.json'); bytechecks=[]
 assert rewrites['generatorIdentifierUnchanged']=="gen'" and rewrites['newMathematicalParametersOrAssumptions'] is False
 def nodes(n):
  yield n
  for c in n.get('children',[]):yield from nodes(c)
 for edit,target in zip(rewrites['rewrites'],[CAN,SOL,GEN]):
  row=rows[edit['sourceCommandIndex']];start=row['range']['start']['offset'];original=raw[start:row['range']['end']['offset']]
  assert hashlib.sha256(original).hexdigest()==edit['originalCommandSHA256']
  selected=[n for n in nodes(row['commandSyntax']) if n.get('identifier')==edit['originalIdentifier']];assert len(selected)==1
  assert selected[0]['range']==edit['sourceIdentifierRange']
  i,j=edit['replacementByteRangeInCommand'];assert original[i:j].decode()==edit['originalIdentifier']
  changed=original[:i]+edit['replacementIdentifier'].encode()+original[j:]
  assert hashlib.sha256(changed).hexdigest()==edit['resultCommandSHA256'] and changed in target.read_bytes()
  bytechecks.append({'target':str(target),'sha256':sha(target),'ASTIdentifierRangeVerified':True,'originalCommandSHA256':edit['originalCommandSHA256'],'resultCommandSHA256':edit['resultCommandSHA256'],'onlyRecordedIdentifierSpanChanged':True})
 audit=read(BLIND/'audit-record.json'); assert audit['english_frozen']
 for path,h in {**audit['codeSHA'],**audit['supportSHA']}.items():exact(Path(path),h)
 for label,h in audit['englishSHA'].items():exact(BLIND/(label+'.en.frozen.md'),h)
 meta=read(EDITORIAL/'metadata.json')
 for path,h in meta['independent_readback']['all_frozen_files_sha256'].items():exact(Path(path),h)
 files={}
 def add(p,member):
  p=Path(p); assert p.is_file(),str(p)
  assert p.stat().st_size<5_000_000,('Do not repack large source libraries',str(p))
  assert member not in files or files[member]==p
  files[member]=p
 def tree(root,prefix):
  assert root.is_dir(),str(root)
  for p in sorted(root.rglob('*')):
   if p.is_file() and '__pycache__' not in p.parts:add(p,prefix+'/'+str(p.relative_to(root)))
 for root,prefix in [(V153,'source-preparation-v153'),(V154,'fourrole-draft-v154'),(FACTS,'source-current-facts-v157'),(BLIND,'fresh-blind'),(EDITORIAL,'editorial-v158'),(PUB,'publication'),(AUD,'actual-fourrole-audit')]:tree(root,prefix)
 for p in [CAN,SOL,GEN]:add(p,'integrated-sources/'+str(p.relative_to(W)))
 for p in [ast,source,W/'references/upload_full_project.md']:add(p,'source-parser-and-rules/'+p.name)
 for p in [W/'lean-toolchain',W/'lakefile.lean',W/'lake-manifest.json']:add(p,'build-configuration/'+p.name)
 # Explicit required success categories and all matching retries are preserved.
 paths=set(H.glob('b1-mem-fieldofextended-self*-result.json'))|set(H.glob('b1-curveof-generator*-result.json'))|{FACTS/'mem-fieldofextended-self-solution-leaf-result.json'}
 paths|={Path(x['result']) for x in e['requiredJobs']}
 paths.add(Path(e['mandatoryProjectGates']['result']))
 ci=[]; pins={}; jobs={}
 for p in sorted(paths):
  j=read(p);r=j['result']; snap=r['snapshot']; manifest=snap['manifest'];resources=j.get('resources',r.get('resources',{}))
  assert j['request']['exclusive'] and snap['workspace_mode']=='exclusive_worktree' and snap['snapshot_id'] is None
  assert Path(j['request']['workspace'])==W
  job=j['job_id'];jobs[job]=j
  member='ci/'+job+'/'+p.name;add(p,member)
  stem=p.name.removesuffix('-result.json')
  for folder in [p.parent,H]:
   for recordedStem in {stem,manifest.get('purpose',stem)}:
    for kind in ['request','submit']:
     q=folder/(recordedStem+'-'+kind+'.json')
     if q.is_file():add(q,'ci/'+job+'/'+q.name)
  for artifact in r.get('artifacts',[]):
   q=Path(artifact);add(q,'ci/'+job+'/artifacts/'+q.name)
  for path,h in manifest.get('input_hashes',{}).items():
   if path.endswith(('.olean','.ilean','.ir')):pins[path]=h
  if resources.get('cpu_time_seconds') is not None:
   assert resources.get('cpu_user_seconds') is not None and resources.get('cpu_system_seconds') is not None
   assert abs(resources['cpu_time_seconds']-resources['cpu_user_seconds']-resources['cpu_system_seconds'])<1e-7
  ci.append({'jobId':job,'status':j['status'],'exitCode':r['exit_code'],'inputSHA256':manifest.get('source_sha256'),'inputHashes':manifest.get('input_hashes',{}),'workspace':j['request']['workspace'],'workspaceMode':snap['workspace_mode'],'snapshotId':None,'exclusive':True,'actualArguments':r['actual_arguments'],'expectedDuration':j['request']['expected_duration'],'expectedMemory':j['request']['expected_memory'],'resources':{k:resources.get(k) for k in ['wall_time_seconds','cpu_time_seconds','cpu_user_seconds','cpu_system_seconds','peak_rss_bytes','peak_pss_bytes']},'resourceSource':resources.get('source',resources.get('memory_decision')),'degraded':resources.get('degraded'),'diagnostics':r.get('diagnostics',[]),'receiptMember':member,'receiptSHA256':sha(p)})
 restoration=[]
 for entry in ci:
  for original,h in entry['inputHashes'].items():
   if not original.endswith(('.lean','.json')):continue
   q=Path(original)
   if q.is_file() and sha(q)==h:continue
   candidates=[m for m,p in files.items() if sha(p)==h]
   assert candidates,('Historical actual input not preserved',entry['jobId'],original,h)
   restoration.append({'jobId':entry['jobId'],'originalPath':original,'sourceSHA256':h,'archiveMembers':candidates,'originalPathNowDiffersOrMissing':True,'classification':'HISTORICAL_FAILED_INPUT_NOT_FINAL_ACCEPTANCE'})
 dump(O/'historical-ci-input-restoration.json',{'restorationMap':restoration});add(O/'historical-ci-input-restoration.json','delivery/historical-ci-input-restoration.json')
 mandatory=e['mandatoryProjectGates'];mj=jobs[mandatory['jobId']]
 assert mj['status']=='succeeded' and mj['result']['exit_code']==0
 for declaration in ['AbcAdaptation.Tripod.mem_fieldOfExtended_self',"AbcAdaptation.Tripod.gen'",'solution']:
  assert "'"+declaration+"' depends on axioms: [propext, Classical.choice, Quot.sound]" in mj['result']['stdout']
 assert 'all three new declarations have standard axioms only' in mj['result']['stdout']
 assert mj['result']['snapshot']['manifest']['input_hashes'][mandatory['source']]==sha(Path(mandatory['source']))
 assert set(mandatory['covers'])=={'Checks','ImportAudit','Act1Scene1','AxiomAudit','new-membership-generator-standard-axioms'}
 requiredCategories={'canonical-leaf','canonical-artifact','solution-leaf','solution-artifact','generator-leaf','generator-artifact','four-role-review'}
 assert {x['category'] for x in e['requiredJobs']}==requiredCategories
 for req in e['requiredJobs']:
  j=jobs[req['jobId']];assert j['status']=='succeeded' and j['result']['exit_code']==0,req
  if req.get('source'):assert j['result']['snapshot']['manifest']['input_hashes'][req['source']]==sha(Path(req['source']))
 prior=[]
 for unit,arcname in [('b1-existing-and-elliptic-delivery-v123-20261117','b1-existing-and-elliptic-evidence-v123.tar.gz'),('b1-arithmetic-delivery-v129-20261117','b1-arithmetic-evidence-v129.tar.gz'),('b1-field-finiteness-delivery-v154-20261117','b1-field-finiteness-evidence-v154.tar.gz')]:
  mp=A/unit/'archive-manifest.json';mj=read(mp);priorArc=A/unit/arcname
  expectedArc=mj.get('archiveSHA256') or read(A/unit/'SOURCE_LEDGER.json')['archive']['sha256']; exact(priorArc,expectedArc)
  entries=mj.get('files',[])
  refs=[x for x in entries if any(k in x.get('path','') for k in ['root-source-facts-v106.json','closure-v111/actual-facts.jsonl','closure-v111/actual-edges.jsonl'])]
  prior.append({'archive':str(priorArc),'archiveSHA256':expectedArc,'requiredMembers':refs,'priorLargeBlobsRepacked':False})
  add(mp,'prior-manifests/'+unit+'.json')
 # Preserve exact source consumer edges without claiming future target consumers are integrated.
 edges=read(V153/'actual-consumer-edges.json');add(Path(edges['sourceActualEdgesPath']).parent/'actual-edges.jsonl','source-edges/actual-edges.jsonl') if Path(edges['sourceActualEdgesPath']).stat().st_size<5_000_000 else None
 gates={'schema':'B1-membership-and-pure-generator-gates/v161','complete':True,'scope':'Only parameter membership and its dependent pure generator data','sourceFullOriginalRecordsMatchAcceptedClosure':True,'ASTBoundIdentifierRenamesOnly':True,'fourMembershipRolesAndCompleteGeneratorTYPEValuePassed':True,'allAxiomsStandardAndSorryAxFree':True,'mergedMandatoryProjectGatesPassed':True,'freshBlindFrozenEnglishSHA256Checked':True,'theoremProofACCEPTED':True,'theoremFinalGETProved':True,'definitionFinalGETExactSource':True,'archiveReopenedSHA256Verified':False,**LIMITS}
 publication={'theoremId':got['theorem_id'],'publicationJobId':post['id'],'proofSubmissionId':verify['id'],'proofStatus':'ACCEPTED','finalGETStatus':'Proved','definitionId':dg.get('definition_id',dg.get('id'))}
 for name,data in [('ci-history.json',{'schema':'B1-membership-generator-ci-history/v161','attempts':ci,'requiredJobs':e['requiredJobs'],'mandatoryProjectGates':e['mandatoryProjectGates'],'resourceInterpretation':'MCP-CI process-tree physical RSS/PSS bytes; null means unknown; CPU total checked as user+system','narrowResultsDoNotCloseB1':True}),('prebuilt-pins.json',{'inputs':pins,'cacheDeletionAllowed':False}),('source-byte-checks.json',{'checks':bytechecks}),('prior-archive-references.json',{'references':prior,'restoreRequiresExistingPriorArchives':True}),('gates.json',gates)]:dump(O/name,data);add(O/name,'delivery/'+name)
 add(O/'final-evidence.json','delivery/final-evidence.json');add(O/'build_archive.py','delivery/build_archive.py');add(O/'cleanup_exact_solution.py','delivery/cleanup_exact_solution.py');add(O/'root-platform-helper-v164.py','delivery/root-platform-helper-v164.py');add(O/'root-platform-helper-v164.before-generic-definition-id-fix.py','delivery/root-platform-helper-v164.before-generic-definition-id-fix.py');add(O/'mandatory-checks-readonly-findings.json','delivery/mandatory-checks-readonly-findings.json');add(O/'publication-readback-history.json','delivery/publication-readback-history.json')
 contents={m:{'sha256':sha(p),'bytes':p.stat().st_size,'originalPath':str(p)} for m,p in sorted(files.items())}
 dump(O/'archive-manifest.json',{'schema':'B1-membership-generator-archive/v161','members':contents,'priorLargeSourceBlobsRepacked':False})
 if not finalize:
  print(json.dumps({'preflight':'passed','files':len(contents),'bytes':sum(x['bytes'] for x in contents.values()),'compressionPerformed':False},indent=2));return
 assert not ARC.exists(),'Frozen archive already exists; do not recompress'
 with ARC.open('xb') as out:
  with gzip.GzipFile(fileobj=out,mode='wb',mtime=0,compresslevel=6) as gz:
   with tarfile.open(fileobj=gz,mode='w') as tar:
    for member,p in sorted({**files,'archive-manifest.json':O/'archive-manifest.json'}.items()):
     info=tar.gettarinfo(str(p),arcname=member);info.mtime=0;info.uid=info.gid=0;info.uname=info.gname=''
     with p.open('rb') as f:tar.addfile(info,f)
 with tarfile.open(ARC,'r:gz') as tar:
  assert set(tar.getnames())==set(contents)|{'archive-manifest.json'}
  for member,meta in contents.items():assert hashlib.sha256(tar.extractfile(member).read()).hexdigest()==meta['sha256'],member
  assert hashlib.sha256(tar.extractfile('archive-manifest.json').read()).hexdigest()==sha(O/'archive-manifest.json')
 arcsha=sha(ARC)
 def ref(member):return {'archive':str(DEST/ARC.name),'archiveSHA256':arcsha,'member':member,'memberSHA256':contents[member]['sha256']}
 ledger={'schema':'B1-membership-and-pure-generator-source-ledger/v161','status':'PROVED_PARAMETER_MEMBERSHIP_AND_REGISTERED_DEPENDENT_GENERATOR_DATA_ONLY','complete':True,'archive':{'path':str(DEST/ARC.name),'sha256':arcsha,'bytes':ARC.stat().st_size,'members':len(contents)+1},'publication':publication,'sourceIdentity':{'membership':"Iut.Tripod.mem_fieldOf'_self",'generator':"Iut.Tripod.gen'",'canonical':'AbcAdaptation.Tripod.mem_fieldOfExtended_self','generatorIdentifierUnchanged':"gen'",'sourceNativeProofTermByteIdentityClaimed':False},'producerConsumers':[{'producer':'AbcAdaptation.Tripod.mem_fieldOfExtended_self','actualTargetConsumer':"AbcAdaptation.Tripod.gen'",'consumption':'gen value pairs l with named membership theorem l'},{'producer':"Iut.Tripod.gen'",'actualSourceConsumers':'source-preparation-v153/actual-consumer-edges.json','downstreamTargetConsumers':'PENDING_NOT_COUNTED_AS_INTEGRATED'}],'historicalCIInputRestoration':ref('delivery/historical-ci-input-restoration.json'),'actualFourRoleAndGeneratorReview':ref('actual-fourrole-audit/'+e['auditReport']),'originalFullSourceRecords':{k:ref('source-current-facts-v157/'+k) for k in ['source-membership-full-actual-fact.json','source-generator-full-actual-fact.json']},'finalProvedGET':ref('publication/'+e['theoremGET']),'finalDefinitionGET':ref('publication/'+e['definitionGET']),'freshBlindAudit':ref('fresh-blind/audit-record.json'),'paperBackground':ref('editorial-v158/paper-context-background.json'),'priorArchives':prior,**LIMITS}
 dump(O/'SOURCE_LEDGER.json',ledger)
 dump(O/'cleanup-whitelist.json',{'schema':'B1-membership-generator-cleanup-whitelist/v161','cleanupPerformed':False,'deleteAllowedOnlyAfterMainAgentAcceptance':True,'entries':[{'path':str(SOL),'sha256':sha(SOL),'archiveSource':ref('integrated-sources/'+str(SOL.relative_to(W)))}],'mustKeep':[pin(CAN),pin(GEN)],'cacheDeletionAllowed':False,'otherSolutionDeletionAllowed':False,'recursiveDeletionAllowed':False})
 dump(O/'registry.patch.json',[{'op':'add','path':'/reference_source_preparation/b1_parameter_membership_and_pure_generator_unit','value':{'status':ledger['status'],'complete':True,'sourceLedger':str(DEST/'SOURCE_LEDGER.json'),'archive':ledger['archive'],'publication':publication,'fullMembershipFourRoleAndPureGeneratorTYPEValueReviewPassed':True,**LIMITS}}])
 (O/'plan-addition.txt').write_text('- [x] 完成参数属于生成域的来源证明及依赖成员证书的纯 gen\' 数据迁移；保留完整来源 TYPE/value、AST 绑定改名、四角色与 gen 审查、独立三语及论文背景；成员证明私有 ACCEPTED/Proved，定义已精确回读。此项不证明实际挠点有限性、provider 存在性，不关闭 B1 或 S2-04。\n')
 gates.update({'archiveReopenedSHA256Verified':True,'archiveSHA256':arcsha});dump(O/'gates.json',gates)
 dump(O/'delivery-manifest.json',{p.name:{'sha256':sha(p),'bytes':p.stat().st_size} for p in sorted(O.iterdir()) if p.is_file() and p.name!='delivery-manifest.json'})
 print(json.dumps({'archive':str(ARC),'sha256':arcsha,'bytes':ARC.stat().st_size,'members':len(contents)+1,'complete':True},indent=2))
if __name__=='__main__':
 parser=argparse.ArgumentParser();parser.add_argument('--finalize',action='store_true');args=parser.parse_args();main(args.finalize)
