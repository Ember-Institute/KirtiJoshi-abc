#!/usr/bin/env python3
"""Prepare Provider4/curve + LocalHeightData11 evidence. --finalize requires parent evidence.
Writes only O. No CI, compiler, API, Git, cleanup or workspace writes.
"""
from pathlib import Path
import argparse,gzip,hashlib,json,tarfile
W=Path('/home/admin-wsl/Coq/abc/prove2me_workspace');A=W/'.local/adaptation';H=A/'main-chain-open-20261116'
O=Path('/tmp/p2m-b1-provider-height-delivery-v193-20261117');DEST=A/O.name.removeprefix('p2m-')
SRC=Path('/tmp/p2m-b1-provider-height-draft-v184-20261117');EDITORIAL=Path('/tmp/p2m-b1-provider-height-publication-v188-20261117')
BLIND=Path('/tmp/p2m-b1-provider-height-fresh-blind-v185-20261117');AUD=A/'b1-provider-height-native-review-v192-20261117';PRIME=A/'b1-provider-height-v187-20261117/source-residuechar'
CAN={k:W/'Definitions'/v for k,v in {'provider':'Def_AbcAdaptation_Reference_Iut_Tripod_CurveProviders.lean','assembly':'Def_AbcAdaptation_Reference_Iut_Concrete_LocalHeightDataAssembly.lean'}.items()}
EXPECTED={'provider':'4adfdc8d3b665c0b8e0763331602e74684f7b8ca9c4e98e76c66301fedff3e0b','assembly':'2f2a6faf01653793354e105019904699cd5fb5472b97806b264834a3efa93770'}
LIMITS={'unconditionalProviderExistenceProved':False,'torsionFinitenessItselfProved':False,'CurveArithmeticSupplied':False,'modRepSupplied':False,'TateInputsSupplyCompleted':False,'providerTateLocalDataHIntegrated':False,'P_hReplacedWithFinHeightRHS':False,'B1Completed':False,'S204Completed':False}
STANDARD={'propext','Classical.choice','Quot.sound'}
ARC=O/'b1-provider-height-evidence-v193.tar.gz'
def read(p):return json.loads(Path(p).read_text())
def dump(p,j):Path(p).write_text(json.dumps(j,ensure_ascii=False,indent=2)+'\n')
_sha_cache={}
def sha(p):
 p=Path(p);st=p.stat();key=(str(p),st.st_size,st.st_mtime_ns)
 if key in _sha_cache:return _sha_cache[key]
 h=hashlib.sha256()
 with Path(p).open('rb') as f:
  for b in iter(lambda:f.read(1024*1024),b''):h.update(b)
 _sha_cache[key]=h.hexdigest();return _sha_cache[key]
def pin(p):return {'path':str(p),'sha256':sha(p),'bytes':Path(p).stat().st_size}
def exact(p,h):assert sha(p)==h,(str(p),h,sha(p))
def ptr(x,path):
 for k in path.strip('/').split('/') if path else []:x=x[int(k)] if isinstance(x,list) else x[k.replace('~1','/').replace('~0','~')]
 return x
def main(finalize):
 e=read(O/'final-evidence.json');assert not finalize or e['parentFinalEvidenceReady'] is True,'Parent finalize signal and terminal evidence pending'
 if e['gitDiffCheckPassed']:
  diff=read(e['gitDiffCheckRecord']);assert diff['exit_code']==0 and diff['command']==['git','diff','--check'] and diff['stdout']==diff['stderr']==''
 files={}
 def add(p,m):
  p=Path(p);assert p.is_file(),str(p)
  assert p.name not in {'actual-facts.jsonl','root-source-facts-v106.json','fact-Iut_isUniformizer_of_valuation_eq.json'},str(p)
  assert 'pending-supplier' not in p.parts,str(p)
  assert m not in files or files[m]==p;files[m]=p
 def tree(p,prefix):
  p=Path(p)
  for q in sorted(p.rglob('*')):
   if q.is_file() and '__pycache__' not in q.parts:add(q,prefix+'/'+str(q.relative_to(p)))
 for k,p in CAN.items():exact(p,EXPECTED[k]);exact(SRC/'definitions'/p.name,EXPECTED[k]);add(p,'integrated-sources/Definitions/'+p.name)
 prov=read(SRC/'source-provenance.json');add(SRC/'source-provenance.json','source/source-provenance.json')
 selected=['Iut.Tripod.CurveProviders'+x for x in ['', '.torsionFinite3','.torsionFinite5','.arith','.modRep','.mk','.rec','.curve','.curve._proof_1','.curve._proof_2']]+['Iut.EllipticCurveData.localHeightData'+x for x in ['', '._proof_1','._proof_2','._proof_3','._proof_4']]
 rows={}
 for p in sorted((SRC/'source').glob('fact-*.json')):
  # Do not parse unrelated 198 MB source proof.
  if p.name=='fact-Iut_isUniformizer_of_valuation_eq.json':continue
  if not (p.name.startswith('fact-Iut_Tripod_CurveProviders') or p.name.startswith('fact-Iut_EllipticCurveData_localHeightData')):continue
  r=read(p)
  if r['name'] in selected:rows[r['name']]=r;add(p,'source/full-facts/'+p.name)
 assert set(rows)==set(selected)
 for r in rows.values():
  assert not r['hasSorryAx']
  for k in ['axioms','typeAxioms','valueAxioms']:assert set(r[k])<=STANDARD
  if r['actualValueExpr'] is not None:assert r['valueRead'] and r['kernelValueTypeMatchesActualTYPE']
 # Match original facts with the previously accepted full closure without repacking it.
 closure=Path(next(x['path'] for x in prov['inputs'] if x['path'].endswith('/actual-facts.jsonl')))
 matched=set()
 for line in closure.open():
  r=json.loads(line)
  if r.get('name') in rows:assert r==rows[r['name']];matched.add(r['name'])
 assert matched==set(rows)
 bytechecks=[]
 chosen={('Iut.Concrete.Existence',21):'assembly',('Iut.Tripod.CurveFacts',39):'provider',('Iut.Tripod.CurveFacts',42):'provider',('Iut.Cor312.ThetaData.Places',17):'assembly'}
 replay=Path(next(x['path'] for x in prov['inputs'] if x['path'].endswith('/B1SourceReplay.lean')))
 replaybytes=replay.read_bytes()
 for command in prov['sourceCommands']:
  key=(command['module'],command['commandIndex'])
  if key not in chosen:continue
  p=Path(command['sourceBytes']['path']);exact(p,command['sourceBytes']['sha256']);b=p.read_bytes();rr=command.get('replayRange');orig=command['originalRange']
  normalized=next(Path(x['path']) for x in prov['inputs'] if x['path'].endswith('/'+command['module'].replace('.','-')+'.normalized.lean'))
  assert normalized.read_bytes()[orig['start']['offset']:orig['end']['offset']]==b
  if rr:assert b==replaybytes[rr['start']['offset']:rr['end']['offset']]
  assert b in CAN[chosen[key]].read_bytes();add(p,'source/AST/'+p.name)
  bytechecks.append({'module':key[0],'commandIndex':key[1],**pin(p),'originalAndNativeCommandBytesEqual':True,'acceptedReplayBytesEqual':True if rr else None,'notReplayOwnedOriginalCachedModule':not bool(rr)})
 assert len(bytechecks)==4
 for x in prov['inputs']:
  if x['bytes']<5_000_000 and any(t in x['path'] for t in ['.normalized.lean','B1SourceReplay.lean','source-replay-spans-map.json']):exact(x['path'],x['sha256']);add(x['path'],'source/small-inputs/'+Path(x['path']).name)
 for name in ['provider-four-fields.json','localHeightData-eleven-constructor-arguments.json','generated-proof-parameter-closure.json','actual-height-chain.json','existing-compatibility-scope.json','ready-source-project-boundaries.json']:
  add(SRC/'audit'/name,'source/audit/'+name)
 add(SRC/'source/actual-consumer-edges.json','source/actual-consumer-edges.json')
 args=read(SRC/'audit/localHeightData-eleven-constructor-arguments.json');assert len(args['arguments'])==11
 assert read(SRC/'audit/provider-four-fields.json')['newInstanceOrInhabitantProvided'] is False
 prime=read(PRIME/'actual/actual-facts.json');assert len(prime['facts'])==46
 full=[r for r in prime['facts'] if r['record']=='fullActualFact'];boundary=[r for r in prime['facts'] if r['record']=='actualBoundary']
 assert len(full)==1 and full[0]['name']=='Iut.residueChar_prime' and len(boundary)==45
 for r in full:
  assert not r['hasSorryAx']
  for k in ['axioms','typeAxioms','valueAxioms']:assert set(r[k])<=STANDARD
 tree(PRIME,'source/residueChar-prime')
 inventory=read(AUD/'actual/native-actual-facts.json');assert len(inventory['facts'])==28 and not inventory['sourceNativeCorrespondenceAccepted']
 tree(AUD,'native-review')
 # Retain actual failed and superseded certificate attempts once, including full V198 output.
 for dirname in ['b1-provider-height-source-certificate-v195-20261117','b1-provider-height-native-proof-delta-v198-20261118','b1-provider-height-portable-source-certificate-v201-20261118','b1-provider-height-native-shared-projection-v203-20261118','b1-provider-height-shared-source-certificate-v205-20261118']:
  tree(A/dirname,'certificate-history/'+dirname)
 unused=Path('/tmp/p2m-b1-provider-height-proof-delta-v198-20261118/unused-large-preparation-config-record.json')
 unusedrecord=read(unused);assert unusedrecord['submittedToCI'] is False and unusedrecord['retainedInArchive'] is False
 add(unused,'certificate-history/unused-large-preparation-config-record.json')
 tree(BLIND,'fresh-blind');blind=read(BLIND/'materials-and-hashes.json');assert blind['independent_original_count']==1 and blind['translations_are_independent_audits'] is False
 exact(BLIND/'readback.en.frozen.md',blind['freeze_sha256'])
 for item in blind['outputs']:exact(BLIND/item['file'],item['sha256'])
 tree(EDITORIAL,'editorial-v188')
 for k,p in CAN.items():assert read(EDITORIAL/k/'payload.json')['definition']==p.read_text()
 publication={};pub=Path(e['publicationDirectory'])
 def verifyPublicationTransforms(k,d):
  frozen=read(EDITORIAL/k/'payload.json');assert read(d/'payload-frozen-readback-format.json')==frozen
  formatted=json.loads(json.dumps(frozen));text=formatted['natural_language_statement']
  for a,b in [(r'\(', '$'),(r'\)', '$'),(r'\[', '$$'),(r'\]', '$$')]:text=text.replace(a,b)
  formatted['natural_language_statement']=text;assert read(d/'payload-before-api-key-normalization.json')==formatted
  formatting=read(pub/'math-delimiter-formatting.json');records=[x for x in formatting['records'] if x['kind']==k];assert len(records)==1;record=records[0]
  assert record['onlyNaturalLanguageMathDelimitersChanged'] and record['formulaContentsUnchanged']
  exact(d/'payload-frozen-readback-format.json',record['frozenPayloadSHA256']);exact(d/'payload-before-api-key-normalization.json',record['submittedPayloadSHA256'])
  normalized={ {'name':'definition_name','title':'definition_title'}.get(key,key):value for key,value in formatted.items() }
  assert set(normalized)=={'definition_name','definition_title','definition','natural_language_statement','source','env','private'}
  assert read(d/'payload-final.json')==normalized
  changes=[x for x in read(pub/'api-key-normalization.json')['changes'] if x['kind']==k];assert len(changes)==1;change=changes[0]
  assert change['keyRenames']=={'name':'definition_name','title':'definition_title'} and change['allValuesUnchanged'] and change['noAPISubmissionOccurredBeforeFix']
  exact(d/'payload-before-api-key-normalization.json',change['originalSHA256']);exact(d/'payload-final.json',change['finalSHA256'])
 for k,p in CAN.items():
  info=e['definitions'][k];d=pub/info['directory']
  if not (d/info['finalGET']).is_file():publication[k]={'status':'PENDING_FINAL_GET'};continue
  payload=read(d/info['payload']);result=read(d/info['publicationResult']);got=read(d/info['finalGET']);validation=read(d/info['validation'])
  assert result['status']=='PUBLISHED' and result['visibility']==got['visibility']=='private' and payload['private']
  assert result.get('definition_id',result.get('theorem_id'))==got['definition_id']
  assert payload['definition']==got['definition']==p.read_text()
  for key in ['definition_name','definition_title','definition','natural_language_statement','source']:assert got[key]==payload[key]
  assert payload['definition_name']==info['definitionName'] and got['mathlib_rev']==payload['env']=='0df444a360eaa60ab8c11dca51a86af692955474'
  assert validation['allSubmittedFieldsExactlyReadBack'] and validation['private']
  verifyPublicationTransforms(k,d)
  assert read(d/'publish-intent.json')['payloadSHA256']==sha(d/info['payload'])
  publication[k]={'definitionId':got['definition_id'],'publicationJobId':result['id'],'private':True,'finalGETExact':True,'naturalLanguageDisplayDelimiterOnlyChange':True,'apiNameTitleKeysNormalizedWithAllValuesUnchanged':True,'frozenReadbackUnchanged':True}
 if pub.is_dir():
  tree(pub,'publication')
  for k in CAN:
   verifyPublicationTransforms(k,pub/k)
 checks=[]
 for x in e['JSONAssertions']:
  p=Path(x['path'])
  if not p.is_file():checks.append({'path':str(p),'status':'PENDING'});continue
  j=read(p)
  for path,expected in x['equals'].items():assert ptr(j,path)==expected,(str(p),path)
  for path in x.get('standardAxiomFields',[]):assert set(ptr(j,path))<=STANDARD,(str(p),path)
  if j.get('schema')=='B1-residueChar-prime-shared-projection-source-certificate/v204':
   assert j['nativeSharedProjectionCertificate']==read(A/'b1-provider-height-native-shared-projection-v203-20261118/actual/native-shared-projection.json')
   assert j['nativeSharedProjectionSuccessfulReceipt']==read(H/'b1-provider-height-native-prime-shared-projection-v204-result.json')
   assert j['sourceRecord']==full[0]
  if j.get('schema')=='B1-provider-height-native-correspondence-audit/v186':
   assert len(j['reports'])==len(j['actualPairs'])==16 and len(j['acceptedBoundaryPairs'])==21
   assert len(j['allActualNewOwnerNativeFacts'])==28 and len(j['unpairedNativeCompilerGeneratedFactsLegalityOnly'])==12
   assert len(j['constructorArgumentReports'])==12 and len(j['nativeSharedProjectionCompleteEqualityReports'])==3
   for row in j['reports']:
    for key in ['completeTYPEKernelEqual','strictPublicForallBinderInfoEqual','strictDeepTYPEBinderInfoEqual','completeComputationMetadataEqual','instanceRegistrationEqual']:assert row[key]
    if row['kind'] in ['definition','theorem','opaque']:assert row['completeValueKernelEqual']
    assert not row['hasSorryAx'] and set(row['axioms'])<=STANDARD
    assert all(d['completeDomainKernelEqual'] for d in row['publicParameterDomainReports'])
   for row in j['unpairedNativeCompilerGeneratedFactsLegalityOnly']:
    assert not row['hasSorryAx'] and row['kernelValueTypeMatchesActualTYPE']
    for key in ['axioms','typeAxioms','valueAxioms']:assert set(row[key])<=STANDARD
   for row in j['unpairedNativeCompilerGeneratedUsageAnalysis']:assert row['fullNativeFactKernelAndAxiomLegalityChecked'] and not row['mathematicalSourcePairingClaimed']
   assert j['constructorArgumentReports'][0]['completeSelectorKernelEqual']
   assert all(row['completeArgumentKernelEqual'] for row in j['constructorArgumentReports'][1:])
   assert [r['field'] for r in j['constructorArgumentReports'][1:]]==['ι','bad','p','hv','f','deg','one_le_deg','p_prime','one_le_hv','one_le_f','sum_f_le']
   for row in j['nativeSharedProjectionCompleteEqualityReports'][:2]:
    for key in ['equalityProofKernelChecked','sameOriginalRCommRingAndDdArgumentsUsed','wholePropTYPEKernelEqual','wholePropValuesKernelEqual']:assert row[key]
    assert not row['newDataArgumentOrAssumptionIntroduced']
   assert j['nativeSharedProjectionCompleteEqualityReports'][2]['wholeHelperEqualityCertificateKernelChecked']
   sourcecert=read(A/'b1-provider-height-shared-source-certificate-v205-20261118/actual/residuechar-prime-shared-projection-source-certificate.json')
   assert j['independentResidueCharPrimeSourceCertificate']==sourcecert
   binding=j['independentSourceCertificateBinding'];assert binding['contents']==sourcecert and binding['sourceCertificateJobId']=='ci-019368-2bcf746f'
   assert binding['receiptContents']==read(H/'b1-provider-height-shared-projection-source-v205-result.json')
   bound=j['configuration']['boundInputsBinding']['contents'];assert len(bound['sourceRecords'])==16
   assert all(r==(full[0] if r['name']=='Iut.residueChar_prime' else rows[r['name']]) for r in bound['sourceRecords'])
   assert bound['nativeInventory']==inventory and bound['proofNumbersUsedAsPairingEvidence'] is False
  add(p,x['member']);checks.append({'path':str(p),'status':'VERIFIED','sha256':sha(p)})
 ci=[];jobs={};pins={};resultpaths=set()
 for pattern in ['b1-curveproviders-*-result.json','b1-localheight-*-result.json','b1-provider-height-*-result.json']:resultpaths.update(H.glob(pattern))
 resultpaths.update(Path(x['result']) for x in e['requiredJobs'].values() if x.get('result') and Path(x['result']).is_file())
 for p in sorted(resultpaths):
  j=read(p);req=j['request'];r=j.get('result') or {};snap=r.get('snapshot') or {};manifest=snap.get('manifest') or req['worktree_manifest'];resources=j.get('resources',r.get('resources',{}));job=j['job_id'];jobs[job]=j
  assert req['exclusive'] and Path(req['workspace'])==W
  if j['status']=='succeeded':assert snap['workspace_mode']=='exclusive_worktree' and snap['snapshot_id'] is None and r['exit_code']==0
  member='ci/'+job+'/'+p.name;add(p,member);stem=p.name.removesuffix('-result.json')
  for st in {stem,manifest.get('purpose',stem)}:
   for kind in ['request','submit','logs','progress-logs']:
    q=p.parent/(st+'-'+kind+'.json')
    if q.is_file():add(q,'ci/'+job+'/'+q.name)
  for path in r.get('artifacts',[]):add(path,'ci/'+job+'/artifacts/'+Path(path).name)
  for path,h in manifest.get('input_hashes',{}).items():
   if path.endswith(('.olean','.ilean','.ir')):pins[path]=h
  cpu=resources.get('cpu_time_seconds')
  if cpu is not None:assert abs(cpu-resources['cpu_user_seconds']-resources['cpu_system_seconds'])<1e-7
  ci.append({'jobId':job,'status':j['status'],'exitCode':r.get('exit_code'),'inputHEAD':manifest.get('head'),'inputSHA256':manifest.get('source_sha256'),'inputHashes':manifest.get('input_hashes',{}),'workspace':req['workspace'],'workspaceMode':snap.get('workspace_mode'),'snapshotId':snap.get('snapshot_id'),'requestExclusive':True,'actualArguments':r.get('actual_arguments'),'expectedDuration':req['expected_duration'],'expectedMemory':req['expected_memory'],'observedCompileTimeSeconds':j.get('compile_time_seconds'),'observedCompileTimeIsOnlyLowerBound':j['status']=='timeout','resources':{k:resources.get(k) for k in ['wall_time_seconds','cpu_time_seconds','cpu_user_seconds','cpu_system_seconds','peak_rss_bytes','peak_pss_bytes']},'resourceSource':resources.get('source',resources.get('memory_decision')),'degraded':resources.get('degraded'),'diagnostics':r.get('diagnostics'),'error':r.get('error'),'receiptMember':member,'receiptSHA256':sha(p)})
 required={}
 for key,x in e['requiredJobs'].items():
  j=jobs.get(x.get('jobId'));passed=bool(j and j['status']=='succeeded' and j['result']['exit_code']==0);required[key]={'passed':passed,**x}
  if passed:
   if x.get('source'):assert j['result']['snapshot']['manifest']['input_hashes'][x['source']]==sha(x['source'])
   for marker in x.get('stdoutRequired',[]):assert marker in j['result']['stdout']
 # Restore original audit inputs from frozen historical files if an in-place parser fix changed a path.
 hashmembers={}
 for member,path in files.items():
  if path.suffix in ['.lean','.json']:hashmembers.setdefault(sha(path),[]).append(member)
 restoration=[]
 for entry in ci:
  for original,h in entry['inputHashes'].items():
   if not original.endswith(('.lean','.json')):continue
   path=Path(original)
   if path.is_file() and sha(path)==h:continue
   candidates=hashmembers.get(h,[]);assert candidates,('Historical CI input unavailable',entry['jobId'],original,h)
   restoration.append({'jobId':entry['jobId'],'originalPath':original,'sourceSHA256':h,'archiveMembers':candidates,'acceptedAsFinalInput':False})
 dump(O/'historical-ci-input-restoration.json',{'restorationMap':restoration});add(O/'historical-ci-input-restoration.json','delivery/historical-ci-input-restoration.json')
 prior=read('/tmp/p2m-b1-curveof-assembly-delivery-v172-20261117/prior-archive-references.json')
 curveLedger=A/'b1-curveof-assembly-delivery-v172-20261117/SOURCE_LEDGER.json';cl=read(curveLedger)
 prior['references'].append({'archive':cl['archive']['path'],'archiveSHA256':cl['archive']['sha256'],'requiredMembers':[],'priorLargeSourceBlobsRepacked':False})
 for ref in prior['references']:exact(ref['archive'],ref['archiveSHA256'])
 prior['priorCurveOfLedger']=pin(curveLedger);add(curveLedger,'prior-manifests/curveOf-SOURCE_LEDGER.json')
 apiReady=all(x.get('finalGETExact') for x in publication.values());allChecks=len(checks)>=2 and all(x['status']=='VERIFIED' for x in checks)
 ready=bool(e['parentFinalEvidenceReady'] and apiReady and allChecks and all(x['passed'] for x in required.values()) and e['gitDiffCheckPassed'])
 gates={'schema':'B1-provider-height-gates/v193','complete':ready,'scope':'Provider4 data interface with curve selector and conditional LocalHeightData11 assembly only','all15OriginalFullFactsMatchAcceptedClosure':True,'fourASTCommandsByteExact':True,'residueCharSourceFullProofCount':1,'residueCharSourceBoundaryCount':45,'nativeInventoryOwnerFactCount':28,'nativeInventoryIsCorrespondenceAcceptance':False,'requiredJobs':required,'JSONEvidence':checks,'twoPrivateDefinitionFinalGETsExact':apiReady,'oneFreshBlindReadbackEnglishFreezeVerified':True,'translationsCountAsAdditionalIndependentAudits':False,'gitDiffCheckPassed':e['gitDiffCheckPassed'],'archiveReopenedSHA256Verified':False,**LIMITS}
 status='ACCEPTED_PROVIDER4_CURVE_AND_CONDITIONAL_LOCALHEIGHTDATA11_ONLY' if ready else 'PREFLIGHT_PENDING_PARENT_TERMINAL_CI_AND_API_EVIDENCE'
 ledger={'schema':'B1-provider-height-source-ledger/v193','status':status,'complete':ready,'sourceRoots':['Iut.Tripod.CurveProviders','Iut.Tripod.CurveProviders.curve','Iut.residueChar_prime','Iut.EllipticCurveData.localHeightData'],'scope':gates['scope'],'nativeMappedDeclarationCount':16,'acceptedBoundaryCount':21,'actualNativeOwnerFactCount':28,'nativeAutoCompanionsLegalityOnlyCount':12,'constructorArgumentReportCount':12,'deepTYPEBinderInfoDifferenceCount':0,'finalNativeReviewJobId':'ci-019381-0a72a1e8','nativeSharedProjectionJobId':'ci-019364-13c9c9f1','sourceWholePropCertificateJobId':'ci-019368-2bcf746f','sourceFacts':{n:pin(SRC/'source'/('fact-'+n.replace('.','_')+'.json')) for n in selected},'sourceResidueCharEvidence':{'fullProofCount':1,'boundaryCount':45,**pin(PRIME/'actual/actual-facts.json')},'publication':publication,'elevenConstructorArguments':pin(SRC/'audit/localHeightData-eleven-constructor-arguments.json'),'fourProviderFields':pin(SRC/'audit/provider-four-fields.json'),'sourceWholePropProofCompatibilityEvidence':checks,'oldTorsionFreeCertificateReusedForNewResidueCharLemma':False,'sourceHFQIdentifiedWithFree':False,'sourceProofByteIdentityWithNativeClaimed':False,'producerConsumers':[{'producer':'conditional curveOf','consumer':'CurveProviders.curve','integrated':True},{'producer':'CurveProviders torsionFinite3/torsionFinite5','consumer':'CurveProviders.curve arguments','integrated':True},{'producer':'CurveArithmetic and TateInputs arguments','consumer':'EllipticCurveData.localHeightData eleven constructor fields','integrated':True},{'producer':'localHeightData','consumer':'future P.localData / P.h = localData.height','integrated':False,'countedAsAcceptedThisUnit':False}],'pendingSupplierIsLaterDraftOnly':True,'referIutAdaptationProgress':{'approximatePercent':70,'precision':'approximate','completedUnitExpectedRangePercent':[70,71],'mathematicalParentCompletionClaimed':False},**LIMITS}
 dump(O/'SOURCE_LEDGER.json',ledger)
 for name,data in {'ci-history.json':{'attempts':ci,'requiredJobs':required,'resourceInterpretation':'Process-tree physical RSS/PSS in bytes; unknown values remain null. CPU total=user+system. Timeout wall duration is only a lower bound.'},'prebuilt-pins.json':{'inputs':pins,'cacheDeletionAllowed':False},'prior-archive-references.json':prior,'source-byte-checks.json':{'checks':bytechecks},'gates.json':gates,'cleanup-whitelist.json':{'cleanupPerformed':False,'entries':[],'mustKeep':[pin(p) for p in CAN.values()],'cacheDeletionAllowed':False,'recursiveDeletionAllowed':False},'registry.patch.json':[{'op':'add','path':'/reference_source_preparation/b1_provider_height_unit','value':{'status':status,'complete':ready,'sourceLedger':str(DEST/'SOURCE_LEDGER.json'),'publication':publication,**LIMITS}}]}.items():dump(O/name,data);add(O/name,'delivery/'+name)
 (O/'plan-addition.txt').write_text('- ['+('x' if ready else ' ')+'] Provider4 数据接口与 curve selector、条件 LocalHeightData11 装配：保留四字段依赖、十一构造参数、真实 height 消费链；residueChar 来源为1完整proof+45边界。'+('本轮 CI/公理审查及双私有 definition 精确GET已验收。' if ready else '等待本轮证明兼容证书、完整原生对应、项目门禁及双私有GET。')+'Provider存在性、TateInputsSupply、P.tate/localData/h 接线及 B1/S2-04仍未完成。\n')
 for p in sorted(O.iterdir()):
  if p.is_file() and (p.suffix=='.py' or p.name in {'final-evidence.json','SOURCE_LEDGER.json','README.zh.md','plan-addition.txt'}):add(p,'delivery/'+p.name)
 for item in e['extraFiles']:add(item['path'],item['member'])
 contents={m:{'sha256':sha(p),'bytes':p.stat().st_size,'originalPath':str(p)} for m,p in sorted(files.items())};dump(O/'archive-manifest.json',{'schema':'B1-provider-height-archive/v193','members':contents,'priorLargeSourceBlobsRepacked':False,'pendingSupplierIncluded':False})
 if not finalize:
  summary={'preflight':'passed','members':len(contents)+1,'bytes':sum(x['bytes'] for x in contents.values()),'compressionPerformed':False,'acceptanceReady':ready,'missingRequiredJobs':[k for k,x in required.items() if not x['passed']],'publication':publication};dump(O/'preflight-report.json',summary);print(json.dumps(summary,ensure_ascii=False,indent=2));return
 assert ready,'Final evidence incomplete';assert not ARC.exists(),'Frozen archive exists; no recompression'
 with ARC.open('xb') as raw:
  with gzip.GzipFile(fileobj=raw,mode='wb',mtime=0,compresslevel=6) as gz:
   with tarfile.open(fileobj=gz,mode='w') as tar:
    for m,p in sorted({**files,'archive-manifest.json':O/'archive-manifest.json'}.items()):
     info=tar.gettarinfo(str(p),arcname=m);info.mtime=0;info.uid=info.gid=0;info.uname=info.gname=''
     with p.open('rb') as f:tar.addfile(info,f)
 with tarfile.open(ARC,'r:gz') as tar:
  assert set(tar.getnames())==set(contents)|{'archive-manifest.json'}
  for m,x in contents.items():assert hashlib.sha256(tar.extractfile(m).read()).hexdigest()==x['sha256'],m
  assert hashlib.sha256(tar.extractfile('archive-manifest.json').read()).hexdigest()==sha(O/'archive-manifest.json')
 arc={'path':str(DEST/ARC.name),'sha256':sha(ARC),'bytes':ARC.stat().st_size,'members':len(contents)+1};ledger['archive']=arc;dump(O/'SOURCE_LEDGER.json',ledger)
 patch=read(O/'registry.patch.json');patch[0]['value']['archive']=arc;dump(O/'registry.patch.json',patch)
 gates.update({'archiveReopenedSHA256Verified':True,'archiveSHA256':arc['sha256']});dump(O/'gates.json',gates)
 dump(O/'delivery-manifest.json',{p.name:{'sha256':sha(p),'bytes':p.stat().st_size} for p in sorted(O.iterdir()) if p.is_file() and p.name!='delivery-manifest.json'})
 print(json.dumps({'archive':str(ARC),**arc,'complete':True},ensure_ascii=False,indent=2))
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--finalize',action='store_true');a=p.parse_args();main(a.finalize)
