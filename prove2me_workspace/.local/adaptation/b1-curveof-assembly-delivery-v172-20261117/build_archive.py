#!/usr/bin/env python3
"""Freeze the conditional CurveOf carrier/assembly unit after parent terminal evidence.
Writes only this /tmp directory. No CI, compiler, API, Git, cleanup or workspace writes.
"""
from pathlib import Path
import argparse,gzip,hashlib,json,tarfile
W=Path('/home/admin-wsl/Coq/abc/prove2me_workspace');A=W/'.local/adaptation';H=A/'main-chain-open-20261116'
O=Path('/tmp/p2m-b1-curveof-assembly-delivery-v172-20261117');DEST=A/'b1-curveof-assembly-delivery-v172-20261117'
SRC=Path('/tmp/p2m-b1-curveof-assembly-v166-20261117');NATIVE=Path('/tmp/p2m-b1-curveof-native-audit-v168-20261117');EDITORIAL=Path('/tmp/p2m-b1-curveof-assembly-publication-v170-20261117');CHECKPOINT=Path('/tmp/p2m-b1-curveof-refspan-v171-20261117');STAGE=A/'b1-curveof-assembly-v167-20261117'
CAN={'carrier':W/'Definitions/Def_AbcAdaptation_Reference_Iut_Tripod_CurveOfCarrier.lean','assembly':W/'Definitions/Def_AbcAdaptation_Reference_Iut_Tripod_CurveOf.lean'}
STANDARD={'propext','Classical.choice','Quot.sound'}
LIMITS={'torsionFinitenessItselfProved':False,'CurveArithmeticSupplied':False,'GaloisPropertySupplied':False,'unconditionalProviderExistenceProved':False,'B1Completed':False,'S204Completed':False}
ARC=O/'b1-curveof-assembly-evidence-v172.tar.gz'
def read(p):return json.loads(Path(p).read_text())
def dump(p,j):Path(p).write_text(json.dumps(j,ensure_ascii=False,indent=2)+'\n')
def sha(p):
 h=hashlib.sha256()
 with Path(p).open('rb') as f:
  for b in iter(lambda:f.read(1024*1024),b''):h.update(b)
 return h.hexdigest()
def pin(p):return {'path':str(p),'sha256':sha(p),'bytes':Path(p).stat().st_size}
def exact(p,h):assert sha(p)==h,(str(p),h,sha(p))
def main(finalize):
 e=read(O/'final-evidence.json');assert not finalize or e['parentFinalEvidenceReady'] is True,'Parent terminal CI/API evidence and finalize signal are pending'
 PUB=Path(e['publicationDirectory']);AUD=Path(e['nativeAuditDirectory']);BLIND=Path(e['freshBlindDirectory']);NORM=Path(e['sourceNormalizationDirectory']);FINAL_EDITORIAL=Path(e['finalEditorialDirectory'])
 publication={}
 for label in ['carrier','assembly']:
  info=e['definitions'][label];d=PUB/info['directory'];payload=read(d/info['payload'])
  if not (d/info['finalGET']).exists() and not finalize:
   publication[label]={'status':'PENDING_FINAL_GET'};continue
  result=read(d/info['publicationResult']);got=read(d/info['finalGET']);validation=read(d/info['validation'])
  assert result['status']=='PUBLISHED' and result['visibility']==got['visibility']=='private' and payload['private']
  assert result.get('definition_id',result.get('theorem_id'))==got['definition_id']
  assert payload['definition']==got['definition']==CAN[label].read_text()
  assert payload['definition_name']==got['definition_name']==info['definitionName']
  assert payload['env']=='0df444a360eaa60ab8c11dca51a86af692955474'
  assert validation['allSubmittedFieldsExactlyReadBack'] and validation['private']
  for field in ['definition_name','definition_title','definition','natural_language_statement','source']:assert got[field]==payload[field]
  assert got['mathlib_rev']==payload['env'] and read(d/'publish-intent.json')['payloadSHA256']==sha(d/info['payload'])
  assert payload==read(FINAL_EDITORIAL/info['directory']/'payload.json')
  publication[label]={'definitionId':got['definition_id'],'publicationJobId':result['id'],'private':True,'finalGETExact':True}
 # Match all original exported facts against the accepted original closure.
 provenance=read(SRC/'source-provenance.json');facts=[read(p) for p in sorted((SRC/'source').glob('fact-*.json'))];assert len(facts)==23
 boundary=read(SRC/'source/boundary-full-facts.json');assert len(boundary)==8
 byname={r['name']:r for r in facts+boundary};assert len(byname)==31
 closure=Path(next(p['path'] for p in provenance['inputPins'] if p['path'].endswith('/actual-facts.jsonl')))
 matched=set()
 for line in closure.open():
  row=json.loads(line)
  if row.get('name') in byname:assert row==byname[row['name']];matched.add(row['name'])
 assert matched==set(byname)
 for r in byname.values():
  if 'actualTypeExpr' not in r:
   assert r['name']=='Iut.Tripod.legendre_isElliptic' and r['proofBodyExported'] is False;continue
  assert not r['hasSorryAx']
  for k in ['axioms','typeAxioms','valueAxioms']:assert set(r[k])<=STANDARD
  if r['actualValueExpr'] is not None:assert r['valueRead'] and r['kernelValueTypeMatchesActualTYPE']
 # Source bytes, accepted replay bytes, and the unique resolved use-site splice.
 for entry in provenance['inputPins']:exact(Path(entry['path']),entry['sha256'])
 normalized=Path(next(p['path'] for p in provenance['inputPins'] if p['path'].endswith('CurveOf.normalized.lean'))).read_bytes()
 replay=Path(next(p['path'] for p in provenance['inputPins'] if p['path'].endswith('B1SourceReplay.lean'))).read_bytes()
 ref=read(e['resolvedReference']);assert ref['sourceCommandBytesMatched'] and ref['referenceExtractedFromActualTermInfo'] and ref['probeOnlyDeclIdRewrite'] and not ref['originalUseSiteRewritten']
 expectedName=[[[[],'str','Iut'],'str','Tripod'],'str',"finiteDimensional_fieldOf'"]
 assert ref['actualResolvedReferences']
 for r in ref['actualResolvedReferences']:
  assert r['referenceNameExpr']==expectedName and not r['isBinder'] and r['parentDeclDisplay']=='Iut.Tripod.curveOf_refSpanProbeV166'
  assert [r['probeByteStart'],r['probeByteEnd']]==[ref['configuration']['probeReferenceByteStart'],ref['configuration']['probeReferenceByteEnd']]
 rewrite=read(e['referenceRewrite']);assert rewrite['acceptedReferenceJobId']==e['requiredJobs']['source-resolved-reference']['jobId']
 assert rewrite['verifiedOriginalResolvedNameExpr']==expectedName and rewrite['unchangedOutsideVerifiedSpan'] and not rewrite['sourceBinderOrHypothesisChanged']
 bytechecks=[]
 for command in provenance['sourceRecords']:
  original=Path(command['sourceBytes']['path']).read_bytes();exact(Path(command['sourceBytes']['path']),command['sourceBytes']['sha256'])
  r=command['originalRange'];rr=command['replayRange'];assert normalized[r['start']['offset']:r['end']['offset']]==original==replay[rr['start']['offset']:rr['end']['offset']]
  index=command['commandIndex'];actual=original
  if index==45:
   u,v=rewrite['originalCommandRelativeRange'];assert original[u:v]==b"finiteDimensional_fieldOf'"
   assert rewrite['originalIdentifier']=="finiteDimensional_fieldOf'" and rewrite['replacementIdentifier']=='finiteDimensional_fieldOfExtended'
   actual=original[:u]+b'finiteDimensional_fieldOfExtended'+original[v:]
   assert hashlib.sha256(original).hexdigest()==rewrite['originalCommandSHA256'] and hashlib.sha256(actual).hexdigest()==rewrite['changedCommandSHA256']
  assert actual in CAN['assembly' if index==45 else 'carrier'].read_bytes()
  bytechecks.append({'sourceCommandIndex':index,'originalSHA256':hashlib.sha256(original).hexdigest(),'integratedCommandSHA256':hashlib.sha256(actual).hexdigest(),'sourceAndAcceptedReplayBytesMatched':True,'onlyResolvedPublicReferenceChanged':index==45})
 assert [x['sourceCommandIndex'] for x in bytechecks]==[39,40,41,42,43,45]
 nine=read(SRC/'audit/curveOf-nine-constructor-consumers.json');assert nine['allNineSourceArgumentsPresent'] and len(nine['arguments'])==9
 helpers=read(SRC/'audit/generated-proof-parameter-closure.json');assert len(helpers)==4 and all(x['fullTypeAndValuePreservedInSourceFact'] for x in helpers)
 assert [x['binderInfo'] for x in byname['Iut.Tripod.curveOf']['telescope']['binders']]==['default']*3
 assert [x['binderInfo'] for x in byname['Iut.Tripod.curveOf._proof_1']['telescope']['binders']]==['default']*3
 # Inventory is evidence of actual names; acceptance requires the separate kernel review.
 inventory=read(AUD/e['nativeInventory']);assert inventory['schema']=='B1-curveOf-native-actual-inventory/v168' and inventory['ownedCount']==9
 report=read(AUD/e['nativeReview']);assert report['status']=='accepted' and report['correspondenceAccepted']
 for k in ['fullSourceProjectClosureCheckedUnderBoundaries','originalSourceMathlibNamesPreservedInOriginalFacts','completeExplicitXH3H5AndNineConstructorFieldsRetained','guardedOriginalSourceOnlyProofExplicitlyExpanded']:assert report[k]
 for k in ['newAssumptionsIntroduced','unmappedProjectProofsSilentlyExpanded','repeatedPriorBoundaryCompilationClaimed','nonPropositionalDataReplaced']:assert report[k] is False
 rows=report['reports'];assert len(rows)==9 and len(report['actualPairs'])==30 and len(report['nativeActualFacts'])==9 and report['mappedNewDeclarationCount']==9 and report['sourceOnlyProofCount']==1
 for r in rows:
  assert not r['hasSorryAx'] and set(r['axioms'])<=STANDARD
  assert all(r[k] for k in ['completeTYPEKernelEqual','strictPublicForallBinderInfoEqual','completeValueKernelEqual','instanceRegistrationEqual','completeComputationMetadataEqual'])
  assert all(p['completeDomainKernelEqual'] for p in r['publicParameterDomainReports'])
  assert not r['rawSourceProofByteIdentityClaimed']
 rawDifferences=[r for r in rows if not r['strictCompleteTYPEBinderInfoEqual']]
 assert len(rawDifferences)==2 and all(r['deepRawTYPEBinderInfoDifferenceRetained'] for r in rawDifferences)
 assert report['rawSemiringProjectionDifference']['dataExpressionReplaced'] is False and report['rawSemiringProjectionDifference']['completeTYPEAndPublicParameterDomainsKernelEqual']
 assert report['instanceCount']==2 and all(report[k]==0 for k in ['structureCount','projectionCount','constructorCount','recursorCount','recursorRuleCount'])
 args=report['constructorArgumentReports'];assert len(args)==9 and all(x['completeArgumentKernelEqual'] for x in args)
 assert [x['field'] for x in args]==['F','fieldF','numberFieldF','Fbar','fieldFbar','algebraFbar','isAlgClosure','E','isElliptic']
 bound=report['configuration']['boundInputsBinding']['contents'];assert len(bound['sourceRecords'])==9 and len(bound['sourceOnlyProofRecords'])==1 and len(bound['acceptedBoundaryPairs'])==21
 for field,sourcePath in [('sourceNineConstructorArguments','audit/curveOf-nine-constructor-consumers.json'),('sourceGeneratedProofTelescopes','audit/generated-proof-parameter-closure.json'),('sourceCompleteActualEdges','source/assembly-complete-actual-edges.json'),('sourceProjectClosure','audit/source-project-closure-plan.json')]:assert bound[field]==read(SRC/sourcePath)
 owned={r['name'] for r in inventory['records'] if r['nameExpr'] in inventory['ownedNameExprs']}
 assert len(owned)==9 and owned=={x['target'] for x in report['reports']}

 assert all(byname[x['name']]==x for x in bound['sourceRecords']+bound['sourceBoundaryFullFacts'])
 sourceOnly=bound['sourceOnlyProofRecords'][0];rawOnly=byname['Iut.Tripod.curveOf._proof_2'];assert all(sourceOnly[k]==v for k,v in rawOnly.items())
 spr=report['sourceOnlyProofReport'];assert spr['originalActualTYPE']==rawOnly['actualTypeExpr'] and spr['originalActualValue']==rawOnly['actualValueExpr']
 for key in ['originalCompleteTYPEKernelCheckedIsProp','originalCompleteValueKernelCheckedAgainstTYPE','isClosedZeroUniverseNoninstanceTheoremWithNoForall']:assert spr[key]
 assert spr['targetConstantInvented'] is False and set(spr['valueAxioms'])<=STANDARD and len(spr['expansions'])==1
 cert=read(NORM/e['sourceNormalizationCertificate']);assert cert==report['explicitSourceWholePropProofNormalizationCertificate']
 assert cert['sourceRecord']==byname['Iut.Tripod.instIsTorsionFreeSubtypeQbarMemIntermediateFieldRat_b1SourceReplay']
 for key in ['wholeProofKernelDefEq','wholeProofEqualityCertificateKernelChecked','sourceKernelNormalizationChecked','sameWholePropTYPEKernelChecked','originalWholeProofKernelChecked']:assert cert[key]
 for key in ['usedAcceptedPublicFreeProofFallbackAfterExactPreflight','sourceASTOrBodyEdited','rawSourceProofByteIdentityClaimed','nonPropositionalDataReplacementUsed','newAxiomsIntroduced','nativeCorrespondenceAccepted']:assert cert[key] is False
 for key in ['rawAxioms','normalizedAxioms','certificateAxioms']:assert set(cert[key])<=STANDARD
 assert cert['actualNativeCandidateSourcePreflightMissingNames']==[] and cert['actualNativeCandidateSourcePreflightUniverseArityDifferences']==[]
 frozen=report['frozenSourceQueryBinding'];exact(Path(frozen['path']),frozen['sha256']);assert frozen['sha256']=='466ac98ff762f9a04a27d94255bac25bd971f457aa3b50e82e1272d36d3def41'
 external=report['sourceFirstVersionExternalMetadataAcceptance'];assert external['addedSourceMetadataGuardsClaimedCompiled'] is False and external['completeNativeRecordJSONEqualsActualInventory'] and external['actualNativeRecordNameOwnerKindInstanceVerified']
 assert external['fixedSourceQuerySHA256']==frozen['sha256']
 nativeRows=[r for r in inventory['records'] if r['name']==cert['configuration']['nativeRecord']['name']];assert len(nativeRows)==1 and nativeRows[0]==cert['configuration']['nativeRecord']==external['actualNativeRecord']
 def onlyReverseQbar(node):
  if isinstance(node,list):return [onlyReverseQbar(x) for x in node]
  if not isinstance(node,dict):return node
  out={k:onlyReverseQbar(v) for k,v in node.items()}
  if node.get('kind')=='const' and node['name']==cert['configuration']['nativeQbarNameExpr']:out['name']=cert['configuration']['sourceQbarNameExpr']
  return out
 assert onlyReverseQbar(nativeRows[0]['elaboratedExpr'])==cert['actualNativeCandidateAfterOnlyQbarReverseTYPE']
 assert onlyReverseQbar(nativeRows[0]['valueExpr'])==cert['actualNativeCandidateAfterOnlyQbarReverseValue']
 assert read(external['rootExternalVerificationBinding']['pin']['path'])==external['rootExternalVerificationBinding']['contents'];exact(Path(external['rootExternalVerificationBinding']['pin']['path']),external['rootExternalVerificationBinding']['pin']['sha256'])
 reused=report['reusedCompleteECDConstructorRecursorAndNumberFieldAcceptance'];assert reused['fullECD12AcceptanceJob']=='ci-018597-7df8415e' and reused['numberFieldAcceptanceJob']=='ci-018574-8f1900b3' and reused['newBoundaryNormalizationsApplied'] is False
 for key in ['fullECD12AcceptanceBinding','numberFieldAcceptanceBinding','deliveryLedgerBinding']:exact(Path(reused[key]['path']),reused[key]['sha256'])
 blind=read(BLIND/e['freshBlindAudit']);assert blind['audit_count']==1 and blind['translations_from_frozen_english']
 for key in ['source_sha256','mathlib_examined_file_sha256','rule_sha256']:
  for path,h in blind[key].items():exact(Path(path),h)
 for name,h in blind['artifact_sha256'].items():exact(BLIND/name,h)
 exact(BLIND/'english-freeze.json',blind['english_freeze_sha256']);freeze=read(BLIND/'english-freeze.json');assert freeze['status']=='frozen before translations'
 for name,h in freeze['sha256'].items():exact(BLIND/name,h)
 files={}
 def add(p,member):
  p=Path(p);assert p.is_file(),str(p)
  assert p.name not in {'actual-facts.jsonl','root-source-facts-v106.json'},('Do not repack large old source libraries',str(p))
  assert member not in files or files[member]==p;files[member]=p
 def tree(root,prefix):
  root=Path(root);assert root.is_dir(),str(root)
  for p in sorted(root.rglob('*')):
   if p.is_file() and '__pycache__' not in p.parts:add(p,prefix+'/'+str(p.relative_to(root)))
 for root,prefix in [(SRC,'source-preparation-v166'),(NATIVE,'native-audit-draft-v168'),(EDITORIAL,'editorial-v170'),(CHECKPOINT,'ref-checkpoint-v171'),(STAGE,'staged-unit'),(AUD,'actual-native-audit'),(BLIND,'fresh-blind'),(PUB,'publication'),(NORM,'source-whole-prop-normalization'),(FINAL_EDITORIAL,'final-editorial-v177')]:tree(root,prefix)
 uncompiled=[]
 draft178=Path('/tmp/p2m-b1-curveof-native-audit-v178-20261117')
 for p in sorted(draft178.iterdir()):
  if not p.is_file():continue
  h=sha(p);same=[m for m,q in files.items() if sha(q)==h]
  if same:members=same
  else:
   m='uncompiled-native-audit-v178/'+p.name;add(p,m);members=[m]
  uncompiled.append({'originalPath':str(p),'sha256':h,'archiveMembers':members,'submittedAsV178CI':False,'classification':'UNCOMPILED_STRICT_DEEP_RAW_TYPE_DRAFT_NOT_A_FAILED_JOB'})
 dump(O/'uncompiled-draft-history.json',{'v178':uncompiled,'v168QuerySubmittedAsFullNativeReview':False});add(O/'uncompiled-draft-history.json','delivery/uncompiled-draft-history.json')
 guardedDraft=Path('/tmp/p2m-b1-curveof-native-audit-v182-20261117')
 for name in ['QueryCurveOfTorsionFreeSourceNormalizationV182.lean','source-normalization.config.json','handoff-manifest.json']:
  add(guardedDraft/name,'later-uncompiled-source-metadata-guards/'+name)
 lateQuery=guardedDraft/'QueryCurveOfTorsionFreeSourceNormalizationV182.lean'
 assert sha(lateQuery)=='bd4e7f06e1d589d63096085e2dc410e2dbd056d1b4f4f026191bde94be647c63' and sha(lateQuery)!=frozen['sha256']
 versionHistory={'compiledFirstSourceQuery':{**frozen,'jobId':'ci-018988-44cac626','containsLaterMetadataGuards':False},'laterMetadataGuardsDraft':{**pin(lateQuery),'compiled':False},'metadataActuallyVerifiedExternally':external['rootExternalVerificationBinding'],'sourceKernelTYPEAndWholeProofChecksPassedInFirstQuery':True,'nonPropositionalDataReplacementUsed':False}
 dump(O/'source-query-version-history.json',versionHistory);add(O/'source-query-version-history.json','delivery/source-query-version-history.json')
 for p in CAN.values():add(p,'integrated-sources/'+str(p.relative_to(W)))
 for record in provenance['inputPins']:
  if record['bytes']<5_000_000:add(Path(record['path']),'small-source-inputs/'+Path(record['path']).name)
 for path in [e['resolvedReference'],e['referenceRewrite']]:add(Path(path),'final-source-reference/'+Path(path).name)
 for p in [W/'lean-toolchain',W/'lakefile.lean',W/'lake-manifest.json']:add(p,'build-configuration/'+p.name)
 # Include every attempt in this unit, including source timeouts and their original inputs.
 resultpaths=set()
 for pattern in ['b1-curveof-carrier-*-result.json','b1-curveof-resolved-ref-*-result.json','b1-curveof-assembly-*-result.json','b1-curveof-native-*-result.json','b1-curveof-required-*-result.json','b1-curveof-source-*-result.json']:resultpaths.update(H.glob(pattern))
 resultpaths.update(Path(x['result']) for x in e['requiredJobs'].values())
 ci=[];jobs={};pins={}
 for p in sorted(resultpaths):
  j=read(p);req=j['request'];r=j.get('result') or {};snap=r.get('snapshot') or {};manifest=snap.get('manifest') or req['worktree_manifest'];resources=j.get('resources',r.get('resources',{}));job=j['job_id'];jobs[job]=j
  assert req['exclusive'] and Path(req['workspace'])==W
  if j['status']=='succeeded':assert snap['workspace_mode']=='exclusive_worktree' and snap['snapshot_id'] is None and r['exit_code']==0
  member='ci/'+job+'/'+p.name;add(p,member);stem=p.name.removesuffix('-result.json')
  for folder in [p.parent,H]:
   for recordedStem in {stem,manifest.get('purpose',stem)}:
    for kind in ['request','submit','logs','progress-logs']:
     q=folder/(recordedStem+'-'+kind+'.json')
     if q.is_file():add(q,'ci/'+job+'/'+q.name)
  for path in r.get('artifacts',[]):
   q=Path(path);add(q,'ci/'+job+'/artifacts/'+q.name)
  for path,h in manifest.get('input_hashes',{}).items():
   if path.endswith(('.olean','.ilean','.ir')):pins[path]=h
  cpu=resources.get('cpu_time_seconds')
  if cpu is not None:assert abs(cpu-resources['cpu_user_seconds']-resources['cpu_system_seconds'])<1e-7
  ci.append({'jobId':job,'status':j['status'],'exitCode':r.get('exit_code'),'inputHEAD':manifest.get('head'),'inputSHA256':manifest.get('source_sha256'),'inputHashes':manifest.get('input_hashes',{}),'workspace':req['workspace'],'workspaceMode':snap.get('workspace_mode'),'snapshotId':snap.get('snapshot_id'),'requestExclusive':True,'actualArguments':r.get('actual_arguments'),'expectedDuration':req['expected_duration'],'expectedMemory':req['expected_memory'],'observedCompileTimeSeconds':j.get('compile_time_seconds'),'observedCompileTimeIsOnlyLowerBound':j['status']=='timeout','resources':{k:resources.get(k) for k in ['wall_time_seconds','cpu_time_seconds','cpu_user_seconds','cpu_system_seconds','peak_rss_bytes','peak_pss_bytes']},'resourceSource':resources.get('source',resources.get('memory_decision')),'degraded':resources.get('degraded'),'diagnostics':r.get('diagnostics'),'error':r.get('error'),'timeoutCauseBeyondReceiptClaimed':False,'receiptMember':member,'receiptSHA256':sha(p)})
 required={'carrier-leaf','carrier-artifact','source-resolved-reference','assembly-leaf','assembly-artifact','native-inventory','native-review','mandatory-project-gates','source-whole-prop-normalization'};assert set(e['requiredJobs'])==required
 for category,x in e['requiredJobs'].items():
  j=jobs[x['jobId']];assert j['status']=='succeeded' and j['result']['exit_code']==0,(category,x)
  if x.get('source'):assert j['result']['snapshot']['manifest']['input_hashes'][x['source']]==sha(Path(x['source']))
 assert report['sourceNormalizationSucceededReceipt']==jobs[e['requiredJobs']['source-whole-prop-normalization']['jobId']]
 normBinding=bound['sourceProofNormalizationBinding'];assert normBinding['sourceNormalizationJob']==e['requiredJobs']['source-whole-prop-normalization']['jobId'] and normBinding['contents']==cert
 exact(Path(normBinding['pin']['path']),normBinding['pin']['sha256']);exact(Path(normBinding['receiptPin']['path']),normBinding['receiptPin']['sha256'])
 timeout=[x for x in ci if x['jobId']=='ci-018841-8fcfd783'];assert len(timeout)==1 and timeout[0]['status']=='timeout' and timeout[0]['observedCompileTimeIsOnlyLowerBound']
 probe=jobs[e['requiredJobs']['source-resolved-reference']['jobId']]
 for checkpoint in ['imports complete','command elaboration start','command elaboration end','InfoTree extraction start','InfoTree extraction end','resolved-reference JSON written']:assert 'CURVEOF_REFSPAN_V171: '+checkpoint in probe['result']['stdout']
 mandatory=jobs[e['requiredJobs']['mandatory-project-gates']['jobId']]
 assert e['mandatoryStdoutRequired'],'Bind actual mandatory standard-axiom output markers'
 for marker in e['mandatoryStdoutRequired']:assert marker in mandatory['result']['stdout']
 restoration=[]
 filehash={}
 for member,p in files.items():filehash.setdefault(sha(p),[]).append(member)
 for entry in ci:
  for original,h in entry['inputHashes'].items():
   if not original.endswith(('.lean','.json')):continue
   p=Path(original)
   if p.is_file() and sha(p)==h:continue
   candidates=filehash.get(h,[]);assert candidates,('Historical actual input missing',entry['jobId'],original,h)
   restoration.append({'jobId':entry['jobId'],'originalPath':original,'sourceSHA256':h,'archiveMembers':candidates,'classification':'HISTORICAL_INPUT_NOT_FINAL_ACCEPTANCE'})
 prior=[]
 for spec in e['priorArchives']:
  p=Path(spec['archive']);mp=Path(spec['manifest']);ledger=Path(spec['ledger']);mj=read(mp);arcsha=mj.get('archiveSHA256') or read(ledger)['archive']['sha256'];exact(p,arcsha)
  entries=mj.get('files',[]);refs=[x for x in entries if any(n in x.get('path','') for n in ['root-source-facts-v106.json','closure-v111/actual-facts.jsonl','closure-v111/actual-edges.jsonl'])]
  prior.append({'archive':str(p),'archiveSHA256':arcsha,'requiredMembers':refs,'priorLargeSourceBlobsRepacked':False});add(mp,'prior-manifests/'+p.parent.name+'.json')
 apiReady=all(x.get('finalGETExact') for x in publication.values())
 gates={'schema':'B1-complete-conditional-CurveOf-gates/v172','complete':bool(apiReady and e['parentFinalEvidenceReady']),'scope':'Carrier support and complete conditional CurveOf data only','all23FullFactsAnd8OriginalBoundaryRecordsMatchAcceptedClosure':True,'sixASTSourceCommandsRetainedExceptOneResolvedPublicUseSite':True,'native9ActualCorrespondencesPlus1SourceOnlyProofAnd21ExistingBoundaryMapAccepted':True,'wholePropSourceNormalizationCertificateBound':True,'twoDeepRawTYPEBinderInfoDifferencesRetained':True,'nonPropositionalDataReplaced':False,'nineConstructorArgumentsAndFourGeneratedProofClosuresRetained':True,'explicitXH3H5Retained':True,'sourceNativeProofTermByteIdentityClaimed':False,'freshBlindFrozenEnglishSHA256Checked':True,'twoPrivateDefinitionFinalGETsExact':apiReady,'fourPublicRootAxiomPrintsExact':True,'nineGuardLogNamesAreLiteralPlaceholders':True,'mergedMandatoryProjectGatesPassed':True,'archiveReopenedSHA256Verified':False,**LIMITS}
 compact={'source-byte-checks.json':{'checks':bytechecks},'ci-history.json':{'attempts':ci,'requiredJobs':e['requiredJobs'],'resourcesInterpretation':'Physical process-tree RSS/PSS bytes; missing values unknown. CPU total=user+system. Timeout duration is a lower bound only.','timeoutCauseClaimed':False,'mandatoryLogInterpretation':'Four public #print roots list actual axioms; nine extra log lines contain literal placeholders, while run_meta guards and final native JSON check actual nine declarations.'},'prebuilt-pins.json':{'inputs':pins,'cacheDeletionAllowed':False},'historical-ci-input-restoration.json':{'restorationMap':restoration},'prior-archive-references.json':{'references':prior,'restoreRequiresExistingPriorArchives':True},'gates.json':gates}
 for name,data in compact.items():dump(O/name,data);add(O/name,'delivery/'+name)
 for p in sorted(O.iterdir()):
  if p.is_file() and (p.suffix=='.py' or p.name=='final-evidence.json'):add(p,'delivery/'+p.name)
 contents={m:{'sha256':sha(p),'bytes':p.stat().st_size,'originalPath':str(p)} for m,p in sorted(files.items())};dump(O/'archive-manifest.json',{'schema':'B1-complete-conditional-CurveOf-archive/v172','members':contents,'priorLargeSourceBlobsRepacked':False})
 if not finalize:
  preflight={'preflight':'passed','members':len(contents)+1,'bytes':sum(x['bytes'] for x in contents.values()),'compressionPerformed':False,'parentFinalEvidenceReady':e['parentFinalEvidenceReady'],'twoFinalAPIGetResultsReady':apiReady,'publication':publication}
  dump(O/'preflight-report.json',preflight);print(json.dumps(preflight,indent=2));return
 assert not ARC.exists(),'Frozen archive already exists; do not recompress'
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
 arcsha=sha(ARC)
 def ref(member):return {'archive':str(DEST/ARC.name),'archiveSHA256':arcsha,'member':member,'memberSHA256':contents[member]['sha256']}
 def memberFor(path):
  hits=[m for m,p in files.items() if p==Path(path)];assert hits,str(path);return sorted(hits)[0]
 ledger={'schema':'B1-complete-conditional-CurveOf-source-ledger/v172','status':'REGISTERED_CARRIER_SUPPORT_AND_COMPLETE_CONDITIONAL_CURVEOF_DATA_ONLY','complete':True,'archive':{'path':str(DEST/ARC.name),'sha256':arcsha,'bytes':ARC.stat().st_size,'members':len(contents)+1},'publication':publication,'sourceRoot':'Iut.Tripod.curveOf','targetRoot':'AbcAdaptation.Tripod.curveOf','explicitArguments':['x:Pt','h3:TorsionFinite x.1 3','h5:TorsionFinite x.1 5'],'nativeMappedDeclarationCount':9,'sourceOnlyProofCount':1,'sourceWholePropNormalizationCertificate':ref(memberFor(NORM/e['sourceNormalizationCertificate'])),'normalizationSourceQuerySHA256':frozen['sha256'],'laterTmpSourceMetadataGuardsClaimedCompiled':False,'deepRawTYPEBinderInfoDifferences':[{'source':r['source'],'target':r['target']} for r in rawDifferences],'nonPropositionalDataReplaced':False,'source23FullFactsAnd8OriginalBoundaryRecords':{'facts':{read(p)['name']:ref('source-preparation-v166/source/'+p.name) for p in sorted((SRC/'source').glob('fact-*.json'))},'boundaryFullFacts':ref('source-preparation-v166/source/boundary-full-facts.json')},'actualNativeReview':ref(memberFor(AUD/e['nativeReview'])),'actualInventory':ref(memberFor(AUD/e['nativeInventory'])),'resolvedUseSite':ref(memberFor(e['resolvedReference'])),'referenceRewrite':ref(memberFor(e['referenceRewrite'])),'producerConsumers':[{'producer':'AbcAdaptation.Tripod.finiteDimensional_fieldOfExtended','consumer':'AbcAdaptation.Tripod.curveOf NumberField support','consumption':'resolved source use-site, actual complete TYPE/value and 9 constructor fields audited'},{'producer':'Carrier theorem/instance support','consumer':'AbcAdaptation.Tripod.curveOf E/isElliptic/algebraic-closure fields','consumption':'actual bound native Expr/constructor argument reports'},{'producer':'AbcAdaptation.Tripod.curveOf','downstreamProviderConsumer':'PENDING_NOT_COUNTED_AS_INTEGRATED'}],'nineConstructorFields':ref('source-preparation-v166/audit/curveOf-nine-constructor-consumers.json'),'fourGeneratedProofClosures':ref('source-preparation-v166/audit/generated-proof-parameter-closure.json'),'priorArchives':prior,**LIMITS};dump(O/'SOURCE_LEDGER.json',ledger)
 dump(O/'cleanup-whitelist.json',{'schema':'B1-complete-conditional-CurveOf-cleanup-whitelist/v172','cleanupPerformed':False,'entries':[],'unitHasNoSolFiles':True,'mustKeep':[pin(p) for p in CAN.values()],'cacheDeletionAllowed':False,'otherSolutionDeletionAllowed':False,'recursiveDeletionAllowed':False})
 dump(O/'registry.patch.json',[{'op':'add','path':'/reference_source_preparation/b1_complete_conditional_curveof_unit','value':{'status':ledger['status'],'complete':True,'sourceLedger':str(DEST/'SOURCE_LEDGER.json'),'archive':ledger['archive'],'publication':publication,**LIMITS}}])
 (O/'plan-addition.txt').write_text('- [x] 完成 Carrier 来源支撑及完整条件 curveOf 数据迁移：保留 x/h3/h5、9 个构造字段及4个生成证明参数闭包；23原完整fact及8既有边界记录、9原生对应+1来源独有Prop支撑/21既有边界与wholeProp归一化证书、唯一resolved use-site、完整kernel/公理审查及两项私有definition精确GET已归档。该构造不提供 CurveArithmetic、Galois 或无条件provider存在性，不关闭B1/S2-04。\n')
 gates.update({'archiveReopenedSHA256Verified':True,'archiveSHA256':arcsha});dump(O/'gates.json',gates)
 dump(O/'delivery-manifest.json',{p.name:{'sha256':sha(p),'bytes':p.stat().st_size} for p in sorted(O.iterdir()) if p.is_file() and p.name!='delivery-manifest.json'})
 print(json.dumps({'archive':str(ARC),'sha256':arcsha,'bytes':ARC.stat().st_size,'members':len(contents)+1,'complete':True},indent=2))
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--finalize',action='store_true');args=p.parse_args();main(args.finalize)
