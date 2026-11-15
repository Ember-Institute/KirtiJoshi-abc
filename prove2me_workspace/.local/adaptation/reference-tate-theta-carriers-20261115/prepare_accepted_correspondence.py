#!/usr/bin/env python3
"""Bind this four-module unit to a real successful kernel audit only.

No compiler, CI, API, network or Git calls. Raw original Expr JSON is streamed
for SHA256 only. The compiler audit binds the lossless compact Expr input.
No candidate mapping or proposed generated declaration Name establishes identity.
"""
import argparse,hashlib,json,math
from pathlib import Path
SELECTED=78
NAMED_SELECTED=76
RECORDS=117
PROOF='TateCurvesTheta.TateParameter.tateJ.eq_1'
PARENT='TateCurvesTheta.TateParameter.tateJ'
STANDARD_PROOF='NumberField.RingOfIntegers.instHasFiniteQuotients'
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
def substitute_level(value,old,new):
 if isinstance(value,dict):
  if value.get('kind')=='param' and value.get('name')==old:return {'kind':'param','name':new}
  return {k:substitute_level(v,old,new) for k,v in value.items()}
 if isinstance(value,list):return [substitute_level(v,old,new) for v in value]
 return value
BINDER_SCOPE='unexpanded-original-exported-signature-after-named-relocation-vs-actual-target-type'
BINDER_CHECKS=['sourceSignatureBinderInfoSerializationValidated','sourceTargetSignatureBinderInfoInventoryEqual','sourceTargetSignatureBinderInfoPlacementEqual','expandedOriginalTypeKernelEqual']
DAG_FIELDS={'schema','stage','inventorySha256','graphSha256','candidateOriginalRecordCount','allActiveOriginalRecordCount','stageOriginalRecordCount','stageOriginalRecordNames','unusedArchivedCandidateNames','standardProofOverrideCount','entries','exprDag','allCompleteTypeValueKernelChecksPassed','allExprDagRootsStrictExprEqualRoundTrip','roundTripIncludesBinderNamesBinderInfoAndNumericNames'}
ACCEPTED_DAG_LEAVES=[
 ('ci-014497-4264b653','absnorm-support',19,'70daeab001bf0447e995ac65dde62b6e698ee95c0a5eb619c872aaa5c5829c91','81e6e6ebb232510e305432238b2cf7b54b7a4bda9d171cf6d244fa806d8373aa','78d66d4a35732cfdd36d962796b1efdae91a0f7cc288c7db72121945de303ca3'),
 ('ci-014507-f12c827f','finite-place',16,'89d124265edaaf0873e62c9233b9ff5cd8d42b9f802d8deedf31706d54e744cc','0c45975482b9696be35fc63cf050a4a3924ad19ebe665e9e16af3ca1b38f56a3','d4cc7dce5651a7eeacab78c9af63bd337a8b42e081129ee63ce99e3dfb8b7826')]
EXPECTED_DAG_PARTITIONS=[['Ideal.absNorm', 'Ideal.absNorm._proof_1', 'Ideal.absNorm._proof_2', 'Ideal.absNorm._proof_3', 'Ideal.absNorm_apply', 'Ideal.absNorm_eq_one_iff', 'Ideal.absNorm_ne_zero_iff', 'Int.instPartialOrder', 'Submodule.cardQuot', 'Submodule.cardQuot_apply', 'Submodule.cardQuot_bot', 'Submodule.cardQuot_eq_one_iff', 'Submodule.cardQuot_top', 'Valuation.instNontrivialSubtypeUnitsMemSubgroupValueGroupOfIsNontrivial', '_private.Mathlib.RingTheory.Ideal.Norm.AbsNorm.0.Submodule.cardQuot_eq_one_iff._simp_1_1', '_private.Mathlib.RingTheory.Valuation.Basic.0.Valuation.instNontrivialSubtypeUnitsMemSubmonoidValueMonoidOfIsNontrivial._simp_1', 'cardQuot_mul', 'cardQuot_mul_of_coprime', 'cardQuot_pow_of_prime'], ['NumberField.FinitePlace', 'NumberField.FinitePlace._proof_1', 'NumberField.FinitePlace.embedding', 'NumberField.FinitePlace.embedding._proof_1', 'NumberField.FinitePlace.embedding._proof_2', 'NumberField.FinitePlace.embedding._proof_3', 'NumberField.FinitePlace.embedding._proof_4', 'NumberField.FinitePlace.embedding._proof_5', 'NumberField.FinitePlace.maximalIdeal', 'NumberField.FinitePlace.maximalIdeal._proof_1', 'NumberField.HeightOneSpectrum.instNormedFieldValuedAdicCompletion', 'NumberField.HeightOneSpectrum.instRankOneAdicCompletion', 'NumberField.HeightOneSpectrum.one_lt_absNorm', 'NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal', 'NumberField.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV', '_private.Mathlib.NumberTheory.NumberField.Completion.FinitePlace.0.NumberField.HeightOneSpectrum.one_lt_absNorm._proof_1_1']]
def verify_signature_scope(row):
 require(row['binderInfoComparisonScope']==BINDER_SCOPE,'Unexpected original signature BinderInfo scope: '+row['original'])
 for key in BINDER_CHECKS:require(row[key] is True,'Missing original signature/expanded kernel check '+key+': '+row['original'])
 return {key:row[key] for key in BINDER_CHECKS}|{'binderInfoComparisonScope':BINDER_SCOPE}
def verify_adic_compatibility(config,audit,comparisons,unit,main_manifest=None):
 import mmap
 binding=config['adicSourceCompatibility'];report=audit['adicSourceCompatibility']
 require(binding['schema']=='tate-theta-adic-two-leaf-compatibility-v1' and report['schema']=='tate-theta-adic-source-dag-compatibility-result-v1','Unexpected exact adic DAG compatibility schema')
 for key,val in {'sourceDataCount':8,'genuineOriginalProofBodyCount':26,'nativeCardPowProofCount':1,'standardNativeProofCountIncludingRing':2,'unusedOriginalProofArchiveCount':15}.items():require(binding[key]==val,'Adic configured accounting differs: '+key)
 for key,val in {'requiredOriginalRecordCount':35,'genuineOriginalDataCount':8,'genuineOriginalProofBodyCount':26,'nativeCardPowProofCount':1,'standardNativeProofCountIncludingRing':2,'unusedOriginalProofArchiveCount':15}.items():require(report[key]==val,'Adic final accounting differs: '+key)
 require(report['completeTypeValueChecksPassed'] and report['publicRawSignatureBinderGuardsAndFullDataEqualityRemainRequired'] and audit['standardProofValueResolutionCount']==2,'Final complete DAG checks or standard proof accounting failed')
 require(len(binding['leaves'])==2,'Expected exact two accepted DAG leaves')
 entries=unique(report['entries'],'original','adic original');all_names=set();evidence=[];data=proofs=card=0
 historical=unit/'attempts/kernel-audit-v4/audit-config.json'
 for index,(leaf,expected) in enumerate(zip(binding['leaves'],ACCEPTED_DAG_LEAVES)):
  job,stage,count,artifact_sha,receipt_sha,source_sha=expected
  view=read(leaf['viewPath']);receipt=read(leaf['receiptPath'])
  require(view==leaf['viewContents'] and sha(leaf['viewPath'])==leaf['viewSha256'],'Accepted complete DAG view changed')
  require(receipt==leaf['receiptContents'] and sha(leaf['receiptPath'])==leaf['receiptSha256']==receipt_sha,'Accepted actual DAG receipt changed')
  require(view['schema']=='tate-theta-adic-receipt-bound-dag-view-v1' and view['receipt']=={'path':leaf['receiptPath'],'sha256':receipt_sha,'job_id':job},'DAG view receipt binding differs')
  require(receipt['job_id']==job and receipt['status']=='succeeded' and receipt['result']['exit_code']==0,'Exact DAG leaf did not succeed')
  request=receipt['request'];snapshot=receipt['result']['snapshot'];resources=receipt['resources']
  require(request['exclusive'] is True and snapshot['workspace_mode']=='exclusive_worktree' and snapshot['snapshot_id'] is None,'DAG leaf must use actual exclusive workspace')
  require(resources['peak_rss_bytes'] is not None and resources['peak_rss_bytes']<=16*1024**3,'DAG leaf exceeds physical RSS bound')
  manifest=request['worktree_manifest'];require(manifest['source_sha256']==source_sha,'Accepted DAG source query changed')
  old_config=request['environment']['NEXT_CARRIER_AUDIT_CONFIG']
  for path,expected_sha in manifest['input_hashes'].items():
   actual=historical if path==old_config else Path(path)
   require(sha(actual)==expected_sha,'Accepted DAG leaf input changed: '+str(actual))
  artifact=Path(view['originalArtifact']['path']);require(sha(artifact)==view['originalArtifact']['sha256']==artifact_sha,'Complete accepted original DAG artifact changed')
  fields=view['sourceFields'];spans=view['exactFieldByteSpans']
  require(set(fields)==set(spans)==DAG_FIELDS,'Incomplete exact DAG view field set')
  with artifact.open('rb') as f,mmap.mmap(f.fileno(),0,access=mmap.ACCESS_READ) as raw:
   for key,span in spans.items():
    start,end=span['start'],span['end'];require(0<=start<end<=len(raw),'Invalid exact DAG field byte span')
    content=raw[start:end];require(hashlib.sha256(content).hexdigest()==span['sha256'] and json.loads(content)==fields[key],'Original complete DAG field differs: '+key)
  require(fields['schema']=='tate-theta-adic-split-expr-dag-v1' and fields['stage']==stage and fields['stageOriginalRecordCount']==count and fields['allActiveOriginalRecordCount']==35 and fields['candidateOriginalRecordCount']==50,'DAG original stage scope differs')
  for key in ['allCompleteTypeValueKernelChecksPassed','allExprDagRootsStrictExprEqualRoundTrip','roundTripIncludesBinderNamesBinderInfoAndNumericNames']:require(fields[key] is True,'Actual leaf exact DAG check failed: '+key)
  for key in ['inventorySha256','graphSha256']:require(fields[key]==config[key],'Adic actual source provenance differs')
  rows=unique(fields['entries'],'name','accepted DAG recipe');expected_names=set(EXPECTED_DAG_PARTITIONS[index])
  require(set(rows)==expected_names|{STANDARD_PROOF} and len(rows)==count+1 and {name_text(n) for n in fields['stageOriginalRecordNames']}==expected_names,'Exact independently reviewed A/B partition differs')
  require(not all_names&expected_names,'A/B original coverage overlaps');all_names|=expected_names
  for name,row in rows.items():
   require(name_text(row['nameExpr'])==name and row['typeRoot']<len(fields['exprDag']['nodes']) and row['valueRoot']<len(fields['exprDag']['nodes']),'Complete source DAG roots/actual Name differ')
   if name==STANDARD_PROOF:continue
   actual=entries.get(name);require(actual is not None,'Final main omitted complete source DAG check: '+name)
   for key in ['levelParams','resolution','isProposition','typeRoot','valueRoot']:require(actual[key]==row[key],'Final main DAG row differs from accepted original: '+name+'.'+key)
   require(actual['originalName']==row['nameExpr'] and actual['standaloneTargetIdentity'] is None and actual['leafJob']==job and actual['viewPath']==leaf['viewPath'],'DAG report must retain actual source Name/value provenance without target identity')
   for key in ['completeTypeAndValueRetainedInExactExprDag','exactOriginalTypeKernelChecked','completeValueKernelCheckedAtExactOriginalType','publicConsumerFullKernelEqualityRequired']:require(actual[key] is True,'Main complete DAG check failed '+key+': '+name)
   require(set(actual['typeAxioms'])<=STANDARD and set(actual['valueAxioms'])<=STANDARD,'DAG type/value uses unexpected axioms: '+name)
   if name=='cardQuot_pow_of_prime':
    require(row['resolution']=='exact-original-type-native-theorem-proof' and row['isProposition'],'Only exact original CardPow may use native theorem proof');card+=1
   else:
    require(row['resolution']=='genuine-original-complete-body','Original source data/proof body was replaced: '+name)
    if row['isProposition']:proofs+=1
    else:data+=1
  bound_paths=[leaf['viewPath'],leaf['receiptPath'],str(artifact)]
  if main_manifest is not None:
   for path in bound_paths:require(main_manifest['input_hashes'].get(path)==sha(path),'Final main manifest does not bind exact accepted DAG evidence: '+path)
  evidence.append({'job_id':job,'viewPath':leaf['viewPath'],'viewSha256':leaf['viewSha256'],'receiptPath':leaf['receiptPath'],'receiptSha256':receipt_sha,'originalArtifact':view['originalArtifact'],'resources':resources,'exactFieldByteSpans':spans})
 require(set(entries)==all_names=={name_text(n) for n in binding['requiredOriginalNames']} and len(all_names)==35 and (data,proofs,card)==(8,26,1),'Final adic35 original data8/proof26/CardPow1 partition differs')
 require(not all_names&set(comparisons),'Internal source compatibility creates project named identities')
 for name,row in comparisons.items():
  verify_signature_scope(row)
  if not row['proofDeclaration'] and row['sourceRecord']['valueExpr'] is not None:require(row['computationalValueEqualityChecked'] and row['kernelValueEqual'] and not row['kernelPropositionalValueEquality'],'Public full computational kernel equality failed after adic source expansion: '+name)
 return report,{'schema':'tate-theta-independent-accepted-adic-dag-evidence-v1','leaves':evidence,'completeSourceRecordCount':35,'genuineDataCount':8,'genuineProofCount':26,'nativeCardPowProofCount':1,'uniqueNativeStandardProofCountIncludingRing':2}

QPROOF='Iut.AdmissiblePrimeData.qOrder._proof_1'
QPARENT='Iut.AdmissiblePrimeData.qOrder'
QTARGET='AbcAdaptation.Reference.'+QPROOF
PROJECT_PROOFS={PROOF,QPROOF}
QORDER_BASELINE_PINS={'diagnostic': 'c2464a038228b34449c915defa6c2acf9cc738726155983df38237ee79976f9d', 'receipt': '01fd884684fb94804638fee5555f9e18c615d8822af009c00fbb6024c93439ca', 'source': '2665384a6bd40629aeeceafdef75089a8a77792b4ebbb9f614a65d1db1665239'}
def expression_head(x):
 while x['kind']=='forall':x=x['body']
 while x['kind']=='app':x=x['fn']
 return name_text(x['name']) if x['kind']=='const' else x['kind']
def verify_qorder_proof(config,audit,comparisons,resolutions,configured,owned,wrappers,unit,manifest,sources):
 q=resolutions[QPROOF];binding=configured[QPROOF];record=q['sourceRecord']
 require(record==binding['sourceRecord'] and record['name']==QPROOF and record['selected'] and record['constantKind']=='theorem' and record['isProposition'] and not record['isInstance'] and record['valueExpr'] is not None,'Exact genuine selected Infinite source theorem/value differs')
 require(record['module']=='Iut.Cor312.ThetaData.AdmissiblePrime' and record['sourceSha256']==sources[QPROOF]['sourceSha256'] and q['originalName']==record['nameExpr'] and name_text(record['nameExpr'])==QPROOF,'Genuine Infinite proof source/structural Name provenance differs')
 require(q['resolution']=='genuine-exported-original-proof-value' and q['standaloneTargetIdentity'] is None and binding['standaloneTargetIdentity'] is None,'Infinite source proof must not acquire standalone target identity')
 require(q['collisionClassification']==binding['collisionClassification']=='present-type-incompatible-generated-proof','Infinite proof must be marked present with incompatible actual target type')
 for key in ['sourceOriginalEnvironmentKernelChecked','sourceAxiomInventoryMatchesAcceptedGraph','actualSourceAndTargetProofTypesKernelDistinct','originalTypeBinderInfoPreserved','inferredTypeBinderInfoPlacementPreserved','exactOriginalTypeKernelChecked','genuineOriginalValueInhabitsExactOriginalType','parentWholeValueEqualityRequired','parentKernelDefinitionalValueEqualityRequired','expandedDependenciesHaveAllowedOwners']:require(q[key] is True,'Genuine Infinite source proof check failed: '+key)
 require(q['parentOriginal']==binding['parentOriginal']==QPARENT and binding['parentWholeValueEqualityRequired'] and binding['parentKernelDefinitionalValueEqualityRequired'],'Infinite source proof parent policy differs')
 require(q['expandedType']==record['elaboratedExpr'] and q['expandedValue']==record['valueExpr'],'Complete genuine Infinite proof must be retained exactly; no native proof/data substitution')
 require(not q['hasSorryAx'] and set(q['expandedTypeAxioms'])<=STANDARD and set(q['expandedValueAxioms'])<=STANDARD and set(record['axioms'])==set(sources[QPROOF]['axioms']) and {name_text(n) for n in binding['expectedSourceAxioms']}==set(record['axioms']),'Genuine Infinite source axiom closure differs')
 parent=comparisons[QPARENT];require(not parent['proofDeclaration'] and parent['computationalValueEqualityChecked'] and parent['kernelValueEqual'] and not parent['kernelPropositionalValueEquality'],'Infinite source proof requires exact complete qOrder data kernel definitional equality')
 facts=config['platformHelperEvidence']['facts']['contents'];current=next(r for r in facts['helperFacts'] if r['name']==QTARGET)
 require(current==q['actualCurrentIncompatibleProofFact']==binding['actualCurrentIncompatibleProofFact'],'Exact incompatible current helper fact changed')
 require(expression_head(record['elaboratedExpr'])=='Infinite' and expression_head(current['elaboratedExpr'])=='Module.Finite','Only exact Infinite/current Module.Finite generated helper collision is reviewed')
 require(current['constantKind']=='theorem' and current['isProposition'] and not current['isInstance'] and current['valueExpr'] is not None and not current['hasSorryAx'],'Current target-only declaration must be an actual complete compiler proof')
 actual=owned[QTARGET];require(actual['constantKind']=='theorem' and actual['hasValue'] and not actual['isInstance'] and actual['elaboratedExpr']==current['elaboratedExpr'] and actual['binderInventory']==current['binderInventory'] and actual['nameExpr']==current['nameExpr'],'Actual compiler-only proof type/Name/value/kind differs')
 for key in ['axioms','typeAxioms','valueAxioms']:require(set(current[key])<=STANDARD and set(actual[key])==set(current[key]),'Current compiler-only proof axiom closure differs')
 expected_provenance={'target':QTARGET,'sourceParentOriginal':QPARENT,'qOrderSourceHelperOriginal':QPROOF,'targetIdentityForSourceProof':False,'ownerAxiomAuditRequired':True,'wholeParentValueEqualityRequired':True,'collisionClassification':'present-type-incompatible-generated-proof','generationKind':'current compiler-generated Module.Finite proof from unchanged qOrder source command','actualCompilerRecord':current}
 require(config['targetOnlyCompilerProvenance']==audit['targetOnlyCompilerProvenance']==[expected_provenance],'Only exact actual qOrder compiler-only proof provenance is accepted')
 bundle=next(r for r in wrappers['bundles'] if r['module']=='Iut.Cor312.ThetaData.AdmissiblePrime')
 commands=[cm for cm in bundle['commandMaps'] if QPARENT in cm['selectedCompilerDeclarations']]
 require(len(commands)==1 and commands[0]['originalCommandIndex']==21 and commands[0]['sha256']=='b00e2de211ff32ba04c0fbe9038d7804e7890f8767e96ffe8fd6de0dfe8b33df' and commands[0]['role']=='selected-declaration','Current compiler helper must arise from exact unchanged whole qOrder source command')
 require(current['module']=='Definitions.Def_AbcAdaptation_Reference_Iut_Cor312_ThetaData_AdmissiblePrime' and current['name']==QTARGET,'Current compiler-only proof owner/family differs')
 baseline=config['qOrderOriginalKernelDiagnostic'];diagnostic=read(baseline['path']);receipt=read(baseline['receiptPath'])
 require(sha(baseline['path'])==baseline['sha256']==QORDER_BASELINE_PINS['diagnostic'] and diagnostic==baseline['contents'],'Actual original qOrder diagnostic changed')
 require(sha(baseline['receiptPath'])==baseline['receiptSha256']==QORDER_BASELINE_PINS['receipt'] and receipt==baseline['receiptContents'],'Actual original qOrder diagnostic receipt changed')
 require(q['originalEnvironmentKernelDiagnosticJob']==baseline['job_id']==receipt['job_id']=='ci-014644-6cff0e0c' and receipt['status']=='succeeded' and receipt['result']['exit_code']==0,'Exact original environment diagnostic did not succeed')
 snapshot=receipt['result']['snapshot'];require(receipt['request']['exclusive'] is True and snapshot['workspace_mode']=='exclusive_worktree' and snapshot['snapshot_id'] is None and receipt['resources']['peak_rss_bytes'] is not None and receipt['resources']['peak_rss_bytes']<=16*1024**3,'Original kernel diagnostic resource/workspace acceptance differs')
 expected={QPARENT,QPROOF,'NumberField.HeightOneSpectrum.instNormedFieldValuedAdicCompletion'}
 require(diagnostic['schema']=='tate-theta-qorder-original-kernel-diagnostic-v1' and diagnostic['compilerVersion']=='4.35.0-rc3' and len(diagnostic['checks'])==len(diagnostic['facts'])==3 and {r['name'] for r in diagnostic['checks']}=={r['name'] for r in diagnostic['facts']}==expected and all(r['originalEnvironmentKernelCheckedTypeAndValue'] for r in diagnostic['checks']),'Three exact complete original kernel checks required')
 original_facts={r['name']:r for r in diagnostic['facts']}
 for n,source in [(QPARENT,parent['sourceRecord']),(QPROOF,record)]:
  for key in ['nameExpr','levelParams','elaboratedExpr','valueExpr','binderInventory','constantKind','isProposition','isInstance','axioms']:require(original_facts[n][key]==source[key],'Fresh original qOrder source evidence differs: '+n+'.'+key)
 query=(unit.parents[2]/receipt['request']['parameters']['source']).resolve()
 require(sha(query)==receipt['request']['worktree_manifest']['source_sha256']==QORDER_BASELINE_PINS['source'],'Original kernel diagnostic source changed')
 require(receipt['result']['actual_arguments']==['lean',receipt['request']['parameters']['source']],'Original kernel diagnostic actual source arguments differ')
 for path,expected_sha in receipt['request']['worktree_manifest']['input_hashes'].items():require(sha(path)==expected_sha,'Original kernel diagnostic input changed: '+path)
 for path in [baseline['path'],baseline['receiptPath'],str(query)]:require(manifest['input_hashes'].get(path)==sha(path),'Final main does not bind original qOrder kernel evidence: '+path)
 return q,expected_provenance,{'schema':'tate-theta-qorder-proof-identity-policy-v1','sourceProofOriginal':QPROOF,'sourceStandaloneTargetIdentity':None,'sourceProofClassification':'present-type-incompatible-generated-proof','actualCurrentCompilerOnlyTarget':QTARGET,'sourceOriginalKernelJob':'ci-014644-6cff0e0c','sourceSelectedCount':78,'namedSelectedCount':76,'genuineSourceProofValueCount':2,'actualOwnedCount':77,'actualCompilerOnlyProofCount':1,'nativeStandardProofCount':2,'historicalPresenceQueryUnchanged':True,'requiredWholeDataParent':QPARENT,'requiredWholeCommandSha256':commands[0]['sha256']}

def verify_standard_proof(config,audit,comparisons,inv):
 compatibility=config['standardProofCompatibility'];report=audit['standardProofCompatibility']
 require(compatibility['schema']=='tate-theta-exact-standard-proof-compatibility-v1' and report['schema']=='tate-theta-exact-standard-proof-resolution-v1','Unexpected exact standard proof schema')
 require(compatibility['original']==report['original']==STANDARD_PROOF and compatibility['standaloneTargetIdentity'] is None and report['standaloneTargetIdentity'] is None,'Standard proof must not acquire an alias target identity')
 require(report['resolution']=='kernel-checked-native-proof-at-exact-original-type' and audit['standardProofValueResolutionCount']==2,'Unexpected standard proof method/count')
 require(config['auditorStandardImports']==['Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients'],'Only exact reviewer standard import allowed')
 evidence=compatibility['evidence']
 for role,e in evidence.items():
  require(sha(e['path'])==e['sha256'],'Exact standard proof evidence changed: '+role)
  if 'contents' in e:require(read(e['path'])==e['contents'],'Exact standard proof evidence contents differ: '+role)
 source=evidence['sourceFacts']['contents'];platform=evidence['platformFacts']['contents'];source_receipt=evidence['sourceReceipt']['contents'];platform_receipt=evidence['platformReceipt']['contents']
 for receipt,job in [(source_receipt,'ci-014215-2414b895'),(platform_receipt,'ci-014243-25ac457f')]:require(receipt['job_id']==job and receipt['status']=='succeeded' and receipt['result']['exit_code']==0,'Required exact standard facts query did not succeed')
 require(source['relevantStandardNameCount']==platform['relevantStandardNameCount']==270 and source['selectedOriginalScopeCount']==78 and [name_text(n) for n in platform['missingRelevantStandardNames']]==[STANDARD_PROOF],'Different exact standard API presence scope')
 require(len(platform['originalCurrentStandardShapeChecks'])==7 and all(all(r[k] for k in ['succeeded','kernelTypeEqual','binderInfoPlacementEqual','computationShapeEqual','structureMetadataEqual']) for r in platform['originalCurrentStandardShapeChecks']),'Seven focused standard API checks incomplete')
 source_record=next(r for r in source['facts'] if r['name']==STANDARD_PROOF)
 require(report['sourceRecord']==source_record and source_record['constantKind']=='theorem' and source_record['isInstance'] and source_record['isProposition'] and source_record['valueExpr'] is not None,'Exact original standard proposition-valued theorem instance record differs')
 native=platform['nativeProofAttempt'];require(report['actualNativeProofAttempt']==native and report['originalSourceBodyAttempt']==platform['genuineSourceBodyAttempt'] and not platform['genuineSourceBodyAttempt']['succeeded'],'Genuine source failure/native actual proof evidence differs')
 native_params=compatibility['nativeLevelParams'];source_params=source_record['levelParams']
 require(native_params==[[[[],'str','_finiteQuotientsQueryUniverse'],'num',0]] and len(source_params)==1 and report['nativeLevelParams']==native_params and report['restoredSourceLevelParams']==source_params,'Actual numeric native universe restoration differs')
 for key in ['nativeUniversesRestoredToOriginal','kernelCheckedExactSourceType','originalTypeBinderInfoPreserved','inferredTypeBinderInfoPreserved','originalCurrentClassAPIChecked','dependencyOwnersStandardOnly','allConsumerWholeDataKernelDefinitionalEqualitiesRequired']:require(report[key] is True,'Exact standard proof kernel report check failed: '+key)
 require(report['expandedType']==source_record['elaboratedExpr'] and report['expandedValue']==substitute_level(native['value'],native_params[0],source_params[0]),'Expanded standard proof must be exact actual native value with only explicit universe restoration')
 require(not report['hasSorryAx'] and set(report['expandedTypeAxioms'])<=STANDARD and set(report['expandedValueAxioms'])<=STANDARD,'Expanded standard proof has nonstandard axioms')
 required=sorted(d['name'] for m in inv['modules'] for d in m['declarations'] if d['selected'] and d['kind']=='def' and STANDARD_PROOF in set(d['directTypeDeps'])|set(d['directValueDeps']))
 require(len(required)==9 and compatibility['requiredDataConsumers']==report['requiredDataConsumers']==required,'Exact nine direct selected data consumers differ')
 for n in required:
  row=comparisons[n];require(not row['proofDeclaration'] and row['computationalValueEqualityChecked'] and row['kernelValueEqual'] and not row['kernelPropositionalValueEquality'],'Standard proof consumer lacks strict whole-data kernel definitional equality: '+n)
 return report

def prepare(unit,receipt_path,audit_path,wrapper_path,expected_job=None):
 unit=unit.resolve();workspace=unit.parents[2]
 receipt=read(receipt_path);config=read(unit/'audit-config.json');wrappers=read(wrapper_path);inv=read(unit/'inventory.json')
 require({k for k in config if 'compatibility' in k.lower()}=={'standardProofCompatibility','adicSourceCompatibility'},'New data compatibility requires its concrete independent review and generator schema update')
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
 require(config['expectedRecordCount']==RECORDS and config['expectedSelectedCount']==SELECTED and config['expectedNamedSelectedCount']==NAMED_SELECTED and config['expectedProofValueResolutionCount']==2 and config['expectedModuleCount']==4,'Wrong configured 78=76+2 declaration dimensions')
 require(config['standardRenames']==[] and config['expectedTargetOnlyCompilerDeclarations']==[QTARGET],'Only the exact reviewed current Module.Finite compiler-only proof may lack a source identity')
 audit=read(audit_path)
 require(audit['schema']=='next-carrier-kernel-audit-v3' and audit['configuration']==config,'Actual audit schema/config differs')
 require(audit['compilerVersion']=='4.33.1' and audit['originalCompilerVersion']=='4.35.0-rc3','Unexpected compiler versions')
 require(not audit['hasSorryAx'] and audit['allOwnedTypeValueClosuresStandardAxiomsOnly'],'Owned axiom closure failed')
 expected={'requiredSourceDeclarationCount':SELECTED,'requiredResolvedCount':SELECTED,'requiredEliminatedInternalProofCount':2,'requiredNamedComparedCount':NAMED_SELECTED,'requiredProofValueResolutionCount':2,'requiredComparedCount':SELECTED}
 for k,v in expected.items():require(audit[k]==v,'Actual audit dimension differs: '+k)
 sources={d['name']:dict(d,sourceModule=m['module'],sourceSha256=m['sourceSha256']) for m in inv['modules'] for d in m['declarations']}
 require(len(sources)==RECORDS,'Not 117 source originals');selected={n for n,r in sources.items() if r['selected']};require(len(selected)==SELECTED,'Not 78 selected originals')
 comparisons=unique(audit['comparisons'],'original','actual compared original');targets=unique(audit['comparisons'],'target','actual compared target')
 resolutions=unique(audit['proofValueResolutions'],'original','genuine original proof value')
 configured=unique(config['proofValueResolutions'],'original','configured original proof value')
 require(set(resolutions)==set(configured)==PROJECT_PROOFS and not PROJECT_PROOFS&set(comparisons),'Only the exact absent equation proof and type-incompatible Infinite proof may lack source target identities')
 require(set(comparisons)<=set(sources) and {n for n in comparisons if sources[n]['selected']}==selected-PROJECT_PROOFS,'Selected actual 76 named plus 2 proof-value partition differs')
 owned=unique(audit['ownedDeclarations'],'name','owned actual target')
 require(audit['targetOnlyCompilerDeclarations']==[QTARGET] and set(owned)==set(targets)|{QTARGET} and len(owned)==77,'Actual target ownership partition differs')
 for n,r in owned.items():
  require(not r['hasSorryAx'],'Owned sorryAx: '+n)
  for k in ['axioms','typeAxioms','valueAxioms']:require(set(r[k])<=STANDARD,'Unexpected owned axiom: '+n)
 missing=set(sources)-set(comparisons)-set(resolutions)
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
  signature_checks=verify_signature_scope(r)
  require(r['expectedIsInstance']==s['isInstance'],'Actual instance status differs: '+n)
  if not r['proofDeclaration'] and s['valueExpr'] is not None:require(r['computationalValueEqualityChecked'] and r['kernelValueEqual'] and not r['kernelPropositionalValueEquality'],'Whole computational value not compared: '+n)
  require(len(s['recursorRuleRhs'])==r['recursorRulesCompared'],'Recursor rules not fully compared: '+n)
  named.append({'original':n,'originalName':r['originalName'],'target':r['target'],'targetName':r['targetName'],'targetToSourceUniverseIndices':r['targetToSourceUniverseIndices'],'expectedIsInstance':r['expectedIsInstance'],'expectedSourceAxioms':[axiom_name(ax) for ax in s['axioms']],'sourceAxiomNames':s['axioms'],'sourceOwner':s['module'],'acceptedJob':receipt['job_id'],'sourceSelected':s['selected'],'comparisonScope':'mandatory-selected' if s['selected'] else 'actual-unselected-compiler-declaration','signatureBinderChecks':signature_checks})
 proof=resolutions[PROOF];binding=configured[PROOF];s=proof['sourceRecord']
 require(binding['parentWholeValueEqualityRequired'] and binding['parentKernelDefinitionalValueEqualityRequired'],'Configuration must require strict full parent definitional value equality')
 require(s==binding['sourceRecord'] and s['name']==PROOF and s['selected'] and s['constantKind']=='theorem' and s['isProposition'] and not s['isInstance'] and s['valueExpr'] is not None,'Exact genuine selected source theorem/value record differs')
 require(s['module']=='TateCurvesTheta.TateCurve.JInvariant' and s['sourceSha256']==sources[PROOF]['sourceSha256'] and name_text(s['nameExpr'])==PROOF and proof['originalName']==s['nameExpr'],'Genuine source proof provenance/actual Name differs')
 require(binding['standaloneTargetIdentity'] is None and proof['standaloneTargetIdentity'] is None and proof['resolution']=='genuine-exported-original-proof-value','Genuine proof must have no standalone target identity')
 require(binding['parentOriginal']==proof['parentOriginal']==PARENT and proof['parentTarget']==comparisons[PARENT]['targetName'],'Genuine proof parent differs from actual named data parent')
 for k in ['originalTypeBinderInfoPreserved','inferredTypeBinderInfoPlacementPreserved','exactOriginalTypeKernelChecked','genuineOriginalValueInhabitsExactOriginalType','sourceAxiomInventoryMatchesAcceptedGraph','parentWholeValueEqualityRequired','parentKernelDefinitionalValueEqualityRequired','actualPlatformAbsenceEvidenceVerified','expandedDependenciesHaveAllowedOwners']:
  require(proof[k] is True,'Genuine tateJ.eq_1 proof check failed: '+k)
 require(not proof['hasSorryAx'] and set(proof['expandedTypeAxioms'])<=STANDARD and set(proof['expandedValueAxioms'])<=STANDARD and set(s['axioms'])==set(sources[PROOF]['axioms']),'Genuine proof axiom closure differs')
 require(proof['expandedType'] is not None and proof['expandedValue'] is not None,'Actual checked genuine proof expressions absent')
 parent=comparisons[PARENT]
 require(not parent['proofDeclaration'] and parent['sourceRecord']['constantKind']=='definition' and parent['sourceRecord']['valueExpr'] is not None and parent['computationalValueEqualityChecked'] and parent['kernelValueEqual'] and not parent['kernelPropositionalValueEquality'],'Full parent tateJ data value must be kernel definitionally equal; fallback is forbidden')
 require(audit['actualPlatformHelperEvidenceVerified'] and audit['actualPlatformHelperQueryJob']==proof['actualPlatformQueryJob']=='ci-014164-c01e488c','Exact actual platform absence query not verified')
 platform=config['platformHelperEvidence']
 for key in ['facts','receipt','querySource','queryConfiguration']:
  e=platform[key];require(sha(e['path'])==e['sha256'],'Actual platform helper evidence changed: '+key)
  if 'contents' in e:require(read(e['path'])==e['contents'],'Actual platform helper contents changed: '+key)
 facts=platform['facts']['contents'];query=platform['receipt']['contents']
 require(query['job_id']=='ci-014164-c01e488c' and query['status']=='succeeded' and query['result']['exit_code']==0,'Actual platform helper query failed')
 require(facts['ownedDeclarationCount']==77 and len(facts['ownedDeclarations'])==77 and facts['targetOnlyNames']==[] and facts['selectedMissingCount']==1,'Exact actual target inventory differs')
 require({r['original'] for r in facts['expectedCurrentCandidates'] if r['selected'] and not r['present']}=={PROOF},'Different selected source declaration absent')
 require({r['name'] for r in facts['ownedDeclarations']}==set(owned),'Final actual owned targets differ from helper query')
 require(binding['actualParentFact']==next(r for r in facts['helperFacts'] if r['name']==parent['target']),'Exact actual target parent type/value evidence differs')
 require(query['request']['worktree_manifest']['input_hashes'][str(unit/'audit-config.json')]==platform['queryConfiguration']['sha256'],'Historical helper query configuration hash differs')
 require(proof['collisionClassification']=='absent-generated-proof','Exact tateJ equation proof must retain absent-generated-proof classification')
 qproof,target_only_provenance,qproof_policy=verify_qorder_proof(config,audit,comparisons,resolutions,configured,owned,wrappers,unit,manifest,sources)
 standard_proof=verify_standard_proof(config,audit,comparisons,inv)
 adic_compatibility,adic_evidence=verify_adic_compatibility(config,audit,comparisons,unit,manifest)
 require(wrappers['definitionsBundleCount']==len(wrappers['bundles'])==4 and wrappers['selectedConstantCount']==SELECTED,'Wrapper dimensions differ')
 for w in wrappers['bundles']:
  require(sha(w['path'])==w['sha256'],'Audited wrapper changed: '+w['module'])
  require((workspace/'Definitions'/Path(w['path']).name).read_bytes()==Path(w['path']).read_bytes(),'Installed wrapper differs: '+w['module'])
 resources=receipt.get('resources') or {};require(resources.get('peak_rss_bytes') is not None and resources['peak_rss_bytes']<=16*1024**3,'Final main audit exceeds physical16GiB RSS bound');cpu,user,system=[resources.get(k) for k in ['cpu_time_seconds','cpu_user_seconds','cpu_system_seconds']]
 if cpu is not None and user is not None and system is not None:require(math.isclose(cpu,user+system,abs_tol=0.1),'CPU total differs from user plus system')
 selected_pairs=[r for r in named if r['sourceSelected']];unselected_pairs=[r for r in named if not r['sourceSelected']]
 return {'schema':'reference-tate-theta-accepted-compiler-correspondence-v1','status':'accepted-kernel-audit','job_id':receipt['job_id'],
  'receipt':str(receipt_path.resolve()),'receiptSha256':sha(receipt_path),'audit':str(audit_path.resolve()),'auditSha256':sha(audit_path),
  'sourceSelectedCount':SELECTED,'actualNamedComparisons':len(named),'selectedNamedComparisons':len(selected_pairs),'unselectedNamedComparisons':len(unselected_pairs),'internalProofValueResolutions':2,'sourceObligationsResolved':len(selected_pairs)+2,
  'namedPairs':named,'selectedNamedPairs':selected_pairs,'unselectedNamedPairs':unselected_pairs,'proofValueResolutions':[proof,qproof],
  'missingUnselectedOriginalDeclarations':audit['missingUnselectedOriginalDeclarations'],'targetOnlyCompilerDeclarations':[QTARGET],'targetOnlyCompilerProvenance':[target_only_provenance],'qOrderProofIdentityPolicy':qproof_policy,
  'proofIdentityPolicy':'The exact original tateJ.eq_1 theorem is absent; the original qOrder._proof_1 Infinite theorem has a present but type-incompatible Module.Finite compiler helper. Both genuine source proof values retain exact source types and no standalone target identity. Both named data parents retain complete kernel definitional value equality. The actual current Module.Finite helper is separately reported as compiler-only provenance and creates no source proof identity.',
  'standardProofCompatibility':standard_proof,'standardProofValueResolutionCount':2,'adicSourceCompatibility':adic_compatibility,'adicSourceCompatibilityEvidence':adic_evidence,'binderInfoComparisonScope':BINDER_SCOPE,
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
