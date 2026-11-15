#!/usr/bin/env python3
"""Review the precise actual-evidence-backed equation proof patch without compiling."""
import ast,difflib,hashlib,json
from pathlib import Path
HERE=Path(__file__).resolve().parent
B=Path('/home/admin-wsl/Coq/abc/prove2me_workspace/.local/adaptation/reference-tate-theta-carriers-20261115')
OLD=B/'attempts/kernel-audit-v2'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def dump(p,x):p.write_text(json.dumps(x,ensure_ascii=False,indent=2)+'\n')
def block(s,a,z):return s[s.index(a):s.index(z,s.index(a))]
for p in HERE.glob('*.py'):ast.parse(p.read_text())
old=(OLD/'AuditNextCarriers.template.lean').read_text();new=(HERE/'AuditNextCarriers.template.lean').read_text()
assert block(old,'def compareRecord','def audit :')==block(new,'def compareRecord','def audit :')
assert block(old,'def auditDeclaration','-- Paths distinguish')==block(new,'def auditDeclaration','-- Paths distinguish')
assert block(old,'partial def binderPlacement','def canonicalLevels')==block(new,'partial def binderPlacement','def canonicalLevels')
assert all(t not in new for t in ['installDecidable','proveGeneratedEliminatorEquality','standardExpansions'])
assert 'kernelTermEq s!"original versus target computational value' in new
assert 'parentKernelDefinitionalValueEqualityRequired' in new
assert 'unless requiredNamedCount == 77' in new and 'proofResolutionReports.size == 1' in new
assert 'let excludedSourceNames ← excludedRows.mapM fun row => do' in new
assert 'let ownedNames ← ownedRows.mapM fun row => do' in new
config=json.loads((HERE/'audit-config.json').read_text());facts=json.loads((B/'platform-helper-facts.json').read_text())
assert config['expectedRecordCount']==117 and config['expectedSelectedCount']==78
assert config['expectedNamedSelectedCount']==77 and config['expectedProofValueResolutionCount']==1
assert config['expectedTargetOnlyCompilerDeclarations']==[] and len(config['projectMap'])==152
assert len(config['excludedOriginalDeclarations'])==6
proofs=config['proofValueResolutions'];assert len(proofs)==1
proof=proofs[0];name='TateCurvesTheta.TateParameter.tateJ.eq_1'
assert proof['original']==name and proof['sourceRecord']['name']==name
assert proof['standaloneTargetIdentity'] is None and proof['sourceRecord']['isProposition']
assert proof['sourceRecord']['selected'] and proof['sourceRecord']['constantKind']=='theorem'
assert not any(r['original']==name for r in config['projectMap'])
assert proof['parentOriginal']=='TateCurvesTheta.TateParameter.tateJ'
assert proof['parentWholeValueEqualityRequired'] and proof['parentKernelDefinitionalValueEqualityRequired']
assert sum(r['required'] for r in config['projectMap'])==77
assert facts['ownedDeclarationCount']==77 and facts['selectedMissingCount']==1
assert config['platformHelperEvidence']['facts']['contents']==facts
assert sha(HERE/'query-config.actual.json')==sha(OLD/'audit-config.json')
for key in ['facts','receipt']:
 e=config['platformHelperEvidence'][key];assert sha(Path(e['path']))==e['sha256']
for f in ['AuditNextCarriers.template.lean','prepare_audit_config.py']:
 a=(OLD/f).read_text();c=(HERE/f).read_text();(HERE/(f+'.diff')).write_text(''.join(difflib.unified_diff(a.splitlines(True),c.splitlines(True),fromfile='actual-archived-v2/'+f,tofile='exact-source-equation-v3/'+f)))
dump(HERE/'static-validation.json',{
 'schema':'tate-theta-exact-equation-source-proof-static-validation-v3','status':'static-only-not-compiled',
 'actualPlatformQueryJob':'ci-014164-c01e488c','actualTargetOwnedDeclarations':77,
 'sourceRecords':117,'selectedSourceObligations':78,'requiredNamedComparisons':77,
 'genuineSourceProofValueResolutions':1,'genuineSourceProofName':name,
 'standaloneTargetIdentity':None,'requiredPriorAcceptedNamedIdentities':42,'projectMapRows':152,
 'privateUnselectedActualRecords':6,'publicCompareRecordByteUnchanged':True,
 'ownedAxiomAuditByteUnchanged':True,'binderPlacementAuditByteUnchanged':True,
 'actualFactsReceiptAndArchivedQueryConfigurationVerified':True,
 'parentFullDataKernelDefinitionalEqualityMandatory':True,
 'noOldRepresentationOrExtensionalEqualityExceptions':True,'offlineFullGeneratorValidationPassed':True,
 'generatedAuditSourceIsUncompiled':True,'compiled':False,'ciSubmitted':False,'mainWorkspaceEdited':False})
dump(HERE/'provenance.json',{
 'schema':'tate-theta-exact-equation-source-proof-provenance-v3',
 'baseFailedAuditJob':'ci-014154-8d1865cd','actualPlatformQueryJob':'ci-014164-c01e488c',
 'inputs':[{'path':str(p),'sha256':sha(p)} for p in [OLD/'AuditNextCarriers.template.lean',OLD/'prepare_audit_config.py',OLD/'audit-config.json',B/'platform-helper-facts.json',B/'platform-helper-facts-result.json']],
 'drafts':[{'path':str(HERE/f),'sha256':sha(HERE/f)} for f in ['AuditNextCarriers.template.lean','prepare_audit_config.py','AuditNextCarriers.lean','audit-config.json']],
 'policy':'Only actual absent tateJ.eq_1 is resolved by its genuine exported source proof value. No target identity is created. Parent tateJ full data value must remain kernel definitionally equal.'})
print(json.dumps({'status':'static-only-not-compiled','source':117,'selected':78,'named':77,'genuineSourceProofValues':1,'projectMap':152,'publicChecksByteUnchanged':True}))
