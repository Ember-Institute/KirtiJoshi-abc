#!/usr/bin/env python3
"""Bind the exact original Infinite/current ModuleFinite helper collision. No compilation."""
import argparse,hashlib,json
from pathlib import Path
HERE=Path(__file__).resolve().parent
W=Path('/home/admin-wsl/Coq/abc/prove2me_workspace')
ORIGINAL='Iut.AdmissiblePrimeData.qOrder._proof_1';TARGET='AbcAdaptation.Reference.'+ORIGINAL

def load(p):return json.loads(Path(p).read_text())
def sha(p):
 h=hashlib.sha256()
 with Path(p).open('rb') as f:
  for b in iter(lambda:f.read(1024*1024),b''):h.update(b)
 return h.hexdigest()
def dump(p,v):Path(p).write_text(json.dumps(v,ensure_ascii=False,separators=(',',':'))+'\n')
p=argparse.ArgumentParser(description=__doc__);p.add_argument('--base-config',required=True,type=Path);p.add_argument('--original-diagnostic',required=True,type=Path);p.add_argument('--original-receipt',required=True,type=Path);p.add_argument('--original-source-record',required=True,type=Path);p.add_argument('--platform-facts',required=True,type=Path);p.add_argument('--audit-output',required=True,type=Path);p.add_argument('--output',type=Path,default=HERE/'audit-config.json');a=p.parse_args();assert a.output.resolve().parent==HERE
config=load(a.base_config);assert config['expectedSelectedCount']==78 and config['expectedNamedSelectedCount']==77 and config['expectedProofValueResolutionCount']==1
original=load(a.original_source_record);assert original['name']==ORIGINAL and original['selected'] and original['constantKind']=='theorem' and original['isProposition'] and not original['isInstance']
diagnostic=load(a.original_diagnostic);receipt=load(a.original_receipt)
assert receipt['status']=='succeeded' and receipt['result']['exit_code']==0
assert receipt['request']['exclusive'] and receipt['result']['snapshot']['workspace_mode']=='exclusive_worktree' and receipt['result']['snapshot']['snapshot_id'] is None
assert receipt['resources']['peak_rss_bytes'] is not None and receipt['resources']['peak_rss_bytes']<=17179869184
assert diagnostic['schema']=='tate-theta-qorder-original-kernel-diagnostic-v1' and diagnostic['compilerVersion']=='4.35.0-rc3'
checks=diagnostic['checks'];assert len(checks)==3 and all(r['originalEnvironmentKernelCheckedTypeAndValue'] for r in checks)
assert {r['name'] for r in checks}=={'Iut.AdmissiblePrimeData.qOrder',ORIGINAL,'NumberField.HeightOneSpectrum.instNormedFieldValuedAdicCompletion'}
old=next(r for r in diagnostic['facts'] if r['name']==ORIGINAL)
for key in ['elaboratedExpr','valueExpr','levelParams','binderInventory','constantKind','isProposition','isInstance','axioms']:assert old[key]==original[key]
query=W/receipt['request']['parameters']['source'];assert sha(query)==receipt['request']['worktree_manifest']['source_sha256']
facts=load(a.platform_facts);assert facts==config['platformHelperEvidence']['facts']['contents'];current=next(r for r in facts['helperFacts'] if r['name']==TARGET)
assert current['constantKind']=='theorem' and current['isProposition'] and not current['hasSorryAx']
removed=[r for r in config['projectMap'] if r['original']==ORIGINAL];assert len(removed)==1
config['projectMap']=[r for r in config['projectMap'] if r['original']!=ORIGINAL]
config['proofValueResolutions'].append({'original':ORIGINAL,'originalName':original['nameExpr'],'sourceRecord':original,'standaloneTargetIdentity':None,'parentOriginal':'Iut.AdmissiblePrimeData.qOrder','expectedSourceAxioms':removed[0]['expectedSourceAxioms'],'actualCurrentIncompatibleProofFact':current,'collisionClassification':'present-type-incompatible-generated-proof','parentWholeValueEqualityRequired':True,'parentKernelDefinitionalValueEqualityRequired':True})
config['expectedNamedSelectedCount']=76;config['expectedProofValueResolutionCount']=2;config['expectedTargetOnlyCompilerDeclarations']=[TARGET]
config['qOrderOriginalKernelDiagnostic']={'path':str(a.original_diagnostic.resolve()),'sha256':sha(a.original_diagnostic),'contents':diagnostic,'receiptPath':str(a.original_receipt.resolve()),'receiptSha256':sha(a.original_receipt),'receiptContents':receipt,'job_id':receipt['job_id']}
config['targetOnlyCompilerProvenance']=[{'target':TARGET,'sourceParentOriginal':'Iut.AdmissiblePrimeData.qOrder','qOrderSourceHelperOriginal':ORIGINAL,'targetIdentityForSourceProof':False,'ownerAxiomAuditRequired':True,'wholeParentValueEqualityRequired':True,'collisionClassification':'present-type-incompatible-generated-proof','generationKind':'current compiler-generated Module.Finite proof from unchanged qOrder source command','actualCompilerRecord':current}]
config['outputDir']=str(a.audit_output.resolve())
evidence={r['path']:r for r in config['inputEvidence']}
for path in [a.base_config,a.original_diagnostic,a.original_receipt,a.original_source_record,a.platform_facts,query]:evidence[str(path.resolve())]={'path':str(path.resolve()),'sha256':sha(path)}
config['inputEvidence']=list(evidence.values());assert len(config['projectMap'])==151 and len(config['proofValueResolutions'])==2
dump(a.output,config)
t=(HERE/'AuditNextCarriers.template.lean').read_text();header='import Lean\n'+''.join('import '+m+'\n' for m in config['auditorStandardImports'])
def display(n):return '' if not n else (display(n[0])+'.' if n[0] else '')+str(n[2])
header+=''.join('import '+display(m)+'\n' for m in config['allowedDependencyModules']);header+=''.join('import '+r['target']+'\n' for r in config['modules'])
marker=']).pretty ++ "\\n")'
if marker in t:assert t.count(marker)==1;t=t.replace(marker,']).compress ++ "\\n")')
(HERE/'AuditNextCarriers.lean').write_text(header+'\n'+t[t.index('/-! Stable JSON'):])
print(json.dumps({'selectedSource':78,'requiredNamed':76,'genuineSourceProofValues':2,'targetOwned':77,'targetOnlyModuleFiniteProof':1,'standardNativeProofs':2,'sourceDataDagEntries':35,'compiled':False}))
