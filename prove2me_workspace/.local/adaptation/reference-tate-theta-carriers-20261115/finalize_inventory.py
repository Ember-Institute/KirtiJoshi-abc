#!/usr/bin/env python3
"""Freeze exact source bytes and pin read-only provenance. Writes only TASK."""
import copy,hashlib,json,subprocess
from collections import Counter
from pathlib import Path
TASK=Path('/tmp/p2m-tate-theta-inventory-v5-20261115');BASE=Path('/home/admin-wsl/Coq/abc');W=BASE/'prove2me_workspace';B=W/'.local/adaptation/reference-tate-theta-carriers-20261115';A=W/'.local/adaptation'
def load(p):return json.loads(Path(p).read_text())
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def write(n,d):(TASK/n).write_text(json.dumps(d,ensure_ascii=False,indent=2)+'\n')
def git(repo,*args):return subprocess.run(['git','-C',str(repo),*args],capture_output=True,check=True).stdout
inv=load(TASK/'inventory.json');configs={n:load(TASK/n) for n in ['unit-config.json','parser-config.json','export-config.json']};provenance=[];source_bytes=[]
for m in inv['modules']:
 p=m['provenance'];module=m['module'];source=Path(m['source']);rel=p['originalSourcePath'];upstream=git(p['actualGitRepository'],'show',p['originalCommit']+':'+rel)
 assert upstream==source.read_bytes() and not p['sourceOverridden']
 snapshot=Path('frozen-sources')/rel;dest=TASK/snapshot;dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(upstream)
 p['frozenEffectiveSource']={'path':str(B/snapshot),'sha256':sha(dest),'byteLength':dest.stat().st_size};p['sourceHeader']=upstream[:upstream.index(b'import ')].decode()
 p['acceptedGraphSourceReceipt']={'path':str(A/'reference-extraction-20261115/c22-graph-source-receipt.json'),'sha256':sha(A/'reference-extraction-20261115/c22-graph-source-receipt.json')}
 provenance.append({'module':module,'repository':p['actualGitRepository'],'actualHead':git(p['actualGitRepository'],'rev-parse','HEAD').decode().strip(),'actualOrigin':git(p['actualGitRepository'],'remote','get-url','origin').decode().strip(),'sourceCommit':p['originalCommit'],'sourceRelativePath':rel,'gitBlobObject':p['sourceGitObject'],'workingSourceEqualsExactCommitBlob':True,'workingSourceEqualsAcceptedEffectiveSource':True,'sha256':sha(source),'provenance':copy.deepcopy(p)})
 source_bytes.append({'module':module,'effectiveSource':p['frozenEffectiveSource'],'upstreamSource':p['frozenEffectiveSource'],'sourceHeaderSha256':p['sourceHeaderSha256'],'originalNoticeRetained':True,'sourceGitBlobMatches':True})
 for c in configs.values():next(x for x in c['sources'] if x['module']==module)['provenance']=copy.deepcopy(p)
write('inventory.json',inv)
for name,c in configs.items():
 if name=='export-config.json':c['inventorySha256']=sha(TASK/'inventory.json');c['nameResolutionPolicy']='Resolve unique actual compiler Name by exact graph display string; serialize actual str/num components. nameExpr=null denotes a source candidate pending compiler export, never an asserted Name.'
 write(name,c)
query=Path('/tmp/p2m-after-volume-tate-next-20261115/QueryAfterVolumeTateParserRanges.draft.lean').read_text().replace('Draft for main-agent MCP-CI validation only.','Uncompiled candidate for main-agent MCP-CI validation only.')
(TASK/'QueryNextCarrierParserRanges.lean').write_text(query)
parser=load(TASK/'parser-config.json');parser['nameResolutionPolicy']={'policy':'Resolve each exact graph display string against actual imported environment Names; require one match; retain actual numeric Name components in nameExpr. Do not reconstruct private Names from dotted text.','privateOriginalDeclarations':[r['name'] for m in inv['modules'] for r in m['declarations'] if r['isPrivate']],'query':'QueryNextCarrierParserRanges.lean','querySha256':sha(TASK/'QueryNextCarrierParserRanges.lean'),'queryStatus':'uncompiled-candidate-no-new-receipt'};write('parser-config.json',parser)
write('source-provenance-audit.json',{'schema':'next-carrier-source-provenance-audit-v1','records':provenance,'sourceLicenseLimit':'Tate repository tree has no standalone LICENSE/COPYING/NOTICE. Exact Tate source copyright/authors/Apache-2.0 notice is retained. Distributed Apache text is copied from the pinned iut license; it is not claimed as a Tate repository file.','readonlyGitCommandsOnly':True})
license_source=BASE/'refer/iut/LICENSE';(TASK/'LICENSE.Apache-2.0').write_bytes(license_source.read_bytes())
write('source-bytes-manifest.json',{'schema':'tate-theta-effective-upstream-source-bytes-v1','files':source_bytes,'distributedApacheText':{'source':str(license_source),'path':str(B/'LICENSE.Apache-2.0'),'sha256':sha(license_source)},'sourceOverrides':[]})
closure=load(TASK/'dependency-closure.json');closure['requiredPriorAvailableNamedCount']=len(closure['requiredPriorActualPairs']);closure['importedBundles']=[x for x in closure['importedBundles'] if x['neededConstants']]
closure['sourceVersionPins']=[{'module':m['module'],'effectiveSource':m['source'],'effectiveSourceSha256':m['sourceSha256'],'upstreamSourceSha256':m['provenance']['upstreamSourceSha256'],'sourceGitObject':m['provenance']['sourceGitObject'],'sourceOverridden':False} for m in inv['modules']]
foundation_path=A/'foundation-reference-carriers-20261115/kernel-audit/foundation-kernel-audit.json';foundation=load(foundation_path);named=[];proofs=[];evidence=[{'path':str(foundation_path),'sha256':sha(foundation_path),'role':'accepted-foundation-kernel-audit','namedCount':110}]
for r in foundation['comparisons']:
 if r['kernelTypeEqual']:
  named.append({'original':r['original'],'originalName':r['sourceRecord']['nameExpr'],'target':r['target'],'targetName':None,'targetNameStatus':'Actual accepted kernel display name; components absent from this audit schema. No reconstruction asserted.','sourceOwner':r['sourceRecord']['module'],'targetToSourceUniverseIndices':r['targetToSourceUniverseIndices'],'expectedIsInstance':r['expectedIsInstance'],'supplierUnit':'foundation','evidencePath':str(foundation_path),'evidenceSha256':sha(foundation_path)})
for folder,label,count in [('reference-packet-field-carriers-20261115','packet-field',131),('reference-volume-tate-carriers-20261115','volume-tate',98)]:
 p=A/folder/'accepted-compiler-correspondence.json';d=load(p);assert d['status']=='accepted-kernel-audit' and len(d['namedPairs'])==count
 for k,h in [('receipt','receiptSha256'),('audit','auditSha256')]:assert sha(d[k])==d[h]
 evidence.append({'path':str(p),'sha256':sha(p),'job_id':d['job_id'],'receipt':d['receipt'],'receiptSha256':d['receiptSha256'],'audit':d['audit'],'auditSha256':d['auditSha256'],'namedCount':count})
 named.extend(dict(r,supplierUnit=label,evidencePath=str(p),evidenceSha256=sha(p)) for r in d['namedPairs'])
 proofs.extend(dict(r,supplierUnit=label,evidencePath=str(p),evidenceSha256=sha(p)) for r in d['proofValueResolutions'])
assert len(named)==len({r['original'] for r in named})==339
required=set(closure['requiredPriorConstants']);assert required<={r['original'] for r in named};assert not required&{r['original'] for r in proofs}
write('accepted-prior-identity-map.json',{'schema':'tate-theta-accepted-prior-identity-map-v1','status':'prior-accepted-evidence-only-current-unit-uncompiled','namedPairs':named,'proofValueResolutions':proofs,'namedCount':339,'proofValueResolutionCount':len(proofs),'evidence':evidence,'policy':'Only namedPairs have standalone actual target identities. Genuine proof-value resolutions are separate and must never be promoted to named identities. No current-unit candidate is accepted.'})
closure['requiredPriorActualPairs']=[r for r in named if r['original'] in required];closure['priorEvidence']=evidence;closure['acceptedPriorIdentityMap']={'path':str(B/'accepted-prior-identity-map.json'),'sha256':sha(TASK/'accepted-prior-identity-map.json')};write('dependency-closure.json',closure)
imports=load(TASK/'imports.json')
for m in imports:m['platform433Candidates']=list(dict.fromkeys(m['platform433Candidates']))
write('imports.json',imports)
plan=load(TASK/'machine-plan.json');plan.update(availableAcceptedNamedCount=339,requiredPriorActualNamedCount=42,requiredPriorSupplierUnitCounts=dict(Counter(r['supplierUnit'] for r in closure['requiredPriorActualPairs'])),requiredPriorProofValueResolutions=[],sourceOverrides=[],additionalPriorModulesNeeded=[],candidateImportStatus='All translated target source paths exist; compiler compatibility and exact syntax imports await main CI',allOriginalNameResolutionRequired=True,sourceCandidateAcceptance='none-current-unit');write('machine-plan.json',plan)
print(json.dumps({'status':'draft-ready-no-compiler','all':117,'selected':78,'roots':20,'requiredPrior':42,'priorAvailable':339,'suppliers':plan['requiredPriorSupplierUnitCounts'],'importedBundles':len(closure['importedBundles'])}))
