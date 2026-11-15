#!/usr/bin/env python3
"""Pin effective/upstream provenance and precise import candidates. Writes only TASK."""
import copy,difflib,hashlib,json,subprocess
from pathlib import Path
TASK=Path('/tmp/p2m-volume-tate-inventory-v4-20261115')
BASE=Path('/home/admin-wsl/Coq/abc');W=BASE/'prove2me_workspace'
B=W/'.local/adaptation/reference-volume-tate-carriers-20261115'
REF=W/'.local/adaptation/reference-extraction-20261115'
def load(p):return json.loads(Path(p).read_text())
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def write(n,d):(TASK/n).write_text(json.dumps(d,ensure_ascii=False,indent=2)+'\n')
def git(repo,*args):return subprocess.run(['git','-C',str(repo),*args],capture_output=True,check=True).stdout
inv=load(TASK/'inventory.json');unit=load(TASK/'unit-config.json');parser=load(TASK/'parser-config.json');export=load(TASK/'export-config.json')
provenance=[];source_bytes=[]
for m in inv['modules']:
 p=m['provenance'];module=m['module'];source=Path(m['source']);rel=p['originalSourcePath'];repo=Path(p['actualGitRepository']);upstream=git(repo,'show',p['originalCommit']+':'+rel)
 snapshot=Path('frozen-sources')/rel;dest=TASK/snapshot;dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(source.read_bytes())
 p['frozenEffectiveSource']={'path':str(B/snapshot),'sha256':sha(dest),'byteLength':dest.stat().st_size}
 if p['sourceOverridden']:
  patch_rel=Path('source-overrides/LogVolume.patch');patch=TASK/patch_rel;patch.parent.mkdir(parents=True,exist_ok=True)
  patch.write_text(''.join(difflib.unified_diff(Path(p['originalSource']).read_text().splitlines(keepends=True),source.read_text().splitlines(keepends=True),fromfile=rel,tofile=rel+' (accepted effective source)')))
  upstream_rel=Path('upstream-sources')/rel;upstream_dest=TASK/upstream_rel;upstream_dest.parent.mkdir(parents=True,exist_ok=True);upstream_dest.write_bytes(upstream)
  p['frozenUpstreamSource']={'path':str(B/upstream_rel),'sha256':sha(upstream_dest),'byteLength':len(upstream)}
  acceptance=REF/'c22-graph-result.json';receipt=load(acceptance);assert receipt['status']=='succeeded' and receipt['job_id']=='ci-012771-ee109b3e'
  p['effectiveSourceOverride']={'upstreamSource':p['originalSource'],'upstreamSourceSha256':p['upstreamSourceSha256'],'upstreamGitObject':p['sourceGitObject'],'effectiveSourceSha256':m['sourceSha256'],'patch':{'path':str(B/patch_rel),'sha256':sha(patch)},'acceptance':{'path':str(acceptance),'sha256':sha(acceptance),'job_id':receipt['job_id']},'acceptedGraphSourceReceipt':{'path':str(REF/'c22-graph-source-receipt.json'),'sha256':sha(REF/'c22-graph-source-receipt.json')},'effectiveSourceLeafAcceptance':{'path':str(REF/'Iut-Cor312-LogVolume-leaf-result.json'),'sha256':sha(REF/'Iut-Cor312-LogVolume-leaf-result.json'),'job_id':'ci-012606-3dbf7af3'},'sourceBuildPlan':{'path':str(REF/'source-build-plan.json'),'sha256':sha(REF/'source-build-plan.json')},'effectiveSourceRepairExplanation':{'path':str(REF/'log-volume-instance-repair.json'),'sha256':sha(REF/'log-volume-instance-repair.json')},'changeScope':'Existing accepted 4.35 source: source lake option mirror (relaxedAutoImplicit=false,maxSynthPendingDepth=3) and elaboration repair (dependent CommRing letI, typed cast/lambda). Complete public structure and fields preserved.'}
 if p['sourceOverridden']:
  p['evidence'] += [p['effectiveSourceOverride'][k] for k in ['patch','acceptance','acceptedGraphSourceReceipt','sourceBuildPlan','effectiveSourceRepairExplanation']]
 assert p['sourceGitBlobMatches']==(upstream==source.read_bytes())
 provenance.append({'module':module,'repository':str(repo),'actualHead':git(repo,'rev-parse','HEAD').decode().strip(),'actualOrigin':git(repo,'remote','get-url','origin').decode().strip(),'sourceCommit':p['originalCommit'],'sourceRelativePath':rel,'gitBlobObject':p['sourceGitObject'],'workingSourceEqualsExactCommitBlob':upstream==source.read_bytes(),'workingSourceEqualsAcceptedEffectiveSource':True,'sha256':sha(source),'provenance':copy.deepcopy(p)})
 source_bytes.append({'module':module,'effectiveSource':p['frozenEffectiveSource'],'upstreamSource':p.get('frozenUpstreamSource',p['frozenEffectiveSource']),'sourceHeaderSha256':p['sourceHeaderSha256'],'originalNoticeRetained':True,'sourceGitBlobMatches':p['sourceGitBlobMatches']})
 for config in [unit,parser,export]:
  entry=next(x for x in config['sources'] if x['module']==module);entry['provenance']=copy.deepcopy(p)
write('inventory.json',inv);write('unit-config.json',unit);write('parser-config.json',parser)
export['inventorySha256']=sha(TASK/'inventory.json');write('export-config.json',export)
write('source-provenance-audit.json',{'schema':'next-carrier-source-provenance-audit-v1','records':provenance,'sourceLicenseLimit':'Tate repository tree has no standalone LICENSE/COPYING/NOTICE. Exact Tate source copyright/authors/Apache-2.0 notice is retained. Distributed Apache text is copied from the pinned iut license; it is not claimed as a Tate repository file.','readonlyGitCommandsOnly':True})
license_source=BASE/'refer/iut/LICENSE';(TASK/'LICENSE.Apache-2.0').write_bytes(license_source.read_bytes())
write('source-bytes-manifest.json',{'schema':'volume-tate-effective-upstream-source-bytes-v1','files':source_bytes,'distributedApacheText':{'source':str(license_source),'path':str(B/'LICENSE.Apache-2.0'),'sha256':sha(license_source)},'sourceOverridesPreserved':True})
imports=load(TASK/'imports.json');platform_math=Path('/home/admin-wsl/Coq/mathlib4-0df444a')
for m in imports:
 for c in m['candidates']:
  if c['sourceCompilerTermModule']=='Mathlib.Algebra.Group.Semigroup':
   c.update(platform433Candidate='Mathlib.Algebra.Group.Defs',platform433CandidatePathExists=True,status='Source checked candidate: exact source dependencies AddSemigroup.toAdd, AddCommMagma.toAdd, AddCommSemigroup.toAddCommMagma, AddLeftCancelSemigroup.toIsLeftCancelAdd are generated by the corresponding classes in platform Algebra.Group.Defs; target compiler validation remains required.')
   c['translationEvidence']={'path':str(platform_math/'Mathlib/Algebra/Group/Defs.lean'),'sha256':sha(platform_math/'Mathlib/Algebra/Group/Defs.lean'),'classDeclarationLines':{'AddSemigroup':182,'AddCommMagma':233,'AddCommSemigroup':251,'AddLeftCancelSemigroup':316}}
 m['platform433Candidates']=list(dict.fromkeys(['Mathlib.Algebra.Group.Defs' if x=='Mathlib.Algebra.Group.Semigroup' else x for x in m['platform433Candidates']]))
 if m['module']=='TateCurvesTheta.QParameter.NormalizedOrder':
  extras=[('Mathlib.Tactic.Linarith','Selected exact source orderZ_pos uses nlinarith/linarith and by_contra; retain tactic frontend, beyond proof-term dependency modules.'),('Lean.Elab.Tactic.NormCast','Selected exact source orderZ_pos uses exact_mod_cast.'),('Lean.Elab.Tactic.Omega','Selected exact source toOrdered positivity proof uses omega.')]
  m['proofSyntaxImportCandidates']=[{'module':n,'reason':reason,'status':'precise frontend candidate; main MCP-CI validation required'} for n,reason in extras]
  m['platform433Candidates']=list(dict.fromkeys(m['platform433Candidates']+[n for n,_ in extras]))
write('imports.json',imports)
closure=load(TASK/'dependency-closure.json');assert all(x['target'] for x in closure['requiredPriorActualPairs']);assert not any('solvableClosure' in x for x in closure['requiredPriorConstants'])
closure['requiredPriorAvailableNamedCount']=len(closure['requiredPriorActualPairs']);closure['requiredPriorProofValueResolutions']=[]
# Only bundles used by the actual closure are dependency input artifacts. Both unit evidence receipts remain pinned.
closure['importedBundles']=[b for b in closure['importedBundles'] if b['neededConstants']]
closure['sourceVersionPins']=[{'module':m['module'],'effectiveSource':m['source'],'effectiveSourceSha256':m['sourceSha256'],'upstreamSourceSha256':m['provenance']['upstreamSourceSha256'],'sourceGitObject':m['provenance']['sourceGitObject'],'sourceOverridden':m['provenance']['sourceOverridden']} for m in inv['modules']]
write('dependency-closure.json',closure)
plan=load(TASK/'machine-plan.json');plan.update(requiredPriorActualNamedCount=62,requiredPriorProofValueResolutions=[],sourceOverrides=['Iut.Cor312.LogVolume'],candidateImportStatus='all translated target source paths exist; compiler compatibility and exact syntax imports await main CI',additionalPriorModulesNeeded=[],additionalSourceRootCandidatesBeyondWholeCommandClosure=[])
write('machine-plan.json',plan)
write('exporter-cache-v2-provenance.json',{'schema':'volume-tate-exporter-cache-v2-provenance-v1','baseSource':'/tmp/p2m-next-carrier-kernel-v3-20261115/QueryNextCarrierOriginalExprsCached.lean','baseSha256':sha('/tmp/p2m-next-carrier-kernel-v3-20261115/QueryNextCarrierOriginalExprsCached.lean'),'source':str(B/'QueryNextCarrierOriginalExprs.lean'),'sha256':sha(TASK/'QueryNextCarrierOriginalExprs.lean'),'change':'Only exact original module import list replaced; optimized axiom cache and direct module lookup remain unchanged.','expectedRecordCount':147,'expectedSelectedCount':100,'environmentVariable':'NEXT_CARRIER_EXPORT_CONFIG','compilationPerformed':False})
print(json.dumps({'status':'draft-ready','allDeclarations':147,'selectedDeclarations':100,'sourceCommandRootCandidates':25,'requiredPriorActualNamedConstants':62,'importedPriorBundles':len(closure['importedBundles']),'sourceOverridePatchSha256':sha(TASK/'source-overrides/LogVolume.patch')},ensure_ascii=False))
