#!/usr/bin/env python3
import difflib,hashlib,json,subprocess
from pathlib import Path
P=Path('/tmp/p2m-volume-tate-inventory-v4-20261115');B=Path('/home/admin-wsl/Coq/abc/prove2me_workspace/.local/adaptation/reference-volume-tate-carriers-20261115')
def load(p):return json.loads(Path(p).read_text())
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def draft(p):return P/Path(p).relative_to(B)
def git(repo,*args):return subprocess.run(['git','-C',str(repo),*args],capture_output=True,check=True).stdout
inv=load(P/'inventory.json');audit=load(P/'source-provenance-audit.json');checks=[]
def ck(x,msg):
 assert x,msg
 checks.append(msg)
for m in inv['modules']:
 p=m['provenance'];r=next(r for r in audit['records'] if r['module']==m['module']);upstream=git(p['actualGitRepository'],'show',p['originalCommit']+':'+p['originalSourcePath']);raw=Path(m['source']).read_bytes()
 ck(hashlib.sha256(upstream).hexdigest()==p['upstreamSourceSha256'],m['module']+' upstream Git blob SHA')
 ck(hashlib.sha256(raw).hexdigest()==m['sourceSha256']==p['sourceSha256']==r['sha256'],m['module']+' effective bytes SHA')
 ck((raw==upstream)==p['sourceGitBlobMatches']==r['workingSourceEqualsExactCommitBlob'],m['module']+' truthful source/blob equality')
 ck(draft(p['frozenEffectiveSource']['path']).read_bytes()==raw,m['module']+' frozen exact source bytes')
 if 'effectiveSourceOverride' in p:
  o=p['effectiveSourceOverride'];receipt=load(o['acceptance']['path']);plan=load(o['sourceBuildPlan']['path'])
  ck(receipt['status']=='succeeded' and receipt['job_id']==o['acceptance']['job_id'],m['module']+' accepted graph receipt')
  ck(sha(o['sourceBuildPlan']['path'])==o['sourceBuildPlan']['sha256']==receipt['request']['worktree_manifest']['source_build_plan_sha256'],m['module']+' accepted source-build plan binding')
  entry=next(x for x in plan['input_modules'] if x['module']==m['module'])
  ck(entry['workspace_source']==m['source'] and entry['sha256']==m['sourceSha256'] and entry['original_sha256']==p['upstreamSourceSha256'],m['module']+' plan binds both original/effective source')
  expected=''.join(difflib.unified_diff(Path(o['upstreamSource']).read_text().splitlines(keepends=True),Path(m['source']).read_text().splitlines(keepends=True),fromfile=p['originalSourcePath'],tofile=p['originalSourcePath']+' (accepted effective source)')).encode()
  ck(draft(o['patch']['path']).read_bytes()==expected and sha(draft(o['patch']['path']))==o['patch']['sha256'],m['module']+' complete exact source delta')
  for k in ['acceptance','sourceBuildPlan','acceptedGraphSourceReceipt','effectiveSourceLeafAcceptance','effectiveSourceRepairExplanation']:
   ck(sha(o[k]['path'])==o[k]['sha256'],m['module']+' '+k+' evidence SHA')
  ck(draft(p['frozenUpstreamSource']['path']).read_bytes()==upstream,m['module']+' frozen exact upstream bytes')
for f in ['inventory.json','parser-config.json','unit-config.json','export-config.json']:
 d=load(P/f);entries=d.get('modules',d.get('sources'))
 for m in entries:
  other=next(x for x in inv['modules'] if x['module']==m['module'])
  ck(m['source']==other['source'] and m['provenance']==other['provenance'],f+' '+m['module']+' source/provenance agreement')
# Verify explicit frontend candidates at the target toolchain/source, without a compiler.
imports=load(P/'imports.json');math=Path('/home/admin-wsl/Coq/mathlib4-0df444a');lean=Path('/root/.elan/toolchains/leanprover--lean4---v4.33.1/src/lean')
for m in imports:
 for x in m['platform433Candidates']:
  if x.startswith('Definitions.'):continue
  root=math if x.startswith('Mathlib.') else lean
  ck(root.joinpath(*x.split('.')).with_suffix('.lean').is_file(),m['module']+' precise import source exists '+x)
result={'schema':'volume-tate-provenance-static-audit-v1','status':'passed','checkCount':len(checks),'checks':checks,'compilationPerformed':False,'networkAccessPerformed':False,'mainWorkspaceModified':False}
(P/'provenance-static-audit.json').write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n')
print(json.dumps({'status':'passed','checkCount':len(checks)}))
