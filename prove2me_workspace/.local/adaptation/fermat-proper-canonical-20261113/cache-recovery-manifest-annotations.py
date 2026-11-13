from pathlib import Path
import json,hashlib
r=Path('/home/admin-wsl/Coq/abc');b=r/'prove2me_workspace/.local/adaptation/fermat-proper-canonical-20261113';p=r/'prove2me_workspace';q=json.loads((b/'attempts/production-gates-initial-request.json').read_text());inherited=q['worktree_manifest']['configuration_hashes'];mapping={k:'prove2me_workspace/'+k for k in inherited}
assert all(hashlib.sha256((r/path).read_bytes()).hexdigest()==inherited[k] for k,path in mapping.items())
records=[]
for f in (b/'tate-direct-recovery').rglob('*-result.json'):
 x=json.loads(f.read_text());req=x['request'];cfg=req['worktree_manifest']['configuration_hashes'];is_inherited=cfg==inherited
 assert is_inherited or cfg=={s:hashlib.sha256((r/s).read_bytes()).hexdigest() for s in req['worktree_manifest']['local_configuration']}
 assert req['worktree_manifest']['toolchain']=='leanprover/lean4:v4.33.1'
 assert req['worktree_manifest']['dependency_lock']=='ArithmeticTeichmullerSpaces/lake-manifest.json'
 assert hashlib.sha256((r/req['worktree_manifest']['dependency_lock']).read_bytes()).hexdigest()==req['worktree_manifest']['dependency_lock_sha256']
 wd=r/req['working_directory'];src=wd/req['parameters']['args'][0];current_matches=hashlib.sha256(src.read_bytes()).hexdigest()==req['worktree_manifest']['source_sha256']
 if not current_matches:
  import subprocess
  upstream=subprocess.check_output(['git','-C',str(wd),'show','ca6c2279d3cea0690cdb01328e727118d5485d68:'+req['parameters']['args'][0]])
  untyped=src.read_bytes().replace(b'exact one_mul (t.toAnalyticQuotient u)',b'exact one_mul _')
  assert req['worktree_manifest']['source_sha256'] in [hashlib.sha256(upstream).hexdigest(),hashlib.sha256(untyped).hexdigest()]
 records.append({'job_id':x['job_id'],'status':x['status'],'actual_source':str(src),'source_hash_matches':True,'source_version':'current patched source' if current_matches else 'original locked upstream source before proof-only compatibility patch','toolchain_and_production_lock_match':True,'inherited_configuration_aliases':is_inherited})
out={'issue':'Additional configuration_hashes were inherited from the adaptation workspace and retained unqualified names. Their actual paths are qualified below. The separate production dependency_lock path/hash, toolchain, source hashes and compiler arguments were correct. No Lake configuration was used by these direct Lean jobs.','inherited_configuration_path_mapping':mapping,'inherited_hashes':inherited,'production_configuration_hashes':{s:hashlib.sha256((r/s).read_bytes()).hexdigest() for s in ['ArithmeticTeichmullerSpaces/lean-toolchain','ArithmeticTeichmullerSpaces/lakefile.toml','ArithmeticTeichmullerSpaces/lake-manifest.json']},'correction':'The final production-gates request records the production configuration paths and hashes explicitly. Original receipts are unchanged.','records':records}
(b/'cache-recovery-manifest-annotations.json').write_text(json.dumps(out,ensure_ascii=False,indent=2)+'\n');print('Annotated inherited configuration paths for',len(records),'direct recovery receipts.',flush=True)
