from pathlib import Path
import json,copy,hashlib,subprocess
ns={};exec(Path('/tmp/p2m-direct-tate-recovery-20261113.py').read_text().split('for row in order:run(row)')[0],ns)
rpc=ns['rpc'];b=ns['b'];r=ns['r'];p=ns['p'];d=ns['d'];save=ns['save']
assert len(list(d.glob('*-result.json')))==56
assert all(json.loads(f.read_text())['status']=='succeeded' for f in d.glob('*-result.json'))
attempts=b/'attempts';attempts.mkdir(exist_ok=True)
for n in ['request','submit','result']:
 f=b/('production-gates-'+n+'.json')
 if f.exists() and not (attempts/('production-gates-initial-'+n+'.json')).exists():f.rename(attempts/('production-gates-initial-'+n+'.json'))
q=copy.deepcopy(ns['base']);paths=q['environment']['LEAN_PATH'].split(':')
for path in [str(p/'.lake/build/lib/lean'),str(r/'ArithmeticTeichmullerSpaces/.lake/packages/formal-schemes/.lake/build/lib/lean')]:
 if path not in paths:paths.insert(-1,path)
q['environment']['LEAN_PATH']=':'.join(paths);q.update(expected_duration='90s',expected_memory='12GiB',idempotency_key='p2m-production-gates-20261113-locked-restored-direct-v2')
q['worktree_manifest']['required_artifacts']=paths;q['worktree_manifest']['input_version']='production-gates-restored-locked-tate-lean4331'
q['worktree_manifest']['configuration_hashes']={s:hashlib.sha256((r/s).read_bytes()).hexdigest() for s in q['worktree_manifest']['local_configuration']}
q['worktree_manifest']['head']=subprocess.check_output(['git','-C',str(r),'rev-parse','HEAD'],text=True).strip()
q['worktree_manifest']['modified_files']=subprocess.check_output(['git','-c','core.quotePath=false','-C',str(r),'diff','HEAD','--name-only'],text=True).splitlines()
q['worktree_manifest']['untracked_files']=subprocess.check_output(['git','-c','core.quotePath=false','-C',str(r),'ls-files','--others','--exclude-standard'],text=True).splitlines()
q['worktree_manifest']['input_hashes']={s:hashlib.sha256((r/s).read_bytes()).hexdigest() for s in q['worktree_manifest']['input_hashes']}
q['worktree_manifest']['source_sha256']=hashlib.sha256((r/q['parameters']['source']).read_bytes()).hexdigest()
q['idempotency_key']='p2m-production-gates-20261113-restored-patched-tate-v3-'+q['worktree_manifest']['source_sha256'][:16]
q['worktree_manifest']['external_dependencies'] += [{'path':str(p),'revision':'ca6c2279d3cea0690cdb01328e727118d5485d68','patch_sha256':hashlib.sha256((r/'ArithmeticTeichmullerSpaces/migration/patches/tate-curves-theta-lean433.patch').read_bytes()).hexdigest()},{'path':str(r/'ArithmeticTeichmullerSpaces/.lake/packages/formal-schemes'),'revision':'51aa935079537bf4dc580751a6e70727fb23ca93','patch_sha256':'86b69efbd1bdbd97522a1b27cb74f337297700e3d2ad9432ab535c50e035e209'}]
save(b/'production-gates-request.json',q);sp=b/'production-gates-submit.json'
if sp.exists():s=json.loads(sp.read_text())
else:s=rpc('ci_submit',q);save(sp,s)
job=s['job_id'];print(json.dumps({'gate_job':job,'status':'submitted'}),flush=True)
while True:
 x=rpc('ci_wait',{'job_id':job,'session_id':q['session_id'],'timeout_seconds':20})
 if x['status'] not in ['queued','running','preparing_snapshot']:break
x=rpc('ci_result',{'job_id':job});save(b/'production-gates-result.json',x)
print(json.dumps({'job_id':job,'status':x['status'],'resources':x['resources'],'result':{'exit_code':x['result'].get('exit_code'),'actual_arguments':x['result'].get('actual_arguments'),'stdout_tail':x['result'].get('stdout','')[-6000:],'stderr_tail':x['result'].get('stderr','')[-2000:],'review_passed':x['result'].get('review',{}).get('passed')}},ensure_ascii=False),flush=True)
assert x['status']=='succeeded' and x['result']['review']['passed']
assert x['result']['snapshot']['workspace_mode']=='exclusive_worktree' and x['result']['snapshot']['snapshot_id'] is None
