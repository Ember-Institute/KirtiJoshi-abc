from pathlib import Path
import json,socket,hashlib,copy,subprocess,time
r=Path('/home/admin-wsl/Coq/abc');b=r/'prove2me_workspace/.local/adaptation/fermat-proper-canonical-20261113';d=b/'tate-direct-recovery';d.mkdir(exist_ok=True)
p=r/'ArithmeticTeichmullerSpaces/.lake/packages/tate-curves-theta';lib=p/'.lake/build/lib/lean';base=json.loads((b/'production-gates-request.json').read_text());order=json.loads(Path('/tmp/p2m-tate-closure-20261113.json').read_text());(d/'closure.json').write_text(json.dumps(order,indent=2)+'\n')
def save(path,x):path.write_text(json.dumps(x,ensure_ascii=False,indent=2)+'\n')
def rpc(name,args):
 for n in range(3):
  s=socket.socket(socket.AF_UNIX);s.settimeout(40)
  try:
   s.connect('/home/admin-wsl/codex-miniCI/data/mcp-ci.sock');s.sendall((json.dumps({'jsonrpc':'2.0','id':'p2m-direct-tate-recovery','method':'tools/call','params':{'name':name,'arguments':args}})+'\n').encode());raw=json.loads(s.makefile('r').readline())
   if 'error' in raw:raise RuntimeError(raw['error'])
   x=raw['result'];return x.get('structuredContent') or json.loads(next(c['text'] for c in x['content'] if c['type']=='text'))
  except (TimeoutError,ConnectionError,OSError) as e:
   print(json.dumps({'transport_retry':name,'attempt':n+1,'error':str(e)}),flush=True)
   if n==2:raise
  finally:s.close()
def run(row):
 m=row['module'];tag=m.replace('.','_');dest=d/(tag+'-result.json')
 if dest.exists() and json.loads(dest.read_text())['status']=='succeeded':return
 source=m.replace('.','/')+'.lean';out='.lake/build/lib/lean/'+m.replace('.','/')+'.olean';(p/out).parent.mkdir(parents=True,exist_ok=True)
 q=copy.deepcopy(base);q.update(task_type='full',target='module',working_directory=str(p.relative_to(r)),parameters={'args':[source,'-o',out]},expected_duration='60s',expected_memory='16GiB',session_id='p2m-direct-tate-recovery-20261113')
 paths=q['environment']['LEAN_PATH'].split(':');paths.insert(-1,str(lib));paths.insert(-1,str(r/'ArithmeticTeichmullerSpaces/.lake/packages/formal-schemes/.lake/build/lib/lean'));q['environment']['LEAN_PATH']=':'.join(paths)
 sha=hashlib.sha256((p/source).read_bytes()).hexdigest();q['idempotency_key']='p2m-direct-tate-20261113-cache32-r2-'+tag+'-'+sha[:16]
 if m=='TateCurvesTheta.AnalyticQuotient':q['idempotency_key']+='-external-closure-cache-r4';q['expected_duration']='120s';q['expected_memory']='12GiB'
 man=q['worktree_manifest'];man.update(input_version='locked-tate-direct-'+m,source_sha256=sha,modified_files=subprocess.check_output(['git','-c','core.quotePath=false','-C',str(r),'diff','HEAD','--name-only'],text=True).splitlines(),untracked_files=subprocess.check_output(['git','-c','core.quotePath=false','-C',str(r),'ls-files','--others','--exclude-standard'],text=True).splitlines())
 man['input_hashes']={str(f.relative_to(r)):hashlib.sha256(f.read_bytes()).hexdigest() for f in (p/'TateCurvesTheta').rglob('*.lean')};man['required_artifacts']=paths;man['external_dependencies'].append({'path':str(p),'revision':'ca6c2279d3cea0690cdb01328e727118d5485d68','restoration':'locked sources; direct compiler uses existing Mathlib 0df444a artifacts'})
 save(d/(tag+'-request.json'),q);sp=d/(tag+'-submit.json')
 if sp.exists():sub=json.loads(sp.read_text())
 else:sub=rpc('ci_submit',q);save(sp,sub)
 job=sub['job_id'];print(json.dumps({'module':m,'job_id':job,'status':'submitted'}),flush=True)
 while True:
  x=rpc('ci_wait',{'job_id':job,'session_id':q['session_id'],'timeout_seconds':20})
  if x['status'] not in ['queued','running','preparing_snapshot']:break
 x=rpc('ci_result',{'job_id':job});save(dest,x);v=x['resources'];res=x['result'];print(json.dumps({'module':m,'job_id':job,'status':x['status'],'wall':v.get('wall_time_seconds'),'cpu':v.get('cpu_time_seconds'),'rss':v.get('peak_rss_bytes'),'stderr':res.get('stderr','')[:1800],'stdout':res.get('stdout','')[-2500:]}),flush=True)
 assert x['status']=='succeeded',(m,x['status'])
 assert v.get('peak_rss_bytes') is None or v['peak_rss_bytes']<=16*1024**3,(m,'requires split')
 assert res['snapshot']['workspace_mode']=='exclusive_worktree' and res['snapshot']['snapshot_id'] is None
 assert res['actual_arguments']==['lean',source,'-o',out]
base['worktree_manifest']['configuration_hashes']={s:hashlib.sha256((r/s).read_bytes()).hexdigest() for s in base['worktree_manifest']['local_configuration']}
for row in order:run(row)
print('Direct Tate cache restoration complete.',flush=True)
