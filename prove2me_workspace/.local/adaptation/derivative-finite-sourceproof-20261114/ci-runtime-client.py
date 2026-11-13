from pathlib import Path
import json,socket,hashlib,copy,subprocess,sys,math
r=Path('/home/admin-wsl/Coq/abc');w=r/'prove2me_workspace';b=w/'.local/adaptation/fermat-riemann-sourceproof-20261114'
base=json.loads((w/'.local/adaptation/fermat-proper-canonical-20261113/production-gates-request.json').read_text())
base.update(workspace=str(w),project_id='ArithmeticTeichmullerSpaces',session_id='p2m-fermat-riemann-sourceproof-20261114',agent_id='/root',exclusive=True)
base.pop('working_directory',None)
for dep in base['worktree_manifest']['external_dependencies']:
 if dep['path'].endswith('/tate-curves-theta'):
  dep['patch_sha256']=hashlib.sha256((r/'ArithmeticTeichmullerSpaces/migration/patches/tate-curves-theta-lean433.patch').read_bytes()).hexdigest()
def save(n,x):(b/n).write_text(json.dumps(x,ensure_ascii=False,indent=2)+'\n')
def rpc(name,args):
 s=socket.socket(socket.AF_UNIX);s.settimeout(40)
 try:
  s.connect('/home/admin-wsl/codex-miniCI/data/mcp-ci.sock');s.sendall((json.dumps({'jsonrpc':'2.0','id':'p2m-fermat-riemann','method':'tools/call','params':{'name':name,'arguments':args}})+'\n').encode());raw=json.loads(s.makefile('r').readline())
 finally:s.close()
 if 'error' in raw:raise RuntimeError(raw['error'])
 z=raw['result'];return z.get('structuredContent') or json.loads(next(c['text'] for c in z['content'] if c['type']=='text'))
def manifest(source):
 cfg=['lean-toolchain','lakefile.lean','lake-manifest.json'];files=[p for folder in ['Definitions','Theorems','Solutions'] for p in (w/folder).glob('*.lean')]
 return {'worktree_id':str(r),'head':subprocess.check_output(['git','-C',str(r),'rev-parse','HEAD'],text=True).strip(),'modified_files':subprocess.check_output(['git','-c','core.quotePath=false','-C',str(r),'diff','HEAD','--name-only'],text=True).splitlines(),'untracked_files':subprocess.check_output(['git','-c','core.quotePath=false','-C',str(r),'ls-files','--others','--exclude-standard'],text=True).splitlines(),'toolchain':(w/'lean-toolchain').read_text().strip(),'dependency_lock':'lake-manifest.json','dependency_lock_sha256':hashlib.sha256((w/'lake-manifest.json').read_bytes()).hexdigest(),'local_configuration':cfg,'configuration_hashes':{s:hashlib.sha256((w/s).read_bytes()).hexdigest() for s in cfg},'input_hashes':{str(p.relative_to(w)):hashlib.sha256(p.read_bytes()).hexdigest() for p in files},'source_sha256':hashlib.sha256((w/source).read_bytes()).hexdigest(),'input_version':'fermat-riemann-'+source,'external_dependencies':base['worktree_manifest']['external_dependencies'],'required_artifacts':base['environment']['LEAN_PATH'].split(':'),'excluded_credentials':'credentials.json ignored; exclusive mode does not copy files'}
def run(tag,source,kind='leaf',artifact=False,duration='60s',memory='16GiB',version='v1'):
 dest=b/(tag+'-result.json')
 if dest.exists() and json.loads(dest.read_text())['status']=='succeeded':print(tag,'already succeeded',flush=True);return
 q=copy.deepcopy(base);params={'args':[source,'-o','.lake/build/lib/lean/'+source[:-5]+'.olean']} if artifact else {'source':source}
 retries=sorted((b/'attempts').glob(tag+'-v*-result.json'),key=lambda p:p.stat().st_mtime)
 if retries and not artifact:
  previous=json.loads(retries[-1].read_text());v=previous['resources']
  measured=v.get('wall_time_seconds')
  if measured is not None:duration=str(max(60,math.ceil(measured*1.4)))+'s'
  elif previous['status']=='timeout' and previous.get('compile_time_seconds') is not None:
   duration=str(max(60,math.ceil(previous['compile_time_seconds']*1.4)))+'s'
  if v.get('peak_rss_bytes') is not None:memory=str(min(16,math.ceil(v['peak_rss_bytes']/1024**3*1.3)))+'GiB'
 if artifact:
  measured=b/(tag.removesuffix('-artifact')+'-leaf-result.json')
  if measured.exists():
   v=json.loads(measured.read_text())['resources'];duration=str(max(60,math.ceil(v['wall_time_seconds']*1.3)))+'s';memory=str(min(16,math.ceil(v['peak_rss_bytes']/1024**3*1.3)))+'GiB'
 if artifact:(w/'.lake/build/lib/lean'/source).parent.mkdir(parents=True,exist_ok=True)
 q.update(task_type='full' if artifact else kind,target='module' if artifact else 'file',parameters=params,expected_duration=duration,expected_memory=memory,worktree_manifest=manifest(source))
 q['idempotency_key']='p2m-fermat-riemann-sourceproof-'+tag+'-'+version+'-'+q['worktree_manifest']['source_sha256'][:16];save(tag+'-request.json',q);sp=b/(tag+'-submit.json')
 if sp.exists():s=json.loads(sp.read_text())
 else:s=rpc('ci_submit',q);save(sp.name,s)
 job=s['job_id'];print(json.dumps({'tag':tag,'job_id':job,'status':'submitted'}),flush=True)
 while True:
  x=rpc('ci_wait',{'job_id':job,'timeout_seconds':20})
  if x['status'] not in ['queued','running','preparing_snapshot']:break
 x=rpc('ci_result',{'job_id':job});save(dest.name,x);res=x.get('result',{});v=x.get('resources',{});print(json.dumps({'tag':tag,'job_id':job,'status':x['status'],'wall':v.get('wall_time_seconds'),'cpu':v.get('cpu_time_seconds'),'rss':v.get('peak_rss_bytes'),'stdout':res.get('stdout','')[:6500] if ('PANIC' in res.get('stdout','') or 'internal exception' in res.get('stdout','')) else res.get('stdout','')[-6500:],'stderr':res.get('stderr','')[-1600:],'review_passed':res.get('review',{}).get('passed') if res.get('review') else None},ensure_ascii=False),flush=True)
 if x['status']!='succeeded':sys.exit(1)
 assert res['exit_code']==0 and res['snapshot']['workspace_mode']=='exclusive_worktree' and res['snapshot']['snapshot_id'] is None
 assert v.get('peak_rss_bytes') is None or v['peak_rss_bytes']<=16*1024**3
 assert res['actual_arguments']==(['lean']+params['args'] if artifact else ['lean',source])
 if kind=='review':assert res['review']['passed']
if __name__=='__main__':
 for n in ['FermatCurveFieldDegree','FermatFunctionFiberDegrees','FermatRiemannPolarApproximation','FermatRiemannBasisPowers']:
  source='Definitions/Def_'+n+'.lean';run(n+'-leaf',source);run(n+'-artifact',source,artifact=True)
 for n in ['functionZeroPoleDegrees','riemannPolarApproximation','riemannBasisPowerLowerBound']:
  source='Theorems/Thm_AbcAdaptation_Tripod_Fermat_Proper_'+n+'.lean';run(n+'-leaf',source,memory='6GiB');run(n+'-artifact',source,artifact=True)
 run('sourceproof-closed-review','Solutions/Checks_FermatRiemannSourceProofs.lean','review',memory='8GiB')
