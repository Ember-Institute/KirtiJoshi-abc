from pathlib import Path
import copy,hashlib,json,math,subprocess,sys
sys.path.insert(0,str(Path(__file__).resolve().parent.parent/'cusp-conductor-sourceproof-20261115'))
from scheduler_common import rpc
b=Path(__file__).resolve().parent;w=b.parents[2];r=w.parent;p=b/'source-project'
plan=json.loads((b/'source-build-plan.json').read_text())
base=json.loads((b/'cached32-request.json').read_text())
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def save(name,x):
 (b/name).write_text(json.dumps(x,ensure_ascii=False,indent=2)+'\n')
def run(item,artifact=False):
 module=item['module'];source=module.replace('.','/')+'.lean';tag=module.replace('.','-')+('-artifact' if artifact else '-leaf')
 resultfile=b/(tag+'-result.json')
 if resultfile.exists():
  old=json.loads(resultfile.read_text())
  if old['status']!='succeeded':raise RuntimeError('Archive failure before retry: '+tag)
  assert old['request']['worktree_manifest']['source_sha256']==sha(p/source)
  print(tag+' already succeeded',flush=True);return old
 q=copy.deepcopy(base);q['working_directory']=str(p.relative_to(w));q['environment']['LEAN_PATH']=str(p/'.lake/build/lib/lean')+':'+q['environment']['LEAN_PATH']
 q['parameters']={'source':source};q['task_type']='leaf';q['target']='file';q['expected_duration']='60s';q['expected_memory']='16GiB'
 if artifact:
  output=p/'.lake/build/lib/lean'/Path(source).with_suffix('.olean');output.parent.mkdir(parents=True,exist_ok=True)
  resources=json.loads((b/(module.replace('.','-')+'-leaf-result.json')).read_text())['resources']
  q['task_type']='full';q['target']='module';q['parameters']={'args':[source,'-o',str(output.relative_to(p))]}
  q['expected_duration']=str(max(30,math.ceil(resources['wall_time_seconds']*1.3)))+'s'
  q['expected_memory']=str(max(1,min(16,math.ceil(resources['peak_rss_bytes']/1024**3*1.3))))+'GiB'
 if module=='Iut.Cor312.LogVolume' and not artifact:
  q['expected_duration']='208s';q['expected_memory']='10GiB'
 if module=='Iut.Implication.Theorem110' and not artifact:
  q['expected_duration']='230s';q['expected_memory']='11GiB'
 if module=='Iut.Implication.Corollary22' and not artifact:
  q['expected_duration']='300s';q['expected_memory']='12GiB'
 q['idempotency_key']='p2m-reference-source-'+tag+'-v7-'+sha(p/source)[:16]
 q['worktree_manifest']={'worktree_id':str(r),'head':subprocess.check_output(['git','-C',str(r),'rev-parse','HEAD'],text=True).strip(),'modified_files':subprocess.check_output(['git','-c','core.quotePath=false','-C',str(r),'diff','HEAD','--name-only'],text=True).splitlines(),'untracked_files':subprocess.check_output(['git','-c','core.quotePath=false','-C',str(r),'ls-files','--others','--exclude-standard'],text=True).splitlines(),'purpose':plan['purpose'],'source_sha256':sha(p/source),'working_directory':str(p),'toolchain':(p/'lean-toolchain').read_text().strip(),'platform_toolchain_unchanged':(w/'lean-toolchain').read_text().strip(),'source_build_plan_sha256':sha(b/'source-build-plan.json'),'source_hashes':{i['module']:sha(Path(i['workspace_source'])) for i in plan['input_modules']},'external_dependencies_manifest':str(b/'artifact-manifest.json'),'external_dependencies_manifest_sha256':sha(b/'artifact-manifest.json'),'source_import_closure':str(b/'module-closure-hashes.json'),'source_import_closure_sha256':sha(b/'module-closure-hashes.json'),'cache_overlay_links':str(b/'read-only-cache-links.json'),'cache_overlay_links_sha256':sha(b/'read-only-cache-links.json'),'required_artifacts':q['environment']['LEAN_PATH'].split(':'),'dependency_lock':'original refer/iut/lake-manifest.json','dependency_lock_sha256':sha(r/'refer/iut/lake-manifest.json'),'read_only_reference_cache':plan['read_only_cache'],'no_cache_copy':True}
 submitfile=b/(tag+'-submit.json')
 if submitfile.exists():
  assert json.loads((b/(tag+'-request.json')).read_text())==q
  z=json.loads(submitfile.read_text())
 else:
  save(tag+'-request.json',q);z=rpc('ci_submit',q);save(tag+'-submit.json',z)
 jid=z['job_id'];print(json.dumps({'tag':tag,'job_id':jid,'status':z['status']}),flush=True)
 while True:
  status=rpc('ci_wait',{'job_id':jid,'timeout_seconds':20})
  if status['status'] not in ['queued','running','preparing_snapshot']:break
 z=rpc('ci_result',{'job_id':jid});save(tag+'-result.json',z);res=z.get('resources',{});out=z.get('result',{})
 print(json.dumps({'tag':tag,'job_id':jid,'status':z['status'],'wall':res.get('wall_time_seconds'),'cpu':res.get('cpu_time_seconds'),'rss':res.get('peak_rss_bytes'),'stdout':out.get('stdout','')[-6500:],'stderr':out.get('stderr','')[-2000:]},ensure_ascii=False),flush=True)
 if z['status']!='succeeded':sys.exit(1)
 assert out['exit_code']==0 and out['snapshot']['workspace_mode']=='exclusive_worktree' and out['snapshot']['snapshot_id'] is None
 assert out['actual_arguments']==(['lean']+q['parameters']['args'] if artifact else ['lean',source])
 if res.get('peak_rss_bytes',0)>16*1024**3:raise RuntimeError('Split source module before further builds')
 return z
for item in plan['input_modules']:
 run(item);run(item,True)
