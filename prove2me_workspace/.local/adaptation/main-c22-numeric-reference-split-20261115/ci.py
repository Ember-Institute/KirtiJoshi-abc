from pathlib import Path
import copy,json,hashlib,math,subprocess,sys
sys.path.insert(0,str(Path(__file__).resolve().parent.parent/'cusp-conductor-sourceproof-20261115'))
from scheduler_common import rpc,manifest
b=Path(__file__).resolve().parent;w=b.parents[2]
base=json.loads((b.parent/'reference-extraction-20261115/production-gates-request.json').read_text())
base['environment'].update(NUMERIC_ORIGINAL_EXPR_FILE=str(b/'source-facts/original-exprs.json'),NUMERIC_AUDIT_OUTPUT_DIR=str(b/'type-audits'))
base.update(session_id='p2m-main-c22-numeric-reference-split-20261115',agent_id='/root',exclusive=True)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def save(name,x):(b/name).write_text(json.dumps(x,ensure_ascii=False,indent=2)+'\n')
def run(tag,source,artifact=False,review=False):
 path=b/(tag+'-result.json')
 if path.exists():
  z=json.loads(path.read_text())
  if z['status']!='succeeded':raise RuntimeError('Archive failed attempt before retry '+tag)
  assert z['request']['worktree_manifest']['source_sha256']==sha(w/source)
  print(tag+' already succeeded',flush=True);return z
 q=copy.deepcopy(base);q.update(task_type='review' if review else 'leaf',target='file',parameters={'source':source},expected_duration='60s',expected_memory='16GiB')
 if artifact:
  output=w/'.lake/build/lib/lean'/Path(source).with_suffix('.olean');output.parent.mkdir(parents=True,exist_ok=True)
  prior=json.loads((b/(tag.removesuffix('-artifact')+'-leaf-result.json')).read_text())['resources']
  q.update(task_type='full',target='module',parameters={'args':[source,'-o',str(output.relative_to(w))]},expected_duration=str(max(30,math.ceil(prior['wall_time_seconds']*1.3)))+'s',expected_memory=str(max(2,min(16,math.ceil(prior['peak_rss_bytes']/1024**3*1.3))))+'GiB')
 if 'Sol_AbcAdaptation_Reference_Iut_LocalHeightData_exists_prime_selection' in source and not artifact:
  q['expected_duration']='65s';q['expected_memory']='5GiB'
 q['worktree_manifest']=manifest(source);q['worktree_manifest']['purpose']='Two exact pure real numerical reference source proofs on pinned platform4.33.1; no Definitions; targets exact source statements';q['idempotency_key']='p2m-main-c22-numeric-'+tag+'-v1-'+sha(w/source)[:16]
 request=b/(tag+'-request.json');submit=b/(tag+'-submit.json')
 if submit.exists():
  assert json.loads(request.read_text())==q
  z=json.loads(submit.read_text())
 else:
  save(request.name,q);z=rpc('ci_submit',q);save(submit.name,z)
 jid=z['job_id'];print(json.dumps({'tag':tag,'job_id':jid,'status':z['status']}),flush=True)
 while True:
  status=rpc('ci_wait',{'job_id':jid,'timeout_seconds':20})
  if status['status'] not in ['queued','running','preparing_snapshot']:break
 z=rpc('ci_result',{'job_id':jid});save(path.name,z);res=z.get('resources',{});r=z.get('result',{})
 print(json.dumps({'tag':tag,'job_id':jid,'status':z['status'],'wall':res.get('wall_time_seconds'),'cpu':res.get('cpu_time_seconds'),'rss':res.get('peak_rss_bytes'),'stdout':r.get('stdout','')[-6000:],'stderr':r.get('stderr','')[-1500:]},ensure_ascii=False),flush=True)
 if z['status']!='succeeded':sys.exit(1)
 assert r['exit_code']==0 and r['snapshot']['workspace_mode']=='exclusive_worktree' and r['snapshot']['snapshot_id'] is None
 assert r['actual_arguments']==(['lean']+q['parameters']['args'] if artifact else ['lean',source])
 assert not any(t in r.get('stdout','')+r.get('stderr','') for t in ['PANIC','error:','error('])
 assert res.get('peak_rss_bytes') is None or res['peak_rss_bytes']<=16*1024**3
 if review:assert r['review']['passed']
 return z
if __name__=='__main__':
 files=json.loads((b/'integration.json').read_text())['files']
 ordered=sorted(files,key=lambda p:(0 if p.startswith('Definitions/') else 1 if p.startswith('Theorems/') else 2, 'LocalHeightData' in p,p))
 for source in ordered:
  tag=Path(source).stem
  run(tag+'-leaf',source);run(tag+'-artifact',source,artifact=True)
