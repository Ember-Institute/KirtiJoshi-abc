from pathlib import Path
import json,socket,hashlib,copy,subprocess,sys
w=Path('/home/admin-wsl/Coq/abc/prove2me_workspace');b=w/'.local/adaptation/fermat-proper-canonical-20261113';base=json.loads((b/'base-request.json').read_text())
def save(n,x):(b/n).write_text(json.dumps(x,ensure_ascii=False,indent=2)+'\n')
def rpc(name,args):
 s=socket.socket(socket.AF_UNIX);s.settimeout(40)
 try:
  s.connect('/home/admin-wsl/codex-miniCI/data/mcp-ci.sock');s.sendall((json.dumps({'jsonrpc':'2.0','id':'p2m-proper-canonical-main','method':'tools/call','params':{'name':name,'arguments':args}})+'\n').encode());raw=json.loads(s.makefile('r').readline())
 finally:s.close()
 if 'error' in raw:raise RuntimeError(raw['error'])
 x=raw['result'];return x.get('structuredContent') or json.loads(next(c['text'] for c in x['content'] if c['type']=='text'))
def wait(tag,job,req):
 while True:
  x=rpc('ci_wait',{'job_id':job,'session_id':req['session_id'],'agent_id':'/root','timeout_seconds':20})
  if x['status'] not in ['queued','running','preparing_snapshot']:break
 x=rpc('ci_result',{'job_id':job});save(tag+'-result.json',x);r=x.get('result',{});v=x.get('resources',{});print(json.dumps({'tag':tag,'job_id':job,'status':x['status'],'exit_code':r.get('exit_code'),'wall':v.get('wall_time_seconds'),'cpu':v.get('cpu_time_seconds'),'rss':v.get('peak_rss_bytes'),'stdout':r.get('stdout','')[:2200],'stderr':r.get('stderr','')[:1200],'review':r.get('review',{}).get('passed')},ensure_ascii=False),flush=True)
 if x['status']!='succeeded':sys.exit(1)
 return x
def run(tag,source,kind='leaf',output=False):
 p=b/(tag+'-result.json')
 if p.exists() and json.loads(p.read_text())['status']=='succeeded':print(tag,'already succeeded',flush=True);return
 req=copy.deepcopy(base);params={'args':[source,'-o','.lake/build/lib/lean/'+source[:-5]+'.olean']} if output else {'source':source};req.update(task_type=kind,target='module' if output else 'file',parameters=params,expected_duration='60s',expected_memory='6GiB' if (tag.startswith('renamed-') or tag in ['local-belyi-leaf','local-belyi-composition-leaf']) else ('16GiB' if kind=='leaf' else '6GiB'));sha=hashlib.sha256((w/source).read_bytes()).hexdigest();req['idempotency_key']='p2m-proper-canonical-'+tag+'-20261113-v4-'+sha[:16];m=req['worktree_manifest'];m.update(source_sha256=sha,input_version=tag+'-'+sha,modified_files=subprocess.check_output(['git','-c','core.quotePath=false','-C',str(w.parent),'diff','HEAD','--name-only'],text=True).splitlines(),untracked_files=subprocess.check_output(['git','-c','core.quotePath=false','-C',str(w.parent),'ls-files','--others','--exclude-standard'],text=True).splitlines());save(tag+'-request.json',req)
 sub=b/(tag+'-submit.json')
 if sub.exists():x=json.loads(sub.read_text())
 else:x=rpc('ci_submit',req);save(sub.name,x)
 print(tag,'submitted',x['job_id'],flush=True);wait(tag,x['job_id'],req)
for tag,source in [
 ('divisor-height','Definitions/Def_FermatProperDivisorHeight.lean'),
 ('divisor-composition','Definitions/Def_FermatProperDivisorComposition.lean'),
 ('local-belyi','Definitions/Def_FermatLocalBelyi.lean'),
 ('local-belyi-composition','Definitions/Def_FermatLocalBelyiComposition.lean'),
 ('comparisons','Definitions/Def_FermatBelyiComparisons.lean'),
 ('canonical-composition','Definitions/Def_FermatCanonicalBelyiComposition.lean')]:
 run(tag+'-leaf',source);run(tag+'-artifact',source,'full',True)
run('closed-compositions-review','Solutions/Checks_FermatProperCanonicalComposition.lean','review')
for name in ['modelExists','placesDiscrete','residuesFinite','affineIdentification','noncriticalSelection','cuspsFinite']:
 source='Theorems/Thm_AbcAdaptation_Tripod_Fermat_Proper_'+name+'.lean';run('renamed-'+name+'-leaf',source);run('renamed-'+name+'-artifact',source,'full',True)
for name in ['polarPresentationExists','canonicalDivisorExists','infinityDivisorExists','planeAdjunctionExists','cuspGeneratorsExists','canonicalDivisorDegree','localCompactness','avoidanceRegularity','embeddingBoundsToSet','canonicalHeightIdentification','belyiHeightRelation','divisorDegreeHeightComparison','belyiDifferentConductorComparison','cuspConductorHeightComparison']:
 source='Theorems/Thm_AbcAdaptation_Tripod_Fermat_Proper_'+name+'.lean';run(name+'-leaf',source);run(name+'-artifact',source,'full',True)
run('canonical-solution-leaf','Solutions/Sol_FermatCanonicalEstimate.lean')
run('canonical-solution-artifact','Solutions/Sol_FermatCanonicalEstimate.lean','full',True)
run('canonical-reduction-axioms','Solutions/Checks_FermatCanonicalReduction.lean')
print('Proper canonical Fermat decomposition passed local validation.',flush=True)
