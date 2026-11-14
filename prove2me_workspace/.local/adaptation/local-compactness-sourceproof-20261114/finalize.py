from pathlib import Path
import hashlib, importlib.util, json, math, subprocess, sys
from datetime import datetime, timezone

b=Path('/home/admin-wsl/Coq/abc/prove2me_workspace/.local/adaptation/local-compactness-sourceproof-20261114')
spec=importlib.util.spec_from_file_location('unit',b/'delivery.py');unit=importlib.util.module_from_spec(spec);spec.loader.exec_module(unit)
r,w,read,save,sha=unit.r,unit.w,unit.read,unit.save,unit.sha
sys.path.insert(0,str(w/'.local/adaptation/northcott-sourceproof-20261114'))
from delivery_common import graph_summary

def main():
    unit.preflight();before,after=graph_summary(read('root-graph-before.json')),graph_summary(read('root-graph-after.json'))
    assert set(before['mathematical'])==set(after['mathematical'])
    old={z['theorem_name']:z for z in before['mathematical'].values()};now={z['theorem_name']:z for z in after['mathematical'].values()}
    assert set(old)==set(now) and old[unit.target]['status']=='Open' and now[unit.target]['status']=='Proved'
    assert all(old[n]['status']==now[n]['status'] for n in old if n!=unit.target)
    assert now['abc.goal.lt_constant_mul_fix']['status']=='Open'
    canonical=lambda es:sorted(es,key=lambda z:z['submission_id'])
    assert canonical(before['reductions'])==canonical(after['reductions']) and before['dependency_pairs']==after['dependency_pairs'] and before['counts']==after['counts']
    result=read('prove-localCompactness-verify-result.json');req=read('prove-localCompactness-verify-request.json');submitted=read('prove-localCompactness-verify-submit.json');ident=read('target-id.json')['id']
    assert result['status']=='ACCEPTED' and result['id']==submitted['submission_id'] and result['theorem_id']==ident
    assert req['source_sha256']==sha(w/unit.sol) and (b/'prove-localCompactness-solution.lean').read_bytes()==(w/unit.sol).read_bytes()
    state=read('platform-after-parent.json');assert state['formal_statement']==read('platform-before-parent.json')['formal_statement'] and state['status']=='Proved' and state['visibility']=='private' and state['mathlib_rev']==unit.ENV
    assert all(state[k]==v for k,v in read('parent-metadata-patch-request.json').items())
    bf,af=read('root-frontier-before.json'),read('root-frontier-after.json')
    for f in [bf,af]:assert f['all_pages_fetched'] and len(f['open_leaves'])==f['total']==len({z['theorem_id'] for z in f['open_leaves']})
    expected={z['theorem_name'] for z in bf['open_leaves']}-{unit.target};assert {z['theorem_name'] for z in af['open_leaves']}==expected
    rp=w/'.local/adaptation/platform-node-registry.json';reg=json.loads(rp.read_text());assert reg==read('registry-before.json'),'Registry changed concurrently'
    direct={z['name']:z for z in reg['direct_closed_proofs']};assert unit.target not in direct
    proof={'name':unit.target,'submission_id':result['id'],'status':'ACCEPTED'};direct[unit.target]=proof;assert all(now[n]['status']=='Proved' for n in direct)
    counts=after['counts']|{'open_frontier':af['total'],'direct_closed_children':len(direct)}
    reg.update(direct_closed_proofs=sorted(direct.values(),key=lambda z:z['name']),graph_counts=counts,open_frontier=sorted(expected),local_open_children_below_root=af['total'],published_open_children_below_root=af['total'],platform_statuses={n:z['status'] for n,z in now.items()},mathematical_root_proved=False,recorded_at=datetime.now(timezone.utc).isoformat())
    reg['local_compactness_sourceproof_unit']={'source':str(b.relative_to(w)),'closed_direct':proof,'new_nodes':[],'new_dependencies':[],'new_open_debt':0,'original_type_preserved':True,'Fermat_route_preserved':True,'deprecations':[]}
    source=read('source-consumer.json');source['status']='exclusive_local_audits_passed_and_platform_ACCEPTED';source['compiled']=True;source['platform_status']='Proved';source['closed_direct']=proof;save('source-consumer.json',source)
    save('graph-count-evidence.json',{'before':before['counts']|{'open_frontier':bf['total']},'after':counts,'mathematical_node_ids_unchanged':True,'reductions_and_dependencies_unchanged':True,'new_nodes':[],'closed_direct':proof,'root':'Open','deprecations':[]})
    records=[];seen=set()
    for p in b.rglob('*-result.json'):
        z=json.loads(p.read_text())
        if not all(k in z for k in ['job_id','request','result','resources']) or z['job_id'] in seen:continue
        seen.add(z['job_id']);q,rs,v=z['request'],z['result'],z['resources']
        assert q['exclusive'] and q['workspace']==str(w) and rs['snapshot']['workspace_mode']=='exclusive_worktree' and rs['snapshot']['snapshot_id'] is None
        cpu,user,system=[v.get(k) for k in ['cpu_time_seconds','cpu_user_seconds','cpu_system_seconds']]
        if None not in [cpu,user,system]:assert math.isclose(cpu,user+system,abs_tol=.1)
        if v.get('peak_rss_bytes') is not None:assert v['peak_rss_bytes']<=16*1024**3
        records.append({'job_id':z['job_id'],'status':z['status'],'receipt':str(p.relative_to(w)),'source_sha256':q['worktree_manifest']['source_sha256'],'input_head':q['worktree_manifest']['head'],'actual_arguments':rs['actual_arguments'],'exit_code':rs['exit_code'],'diagnostics':rs.get('diagnostics'),**{k:v.get(k) for k in ['wall_time_seconds','cpu_time_seconds','cpu_user_seconds','cpu_system_seconds','peak_rss_bytes','peak_pss_bytes']},'resource_source':v.get('source'),'degraded':v.get('degraded')})
    save('unit-ci-summary.json',{'records':records,'succeeded':sum(z['status']=='succeeded' for z in records),'failed_or_other_terminal':sum(z['status']!='succeeded' for z in records),'peak_rss_bytes':max(z['peak_rss_bytes'] for z in records if z['peak_rss_bytes'] is not None),'missing_resources':'unknown, not zero','closed_direct':proof,'root':'Open'})
    own=read('delivery-validation.json')['owned_source_hashes'];save('integration.json',{'input_head':read('git-input-state.json')['head'],'owned_sources':own,'status':'Exact original localCompactness Proved by the bounded-degree all-embeddings compactness source chain','closed_direct':proof,'source_ledger':'source-consumer.json','graph_counts':counts,'new_nodes':[],'new_open_debt':0,'Fermat_route_preserved':True,'deprecations':[]})
    doc=r/'docs/Prove2Me适配状态.md';assert doc.read_text()==(b/'pending-db-before.md').read_text(),'Pending database changed concurrently';text=(b/'pending-db-after.md').read_text()
    assert 'Proper.planeAdjunctionExists' in text and 'Proper.canonicalHeightIdentification' in text
    removed='- `Heights@721496ca4c158e511d25d8ccf6bfe8503eda73c1/Heights/Curve/Compactness.lean:233`\n'
    assert text==(b/'pending-db-before.md').read_text().replace(removed,'')
    unit.save('pending-db-scope.json',{'removed_only':removed.strip(),'reason':'The complete exact source compactness obligation and its trilingual readbacks are delivered','broader_descent_and_height_sources_remain':True})
    files=sorted({str((w/f).relative_to(r)) for f in own}|{str(doc.relative_to(r)),str(rp.relative_to(r))}|{str(p.relative_to(r)) for p in b.rglob('*') if p.is_file() and '__pycache__' not in p.parts})
    for f in files:
        p=r/f
        if p!=rp:reg['files'][f]=hashlib.sha256(text.encode()).hexdigest() if p==doc else sha(p)
    reg['files']=dict(sorted(reg['files'].items()));assert not subprocess.check_output(['git','diff','--cached','--name-only'],cwd=r).strip(),'Preserve unrelated staged files'
    credentials=json.loads((w/'credentials.json').read_text());secrets=[v.encode() for k,v in credentials.items() if k in ['api_key','access_token','refresh_token','token'] and isinstance(v,str) and len(v)>15]
    for f in files:
        p=r/f;data=text.encode() if p==doc else json.dumps(reg,ensure_ascii=False).encode() if p==rp else p.read_bytes()
        assert p.name!='credentials.json' and not any(s in data for s in secrets) and (b'p2m_'+b'eyJ') not in data,f
        assert all(line.rstrip(b' \t')==line for line in data.splitlines()),f
        if p.suffix in ['.lean','.md','.py']:assert not data.endswith(b'\n\n'),f
    doc.write_text(text);rp.write_text(json.dumps(reg,ensure_ascii=False,indent=2)+'\n')
    subprocess.run(['git','diff','--check'],cwd=r,check=True);subprocess.run(['git','add','-f','--']+files,cwd=r,check=True);subprocess.run(['git','diff','--cached','--check'],cwd=r,check=True)
    staged=subprocess.check_output(['git','diff','--cached','--name-only','-z'],cwd=r).split(b'\0')
    print(json.dumps({'staged_files':len([f for f in staged if f]),'audited_allowlist':len(files),'graph_counts':counts,'target':'Proved','root':'Open','new_nodes':[]}),flush=True)
if __name__=='__main__':main()
