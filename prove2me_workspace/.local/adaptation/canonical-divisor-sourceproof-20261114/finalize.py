from pathlib import Path
import hashlib, importlib.util, json, math, subprocess, sys
from datetime import datetime, timezone

b=Path('/home/admin-wsl/Coq/abc/prove2me_workspace/.local/adaptation/canonical-divisor-sourceproof-20261114')
spec=importlib.util.spec_from_file_location('unit',b/'delivery.py');unit=importlib.util.module_from_spec(spec);spec.loader.exec_module(unit)
r,w,read,save,sha=unit.r,unit.w,unit.read,unit.save,unit.sha
sys.path.insert(0,str(w/'.local/adaptation/northcott-sourceproof-20261114'))
from delivery_common import graph_summary

def main():
    unit.preflight()
    before,after=graph_summary(read('root-graph-before.json')),graph_summary(read('root-graph-after.json'))
    assert set(before['mathematical'])==set(after['mathematical']),'Theorem identities must be retained'
    old={z['theorem_name']:z for z in before['mathematical'].values()};now={z['theorem_name']:z for z in after['mathematical'].values()}
    assert set(now)==set(old),'No new theorem node is authorized for this source-reuse unit'
    assert old[unit.target]['status']=='Open' and now[unit.target]['status']=='Proved'
    assert all(old[n]['status']==now[n]['status'] for n in old if n!=unit.target)
    assert now[unit.dependency]['status']=='Proved' and now['abc.goal.lt_constant_mul_fix']['status']=='Open'
    prior={z['submission_id']:z for z in before['reductions']};current={z['submission_id']:z for z in after['reductions']}
    assert all(current[k]==v for k,v in prior.items()),'Existing reductions must be retained'
    result=read('prove-canonicalDivisorExists-verify-result.json');submitted=read('prove-canonicalDivisorExists-verify-submit.json');req=read('prove-canonicalDivisorExists-verify-request.json')
    ident=read('target-id.json')['id'];assert result['status']=='ACCEPTED' and result['id']==submitted['submission_id'] and result['theorem_id']==ident
    assert req['source_sha256']==sha(w/unit.sol) and (b/'prove-canonicalDivisorExists-solution.lean').read_bytes()==(w/unit.sol).read_bytes()
    assert set(current)-set(prior)=={result['id']}
    edge=current[result['id']];assert edge['parent']==unit.target and edge['children']==[unit.dependency] and edge['status']=='ACCEPTED'
    assert before['dependency_pairs']<=after['dependency_pairs'] and after['dependency_pairs']-before['dependency_pairs']=={(unit.target,unit.dependency)}
    before_target,after_target=read('platform-before-parent.json'),read('platform-after-parent.json')
    assert before_target['formal_statement']==after_target['formal_statement'] and after_target['status']=='Proved'
    assert after_target['visibility']=='private' and after_target['mathlib_rev']==unit.ENV
    assert all(after_target[k]==v for k,v in read('parent-metadata-patch-request.json').items())
    bf,af=read('root-frontier-before.json'),read('root-frontier-after.json')
    for f in [bf,af]:assert f['all_pages_fetched'] and len(f['open_leaves'])==f['total']==len({z['theorem_id'] for z in f['open_leaves']})
    expected={z['theorem_name'] for z in bf['open_leaves']}-{unit.target}
    assert {z['theorem_name'] for z in af['open_leaves']}==expected
    registry_path=w/'.local/adaptation/platform-node-registry.json';registry=json.loads(registry_path.read_text());baseline=read('registry-before.json');assert registry==baseline,'Registry changed concurrently'
    assert all(now[z['name']]['status']=='Proved' for z in registry['direct_closed_proofs'])
    counts=after['counts']|{'open_frontier':af['total'],'direct_closed_children':len(registry['direct_closed_proofs'])}
    proof={'name':unit.target,'submission_id':result['id'],'status':'ACCEPTED','existing_proved_dependency':unit.dependency}
    registry.update(edges=sorted(after['reductions'],key=lambda z:(z['parent'],z['submission_id'])),graph_counts=counts,accepted_platform_reductions=counts['accepted_reductions'],dependency_edges=counts['dependency_edges'],open_frontier=sorted(expected),local_open_children_below_root=af['total'],published_open_children_below_root=af['total'],platform_statuses={n:z['status'] for n,z in now.items()},mathematical_root_proved=False,recorded_at=datetime.now(timezone.utc).isoformat())
    registry['canonical_divisor_sourceproof_unit']={'source':str(b.relative_to(w)),'closed_proof':proof,'new_nodes':[],'new_open_debt':0,'actual_new_edge':edge,'all_proper_places_preserved':True,'Fermat_route_preserved':True,'deprecations':[]}
    source=read('source-consumer.json');source['status']='exclusive_local_audits_passed_and_platform_ACCEPTED';source['closed_proof']=proof;save('source-consumer.json',source)
    save('graph-count-evidence.json',{'before':before['counts']|{'open_frontier':bf['total']},'after':counts,'new_nodes':[],'mathematical_node_set_unchanged':True,'existing_reductions_preserved':True,'added_dependency':[unit.target,unit.dependency],'closed_proof':proof,'root':'Open','deprecations':[]})
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
    save('unit-ci-summary.json',{'records':records,'succeeded':sum(z['status']=='succeeded' for z in records),'failed_or_other_terminal':sum(z['status']!='succeeded' for z in records),'peak_rss_bytes':max(z['peak_rss_bytes'] for z in records if z['peak_rss_bytes'] is not None),'missing_resource_values':'unknown, not zero','closed_proof':proof,'root':'Open'})
    own=read('delivery-validation.json')['owned_source_hashes']
    save('integration.json',{'input_head':read('git-input-state.json')['head'],'status':'Original canonicalDivisorExists Proved using its actual finite-support construction and the existing generic finite-ramification proof','owned_sources':own,'source_ledger':'source-consumer.json','closed_proof':proof,'graph_counts':counts,'original_target_type_preserved':True,'new_nodes':[],'new_open_debt':0,'Fermat_route_preserved':True,'deprecations':[]})
    document=r/'docs/Prove2Me适配状态.md';assert document.read_text()==(b/'pending-db-before.md').read_text(),'Pending database changed concurrently'
    updated=(b/'pending-db-after.md').read_text();assert 'Proper.planeAdjunctionExists' in updated and 'Proper.canonicalHeightIdentification' in updated
    assert '- `Belyi@9ce4d3f793d3bc831f2fc7214b7dbad90ea012d8/Belyi/CurveField/Canonical.lean:44`' not in updated
    files=sorted({str((w/f).relative_to(r)) for f in own}|{'docs/Prove2Me适配状态.md',str(registry_path.relative_to(r))}|{str(p.relative_to(r)) for p in b.rglob('*') if p.is_file() and '__pycache__' not in p.parts})
    for f in files:
        p=r/f
        if p!=registry_path:registry['files'][f]=hashlib.sha256(updated.encode()).hexdigest() if p==document else sha(p)
    registry['files']=dict(sorted(registry['files'].items()))
    assert not subprocess.check_output(['git','diff','--cached','--name-only'],cwd=r).strip(),'Preserve unrelated staged work'
    credentials=json.loads((w/'credentials.json').read_text());secrets=[v.encode() for k,v in credentials.items() if k in ['api_key','access_token','refresh_token','token'] and isinstance(v,str) and len(v)>15]
    for f in files:
        p=r/f;data=updated.encode() if p==document else json.dumps(registry,ensure_ascii=False).encode() if p==registry_path else p.read_bytes()
        assert p.name!='credentials.json' and not any(s in data for s in secrets) and (b'p2m_'+b'eyJ') not in data,f
        assert all(line.rstrip(b' \t')==line for line in data.splitlines()),f
        if p.suffix in ['.lean','.md','.py']:assert not data.endswith(b'\n\n'),f
    document.write_text(updated);registry_path.write_text(json.dumps(registry,ensure_ascii=False,indent=2)+'\n')
    subprocess.run(['git','diff','--check'],cwd=r,check=True);subprocess.run(['git','add','-f','--']+files,cwd=r,check=True);subprocess.run(['git','diff','--cached','--check'],cwd=r,check=True)
    print(json.dumps({'staged_files':len(files),'graph_counts':counts,'target':'Proved','root':'Open','new_nodes':[]}),flush=True)
if __name__=='__main__':main()
