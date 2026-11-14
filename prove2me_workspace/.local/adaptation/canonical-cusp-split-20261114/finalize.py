from pathlib import Path
import hashlib, importlib.util, json, math, subprocess, sys
from datetime import datetime, timezone

b=Path('/home/admin-wsl/Coq/abc/prove2me_workspace/.local/adaptation/canonical-cusp-split-20261114')
spec=importlib.util.spec_from_file_location('unit',b/'delivery.py');unit=importlib.util.module_from_spec(spec);spec.loader.exec_module(unit)
r,w,read,save,sha=unit.r,unit.w,unit.read,unit.save,unit.sha
sys.path.insert(0,str(w/'.local/adaptation/northcott-sourceproof-20261114'))
from delivery_common import graph_summary

def main():
    unit.preflight();before,after=graph_summary(read('root-graph-before.json')),graph_summary(read('root-graph-after.json'))
    old={z['theorem_name']:z for z in before['mathematical'].values()};now={z['theorem_name']:z for z in after['mathematical'].values()}
    ids=read('published-child-ids.json');assert set(ids)==set(unit.children) and set(now)==set(old)|set(ids)
    assert before['dependency_pairs']<=after['dependency_pairs'] and len(after['dependency_pairs']-before['dependency_pairs'])==2
    previous={z['submission_id']:z for z in before['reductions']};current={z['submission_id']:z for z in after['reductions']}
    assert all(current[k]==v for k,v in previous.items()) and len(current)==len(previous)+1
    new=[z for z in after['reductions'] if z['submission_id'] not in previous];assert len(new)==1
    result=read('reduce-parent-verify-result.json');submitted=read('reduce-parent-verify-submit.json');request=read('reduce-parent-verify-request.json')
    assert result['status']=='SKETCH_ACCEPTED' and result['id']==submitted['submission_id'] and result['theorem_id']==read('target-id.json')['id']
    assert new[0]['parent']==unit.parent and set(new[0]['children'])==set(ids) and new[0]['submission_id']==result['id']
    assert request['source_sha256']==sha(w/unit.sol) and (b/'reduce-parent-solution.lean').read_bytes()==(w/unit.sol).read_bytes()
    assert all(now[n]['status']==old[n]['status'] for n in old)
    assert all(now[n]['status']=='Open' for n in unit.children+[unit.parent,'abc.goal.lt_constant_mul_fix'])
    assert read('platform-before-parent.json')['formal_statement']==read('platform-after-parent.json')['formal_statement']
    assert all(read('platform-after-parent.json')[k]==v for k,v in read('parent-metadata-patch-request.json').items())
    for item in read('canonical-cusp-children-payload.json')['problems']:
        state=read('platform-after-'+item['theorem_name'].removeprefix(unit.pre)+'.json')
        assert state['formal_statement']==item['formal_statement'] and state['preamble']==item['preamble']
        assert state['status']=='Open' and state['visibility']=='private' and state['mathlib_rev']==unit.ENV
        assert not state.get('deprecated',False)
    bf,af=read('root-frontier-before.json'),read('root-frontier-after.json')
    for f in [bf,af]:assert f['all_pages_fetched'] and len(f['open_leaves'])==f['total']==len({z['theorem_id'] for z in f['open_leaves']})
    expected={z['theorem_name'] for z in bf['open_leaves']}-{unit.parent}|set(unit.children)
    assert {z['theorem_name'] for z in af['open_leaves']}==expected
    assert read('direct-graph-evidence.json')['both_children_open'] and af['total']==bf['total']+1
    rp=w/'.local/adaptation/platform-node-registry.json';reg=json.loads(rp.read_text());assert reg==read('registry-before.json'),'Registry changed concurrently'
    assert all(now[z['name']]['status']=='Proved' for z in reg['direct_closed_proofs'])
    counts=after['counts']|{'open_frontier':af['total'],'direct_closed_children':len(reg['direct_closed_proofs'])}
    reg.update(edges=sorted(after['reductions'],key=lambda z:(z['parent'],z['submission_id'])),published_nodes=sorted([{'name':z['theorem_name'],'id':tid} for tid,z in after['mathematical'].items() if tid!=unit.ROOT],key=lambda z:z['name']),graph_counts=counts,open_frontier=sorted(expected),local_open_children_below_root=af['total'],published_open_children_below_root=af['total'],accepted_platform_reductions=counts['accepted_reductions'],dependency_edges=counts['dependency_edges'],mathematical_root_proved=False,recorded_at=datetime.now(timezone.utc).isoformat(),platform_statuses={n:z['status'] for n,z in now.items()})
    reg['canonical_cusp_split_unit']={'source':str(b.relative_to(w)),'parent':unit.parent,'exact_parent_type_preserved':True,'children':ids,'both_children_open':True,'submission_id':result['id'],'explicit_Fermat_route_preserved':True,'new_definitions':[],'deprecations':[]}
    provenance=read('source-consumer.json');provenance['status']='exclusive_local_checks_passed_and_exact_two_child_SKETCH_ACCEPTED';provenance['platform_submission']=result['id'];provenance['parent_status']='Open';provenance['platform_children']=ids
    provenance['current_proof_debt_scope']='Both exact child statements remain Open. Draft missing-proof lists describe their assembly/porting debt; already available infrastructure is identified in independent-source-review.json and should be reused.'
    save('source-consumer.json',provenance)
    save('graph-count-evidence.json',{'before':before['counts']|{'open_frontier':bf['total']},'after':counts,'new_mathematical_nodes':ids,'actual_new_reduction':new[0],'existing_nodes_and_reductions_preserved':True,'new_dependency_pairs':sorted(after['dependency_pairs']-before['dependency_pairs']),'root':'Open','deprecations':[]})
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
    save('unit-ci-summary.json',{'records':records,'succeeded':sum(z['status']=='succeeded' for z in records),'failed_or_other_terminal':sum(z['status']!='succeeded' for z in records),'peak_rss_bytes':max(z['peak_rss_bytes'] for z in records if z['peak_rss_bytes'] is not None),'missing_resources':'unknown, not zero','parent_status':'Open','both_children_open':True,'root':'Open'})
    own=read('delivery-validation.json')['owned_source_hashes'];save('integration.json',{'input_head':read('git-input-state.json')['head'],'status':'Exact two-child canonical-cusp reduction accepted; both mathematical children remain Open','owned_sources':own,'source_ledger':'source-consumer.json','graph_counts':counts,'original_parent_type_preserved':True,'Fermat_route_preserved':True,'deprecations':[]})
    doc=r/'docs/Prove2Me适配状态.md';assert doc.read_text()==(b/'pending-db-before.md').read_text(),'Pending database changed concurrently'
    text=(b/'pending-db-after.md').read_text()
    scope=read('pending-db-refinement-plan.json');oldtext=doc.read_text();expected=oldtext
    for line in scope['removed']:
        assert expected.count(line+'\n')==1;expected=expected.replace(line+'\n','')
    marker='\n## 2. Joshi 论文直接列出而尚未拆分的证明义务'
    expected=expected.replace(marker,'\n'+''.join(line+'\n' for line in scope['added'])+marker)
    assert text==expected and 'Proper.planeAdjunctionExists' in text and 'Proper.canonicalHeightIdentification' in text
    save('pending-db-scope.json',{'removed_completed_source_mappings':scope['removed'],'added_unexpanded_child_source_locations':scope['added'],'other_sections_unchanged':oldtext.split('## 2.',1)[1]==text.split('## 2.',1)[1],'two_child_proofs_remain_open':True})
    files=sorted({str((w/f).relative_to(r)) for f in own}|{str(doc.relative_to(r)),str(rp.relative_to(r))}|{str(p.relative_to(r)) for p in b.rglob('*') if p.is_file() and '__pycache__' not in p.parts})
    for f in files:
        if f!=str(rp.relative_to(r)):reg['files'][f]=hashlib.sha256(text.encode()).hexdigest() if f==str(doc.relative_to(r)) else sha(r/f)
    reg['files']=dict(sorted(reg['files'].items()));assert not subprocess.check_output(['git','diff','--cached','--name-only'],cwd=r).strip(),'Preserve unrelated staged work'
    credentials=json.loads((w/'credentials.json').read_text());secrets=[v.encode() for k,v in credentials.items() if k in ['api_key','access_token','refresh_token','token'] and isinstance(v,str) and len(v)>15]
    for f in files:
        p=r/f;data=text.encode() if p==doc else json.dumps(reg,ensure_ascii=False).encode() if p==rp else p.read_bytes()
        assert p.name!='credentials.json' and not any(s in data for s in secrets) and (b'p2m_'+b'eyJ') not in data,f
        assert all(line.rstrip(b' \t')==line for line in data.splitlines()),f
        if p.suffix in ['.lean','.md','.py']:assert not data.endswith(b'\n\n'),f
    doc.write_text(text);rp.write_text(json.dumps(reg,ensure_ascii=False,indent=2)+'\n')
    subprocess.run(['git','diff','--check'],cwd=r,check=True);subprocess.run(['git','add','-f','--']+files,cwd=r,check=True);subprocess.run(['git','diff','--cached','--check'],cwd=r,check=True)
    print(json.dumps({'staged_files':len(files),'graph_counts':counts,'both_children_open':True,'root':'Open','deprecations':[]}),flush=True)
if __name__=='__main__':main()
