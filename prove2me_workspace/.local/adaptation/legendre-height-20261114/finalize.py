from pathlib import Path
import hashlib, importlib.util, json, math, subprocess, sys
from datetime import datetime, timezone

b=Path('/home/admin-wsl/Coq/abc/prove2me_workspace/.local/adaptation/legendre-height-20261114')
spec=importlib.util.spec_from_file_location('unit',b/'delivery.py');unit=importlib.util.module_from_spec(spec);spec.loader.exec_module(unit)
r,w,read,save,sha=unit.r,unit.w,unit.read,unit.save,unit.sha
sys.path.insert(0,str(w/'.local/adaptation/northcott-sourceproof-20261114'))
from delivery_common import graph_summary

def main():
    unit.preflight()
    before,after=graph_summary(read('root-graph-before.json')),graph_summary(read('root-graph-after.json'))
    old={z['theorem_name']:z for z in before['mathematical'].values()};now={z['theorem_name']:z for z in after['mathematical'].values()}
    ids=read('published-child-ids.json');assert set(now)==set(old)|set(ids)
    assert before['dependency_pairs']<=after['dependency_pairs'] and len(after['dependency_pairs']-before['dependency_pairs'])==4
    olds={z['submission_id']:z for z in before['reductions']};news={z['submission_id']:z for z in after['reductions']}
    assert all(news[k]==v for k,v in olds.items()) and len(news)==len(olds)+1
    parent=unit.pre+'canonicalLegendreHeightComparison';newedges=[z for z in after['reductions'] if z['submission_id'] not in olds]
    assert len(newedges)==1 and newedges[0]['parent']==parent and set(newedges[0]['children'])==set(ids)
    assert newedges[0]['submission_id']==read('reduce-parent-verify-result.json')['id']
    assert all(now[n]['status']==old[n]['status'] for n in old)
    assert all(now[unit.pre+n]['status']==('Proved' if n in unit.closed else 'Open') for n in unit.children)
    assert now[parent]['status']=='Open' and now['abc.goal.lt_constant_mul_fix']['status']=='Open'
    bf,af=read('root-frontier-before.json'),read('root-frontier-after.json')
    for frontier in [bf,af]:assert frontier['all_pages_fetched'] and len(frontier['open_leaves'])==frontier['total']==len({z['theorem_id'] for z in frontier['open_leaves']})
    expected={z['theorem_name'] for z in bf['open_leaves']}-{parent}|{unit.pre+n for n in unit.children[:2]}
    assert {z['theorem_name'] for z in af['open_leaves']}==expected
    for n in unit.closed:
        req=read('prove-'+n+'-verify-request.json');result=read('prove-'+n+'-verify-result.json');submission=read('prove-'+n+'-verify-submit.json')
        assert result['status']=='ACCEPTED' and result['id']==submission['submission_id'] and result['theorem_id']==ids[unit.pre+n]
        archive=b/('prove-'+n+'-submitted-source.json')
        raw=json.loads(archive.read_text())['source_text'].encode() if archive.exists() else (b/('prove-'+n+'-solution.lean')).read_bytes()
        assert req['source_sha256']==hashlib.sha256(raw).hexdigest()
        assert raw==(w/req['file']).read_bytes() or raw.rstrip()+b'\n'==(w/req['file']).read_bytes()
    assert read('platform-before-parent.json')['formal_statement']==read('platform-after-parent.json')['formal_statement']
    assert read('direct-graph-evidence.json')['two_proved_two_open']
    registry=w/'.local/adaptation/platform-node-registry.json';current=json.loads(registry.read_text());baseline=read('registry-before.json')
    if current!=baseline:
        assert current['legendre_height_unit']['submission_id']==read('reduce-parent-verify-result.json')['id']
        changed={'edges','published_nodes','direct_closed_proofs','graph_counts','open_frontier','local_open_children_below_root','published_open_children_below_root','accepted_platform_reductions','dependency_edges','mathematical_root_proved','recorded_at','platform_statuses','files'}
        assert all(current[k]==v for k,v in baseline.items() if k not in changed),'Reconcile unrelated registry changes before finalization'
    reg=json.loads(json.dumps(baseline))
    closed=[{'name':unit.pre+n,'submission_id':read('prove-'+n+'-verify-result.json')['id'],'status':'ACCEPTED'} for n in unit.closed]
    provenance=read('source-consumer.json');provenance['status']='exclusive_local_audits_passed_and_platform_reduction_accepted'
    for child in provenance['children']:
        if child['declaration'] in {z['name'] for z in closed}:
            child['proof_status']='source_proof_locally_audited_and_platform_Proved'
            child['platform_proof']=next(z for z in closed if z['name']==child['declaration'])
    save('source-consumer.json',provenance)
    prior={z['name']:z for z in baseline['direct_closed_proofs']};assert not(set(prior)&{z['name'] for z in closed})
    direct=prior|{z['name']:z for z in closed};assert all(now[n]['status']=='Proved' for n in direct)
    counts=after['counts']|{'open_frontier':af['total'],'direct_closed_children':len(direct)}
    reg.update(edges=sorted(after['reductions'],key=lambda z:(z['parent'],z['submission_id'])),published_nodes=sorted([{'name':z['theorem_name'],'id':ident} for ident,z in after['mathematical'].items() if ident!=unit.ROOT],key=lambda z:z['name']),direct_closed_proofs=sorted(direct.values(),key=lambda z:z['name']),graph_counts=counts,open_frontier=sorted(expected),local_open_children_below_root=af['total'],published_open_children_below_root=af['total'],accepted_platform_reductions=counts['accepted_reductions'],dependency_edges=counts['dependency_edges'],mathematical_root_proved=False,recorded_at=datetime.now(timezone.utc).isoformat())
    reg['platform_statuses']={n:z['status'] for n,z in now.items()}
    reg['legendre_height_unit']={'source':str(b.relative_to(w)),'parent':parent,'exact_type_preserved':True,'children':ids,'closed_direct':closed,'remaining_open':[unit.pre+n for n in unit.children[:2]],'submission_id':read('reduce-parent-verify-result.json')['id'],'explicit_fermat_route_preserved':True,'deprecated_nodes':[]}
    save('graph-count-evidence.json',{'before':before['counts']|{'open_frontier':bf['total']},'after':counts,'new_mathematical_nodes':ids,'actual_new_reduction':newedges[0],'existing_nodes_and_reductions_preserved':True,'new_dependency_pairs':sorted(after['dependency_pairs']-before['dependency_pairs']),'deprecations':[]})
    records=[];seen=set()
    for p in b.rglob('*-result.json'):
        z=json.loads(p.read_text())
        if not all(k in z for k in ['job_id','request','result','resources']) or z['job_id'] in seen:continue
        seen.add(z['job_id']);q,rs,v=z['request'],z['result'],z['resources']
        assert q['exclusive'] and q['workspace']==str(w) and rs['snapshot']['workspace_mode']=='exclusive_worktree' and rs['snapshot']['snapshot_id'] is None
        assert z['status']=='succeeded' and rs['exit_code']==0
        cpu,user,system=[v.get(k) for k in ['cpu_time_seconds','cpu_user_seconds','cpu_system_seconds']]
        if None not in [cpu,user,system]:assert math.isclose(cpu,user+system,abs_tol=.1)
        if v.get('peak_rss_bytes') is not None:assert v['peak_rss_bytes']<=16*1024**3
        records.append({'job_id':z['job_id'],'status':z['status'],'receipt':str(p.relative_to(w)),'source_sha256':q['worktree_manifest']['source_sha256'],'input_head':q['worktree_manifest']['head'],'actual_arguments':rs['actual_arguments'],'exit_code':rs['exit_code'],'diagnostics':rs.get('diagnostics'),**{k:v.get(k) for k in ['wall_time_seconds','cpu_time_seconds','cpu_user_seconds','cpu_system_seconds','peak_rss_bytes','peak_pss_bytes']},'resource_source':v.get('source'),'degraded':v.get('degraded')})
    save('unit-ci-summary.json',{'records':records,'succeeded':len(records),'failed_or_other_terminal':0,'peak_rss_bytes':max(z['peak_rss_bytes'] for z in records if z['peak_rss_bytes'] is not None),'missing_resource_values':'unknown, not zero','parent_status':'Open','two_proved_two_open':True,'root_proved':False})
    own=read('delivery-validation.json')['owned_source_hashes']
    own.update({f:sha(w/f) for f in ['Solutions/Checks_TripodLegendreHeightClosed.lean','Solutions/Checks_TripodLegendreHeightReduction.lean']})
    save('integration.json',{'input_head':(b/'input-head.txt').read_text().strip(),'status':'Exact four-child decomposition accepted; two source proofs accepted; two finite source ports remain Open','owned_sources':own,'source_ledger':'source-consumer.json','closed_direct':closed,'graph_counts':counts,'original_parent_type_unchanged':True,'Fermat_route_preserved':True,'deprecations':[]})
    document=r/'docs/Prove2Me适配状态.md';assert document.read_text() in [(b/'pending-db-before.md').read_text(),(b/'pending-db-after.md').read_text()],'Pending database changed concurrently'
    updated=(b/'pending-db-after.md').read_text()
    assert 'Proper.coordinatePoleMultiplicity_eq' in updated and 'Fermat.heightNormalization' in updated
    assert '- `refer/iut/Iut/Tripod/Height.lean:791`' not in updated
    assert all('- `refer/iut/Iut/Tripod/Height.lean:'+str(n)+'`' in updated for n in [714,743])
    files=sorted({str((w/f).relative_to(r)) for f in own}|{'docs/Prove2Me适配状态.md',str(registry.relative_to(r))}|{str(p.relative_to(r)) for p in b.rglob('*') if p.is_file() and '__pycache__' not in p.parts})
    for f in files:
        p=r/f
        if p!=registry:reg['files'][f]=hashlib.sha256(updated.encode()).hexdigest() if p==document else sha(p)
    reg['files']=dict(sorted(reg['files'].items()))
    staged=set(subprocess.check_output(['git','-c','core.quotePath=false','diff','--cached','--name-only'],cwd=r,text=True).splitlines())
    assert staged<=set(files),'Preserve unrelated staged work'
    credentials=json.loads((w/'credentials.json').read_text());secrets=[v.encode() for k,v in credentials.items() if k in ['api_key','access_token','refresh_token','token'] and isinstance(v,str) and len(v)>15]
    for f in files:
        p=r/f;data=updated.encode() if p==document else json.dumps(reg,ensure_ascii=False).encode() if p==registry else p.read_bytes()
        assert p.name!='credentials.json' and not any(s in data for s in secrets) and (b'p2m_'+b'eyJ') not in data,f
    document.write_text(updated);registry.write_text(json.dumps(reg,ensure_ascii=False,indent=2)+'\n')
    subprocess.run(['git','diff','--check'],cwd=r,check=True)
    subprocess.run(['git','add','-f','--']+files,cwd=r,check=True)
    subprocess.run(['git','diff','--cached','--check'],cwd=r,check=True)
    print(json.dumps({'staged_files':len(files),'graph_counts':counts,'all_local_jobs_succeeded':len(records),'root':'Open','deprecations':[]}),flush=True)
if __name__=='__main__':main()
