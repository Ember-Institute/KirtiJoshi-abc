from pathlib import Path
import hashlib, importlib.util, json, math, subprocess, sys
from datetime import datetime, timezone

b=Path('/home/admin-wsl/Coq/abc/prove2me_workspace/.local/adaptation/legendre-finite-sourceproof-20261114')
spec=importlib.util.spec_from_file_location('unit',b/'delivery.py');unit=importlib.util.module_from_spec(spec);spec.loader.exec_module(unit)
r,w,read,save,sha=unit.r,unit.w,unit.read,unit.save,unit.sha
sys.path.insert(0,str(w/'.local/adaptation/northcott-sourceproof-20261114'))
from delivery_common import graph_summary

def main():
    unit.preflight()
    before,after=graph_summary(read('root-graph-before.json')),graph_summary(read('root-graph-after.json'))
    old={z['theorem_name']:z for z in before['mathematical'].values()};now={z['theorem_name']:z for z in after['mathematical'].values()}
    assert set(now)==set(old) and before['dependency_pairs']==after['dependency_pairs'] and before['counts']==after['counts']
    ident=lambda z:(z['parent'],tuple(z['children']),z['submission_id'])
    assert sorted(map(ident,before['reductions']))==sorted(map(ident,after['reductions']))
    changed={unit.pre+n for n in unit.targets}|{unit.parent}
    assert all(now[n]['status']=='Proved' and old[n]['status']=='Open' for n in changed)
    assert all(now[n]['status']==old[n]['status'] for n in old if n not in changed)
    assert now['abc.goal.lt_constant_mul_fix']['status']=='Open'
    bf,af=read('root-frontier-before.json'),read('root-frontier-after.json')
    for f in [bf,af]:assert f['all_pages_fetched'] and len(f['open_leaves'])==f['total']==len({z['theorem_id'] for z in f['open_leaves']})
    expected={z['theorem_name'] for z in bf['open_leaves']}-{unit.pre+n for n in unit.targets}
    assert {z['theorem_name'] for z in af['open_leaves']}==expected
    ids=read('target-ids.json');proofs=[]
    for n in unit.targets:
        result=read('prove-'+n+'-verify-result.json');request=read('prove-'+n+'-verify-request.json');submitted=read('prove-'+n+'-verify-submit.json')
        assert result['status']=='ACCEPTED' and result['id']==submitted['submission_id'] and result['theorem_id']==ids[unit.pre+n]
        assert request['source_sha256']==sha(w/request['file'])
        assert (b/('prove-'+n+'-solution.lean')).read_bytes()==(w/request['file']).read_bytes()
        a=read('platform-after-'+n+'.json');z=read('platform-before-'+n+'.json')
        assert a['formal_statement']==z['formal_statement'] and a['status']=='Proved' and a['visibility']=='private' and a['mathlib_rev']==unit.ENV
        proofs.append({'name':unit.pre+n,'submission_id':result['id'],'status':'ACCEPTED'})
    # Preserve the original canonical parent reduction with exactly the original four children.
    edges=[z for z in after['reductions'] if z['parent']==unit.parent]
    assert len(edges)==1 and set(edges[0]['children'])=={unit.pre+n for n in ['legendreFiniteUpperBound','legendreFiniteLowerBound','legendreArchimedeanTripleBound','legendreZeroJRootOfUnity']}
    assert all(now[n]['status']=='Proved' for n in edges[0]['children'])
    regpath=w/'.local/adaptation/platform-node-registry.json';registry=json.loads(regpath.read_text());baseline=read('registry-before.json');assert registry==baseline,'Registry changed concurrently'
    direct={z['name']:z for z in registry['direct_closed_proofs']};assert not({z['name'] for z in proofs}&set(direct));direct.update({z['name']:z for z in proofs})
    assert all(now[n]['status']=='Proved' for n in direct)
    counts=after['counts']|{'open_frontier':af['total'],'direct_closed_children':len(direct)}
    registry.update(edges=sorted(after['reductions'],key=lambda z:(z['parent'],z['submission_id'])),direct_closed_proofs=sorted(direct.values(),key=lambda z:z['name']),graph_counts=counts,open_frontier=sorted(expected),local_open_children_below_root=af['total'],published_open_children_below_root=af['total'],platform_statuses={n:z['status'] for n,z in now.items()},mathematical_root_proved=False,recorded_at=datetime.now(timezone.utc).isoformat())
    registry['legendre_finite_sourceproof_unit']={'source':str(b.relative_to(w)),'closed_direct':proofs,'new_platform_nodes':[],'new_open_debt':0,'changed_to_Proved':sorted(changed),'source_ledger':'source-consumer-ledger.json','explicit_Fermat_route_preserved':True,'deprecations':[]}
    ledger=read('source-consumer-ledger.json');ledger['status']='closed_source_proofs_locally_audited_and_platform_ACCEPTED';ledger['direct_proofs']=proofs;ledger['canonical_parent_status']='Proved';save('source-consumer-ledger.json',ledger)
    save('graph-count-evidence.json',{'before':before['counts']|{'open_frontier':bf['total']},'after':counts,'new_platform_nodes':[],'unchanged_mathematical_node_set':True,'unchanged_dependency_pairs':True,'unchanged_reduction_identities':True,'changed_to_Proved':sorted(changed),'canonical_parent_four_children_Proved':True,'deprecations':[],'root':'Open'})
    receipts=[];seen=set()
    for p in b.rglob('*-result.json'):
        if 'observation-errors' in p.parts:continue
        z=json.loads(p.read_text())
        if not all(k in z for k in ['job_id','request','result','resources']) or z['job_id'] in seen:continue
        seen.add(z['job_id']);q,rs,v=z['request'],z['result'],z['resources']
        assert q['exclusive'] and q['workspace']==str(w) and rs['snapshot']['workspace_mode']=='exclusive_worktree' and rs['snapshot']['snapshot_id'] is None
        cpu,user,system=[v.get(k) for k in ['cpu_time_seconds','cpu_user_seconds','cpu_system_seconds']]
        if None not in [cpu,user,system]:assert math.isclose(cpu,user+system,abs_tol=.1)
        if v.get('peak_rss_bytes') is not None:assert v['peak_rss_bytes']<=16*1024**3
        receipts.append({'job_id':z['job_id'],'status':z['status'],'receipt':str(p.relative_to(w)),'source_sha256':q['worktree_manifest']['source_sha256'],'input_head':q['worktree_manifest']['head'],'actual_arguments':rs['actual_arguments'],'exit_code':rs['exit_code'],'diagnostics':rs.get('diagnostics'),**{k:v.get(k) for k in ['wall_time_seconds','cpu_time_seconds','cpu_user_seconds','cpu_system_seconds','peak_rss_bytes','peak_pss_bytes']},'resource_source':v.get('source'),'degraded':v.get('degraded')})
    save('unit-ci-summary.json',{'records':receipts,'succeeded':sum(z['status']=='succeeded' for z in receipts),'failed_or_other_terminal':sum(z['status']!='succeeded' for z in receipts),'observation_mismatch':'idempotency-collision-resolution.json; earlier unrelated receipt excluded from this unit totals','peak_rss_bytes':max(z['peak_rss_bytes'] for z in receipts if z['peak_rss_bytes'] is not None),'missing_resources':'unknown, not zero','closed_direct':proofs,'canonical_parent':'Proved','root':'Open'})
    own=read('delivery-validation.json')['owned_source_hashes']
    own['Solutions/Checks_LegendreFiniteSourceClosure.lean']=sha(w/'Solutions/Checks_LegendreFiniteSourceClosure.lean')
    save('integration.json',{'input_head':read('git-input-state.json')['head'],'status':'Both finite source estimates ACCEPTED and canonical Legendre parent Proved','owned_sources':own,'source_ledger':'source-consumer-ledger.json','closed_direct':proofs,'graph_counts':counts,'original_target_types_preserved':True,'Fermat_route_preserved':True,'deprecations':[]})
    document=r/'docs/Prove2Me适配状态.md';assert document.read_text()==(b/'pending-db-before.md').read_text(),'Pending database changed concurrently'
    updated=(b/'pending-db-after.md').read_text();assert 'Fermat.heightNormalization' in updated and 'Proper.coordinatePoleMultiplicity_eq' in updated
    for n in [714,743]:assert '- `refer/iut/Iut/Tripod/Height.lean:'+str(n)+'`' not in updated
    files=sorted({str((w/f).relative_to(r)) for f in own}|{'docs/Prove2Me适配状态.md',str(regpath.relative_to(r))}|{str(p.relative_to(r)) for p in b.rglob('*') if p.is_file() and '__pycache__' not in p.parts})
    for f in files:
        p=r/f
        if p!=regpath:registry['files'][f]=hashlib.sha256(updated.encode()).hexdigest() if p==document else sha(p)
    registry['files']=dict(sorted(registry['files'].items()))
    assert not subprocess.check_output(['git','diff','--cached','--name-only'],cwd=r).strip(),'Preserve unrelated staged files'
    credentials=json.loads((w/'credentials.json').read_text());secrets=[v.encode() for k,v in credentials.items() if k in ['api_key','access_token','refresh_token','token'] and isinstance(v,str) and len(v)>15]
    for f in files:
        p=r/f;data=updated.encode() if p==document else json.dumps(registry,ensure_ascii=False).encode() if p==regpath else p.read_bytes()
        assert p.name!='credentials.json' and not any(z in data for z in secrets) and (b'p2m_'+b'eyJ') not in data,f
        # Check added-file trailing whitespace before modifying the shared index.
        assert all(line.rstrip(b' \t')==line for line in data.splitlines()),f
        if p.suffix in ['.lean','.md','.py']:assert not data.endswith(b'\n\n'),f
    document.write_text(updated);regpath.write_text(json.dumps(registry,ensure_ascii=False,indent=2)+'\n')
    subprocess.run(['git','diff','--check'],cwd=r,check=True)
    subprocess.run(['git','add','-f','--']+files,cwd=r,check=True)
    subprocess.run(['git','diff','--cached','--check'],cwd=r,check=True)
    print(json.dumps({'staged_files':len(files),'graph_counts':counts,'canonical_parent':'Proved','root':'Open'}),flush=True)
if __name__=='__main__':main()
