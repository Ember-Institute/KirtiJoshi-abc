from pathlib import Path
import json,math
w=Path('/home/admin-wsl/Coq/abc/prove2me_workspace');b=w/'.local/adaptation/fermat-general-position-20261113'
expected=['inputs-leaf','inputs-artifact','composition-leaf','composition-artifact']
for n in ['heightNormalization','liftDifferent','canonicalEstimate']:expected += [n+'-leaf',n+'-artifact']
expected += ['solution-leaf','solution-artifact','composition-review','reduction-axioms-leaf']
for tag in expected:
 x=json.loads((b/(tag+'-result.json')).read_text());assert x['status']=='succeeded' and x['result']['exit_code']==0,tag
rows=[]
for p in list(b.glob('*-result.json'))+list((b/'attempts').glob('*-result.json')):
 x=json.loads(p.read_text())
 if 'resources' not in x or 'request' not in x:continue
 r=x['result'];q=x['request'];v=x['resources'];snap=r['snapshot']
 assert q['workspace']==str(w) and q['exclusive'] is True and snap['workspace_mode']=='exclusive_worktree' and snap['snapshot_id'] is None
 assert v.get('cpu_time_seconds') is None or math.isclose(v['cpu_time_seconds'],v['cpu_user_seconds']+v['cpu_system_seconds'])
 assert v.get('peak_rss_bytes') is None or v['peak_rss_bytes']<=16*1024**3
 rows.append({'receipt':str(p.relative_to(b)),'job_id':x['job_id'],'status':x['status'],'exit_code':r['exit_code'],'input_version':q['worktree_manifest'].get('input_version'),'source_sha256':q['worktree_manifest'].get('source_sha256'),'parameters':q['parameters'],'actual_arguments':r.get('actual_arguments'),'workspace':q['workspace'],'workspace_mode':snap['workspace_mode'],'snapshot_id':None,'wall_time_seconds':v.get('wall_time_seconds'),'cpu_time_seconds':v.get('cpu_time_seconds'),'cpu_user_seconds':v.get('cpu_user_seconds'),'cpu_system_seconds':v.get('cpu_system_seconds'),'peak_rss_bytes':v.get('peak_rss_bytes'),'peak_rss_GiB':v['peak_rss_bytes']/1024**3 if v.get('peak_rss_bytes') is not None else None,'peak_pss_bytes':v.get('peak_pss_bytes'),'resource_source':'MCP-CI scheduler process-tree physical RSS; receipt resources','degraded':'unknown: receipt has no degraded flag','diagnostics':r.get('diagnostics'),'stdout':r.get('stdout'),'stderr':r.get('stderr'),'review':r.get('review')})
out={'scope':'Fermat platform adaptation only; production Scene1 imports unchanged; three new children remain Open.','records':rows,'success_count':sum(x['status']=='succeeded' for x in rows),'failure_count':sum(x['status']!='succeeded' for x in rows),'total_wall_time_seconds':sum(x['wall_time_seconds'] for x in rows if x['wall_time_seconds'] is not None),'total_cpu_time_seconds':sum(x['cpu_time_seconds'] for x in rows if x['cpu_time_seconds'] is not None),'max_peak_rss_bytes':max(x['peak_rss_bytes'] for x in rows if x['peak_rss_bytes'] is not None),'review_boundary':'Conditional composition has propext/Classical.choice/Quot.sound only. Top-level solution imports three Open children and has sorryAx as expected for a sketch.','failures':[{'job_id':'ci-009257-703edf76','cause':'toTripod/coefficient needed noncomputable; definitions/binders otherwise unchanged.'},{'job_id':'ci-009261-39ffb589','cause':'Changed Mathlib mul_le_mul_left API; used mul_le_mul_iff_right0 to cancel a positive scalar. Statement unchanged.'}],'remaining_warning':'Unused ring tactic after field_simp in composition; no mathematical or audit failure.','scope_checks':'All new leaves/artifacts, conditional composition axioms review, reduction axioms, independent shape audit, 19 independent trilingual readbacks and static import inspection. No full production-project claim.'}
(b/'unit-ci-summary.json').write_text(json.dumps(out,ensure_ascii=False,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items() if k in ['success_count','failure_count','total_wall_time_seconds','total_cpu_time_seconds','max_peak_rss_bytes']}))
