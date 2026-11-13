from pathlib import Path
import json,hashlib,math,subprocess,shutil
from datetime import datetime, timezone
r=Path('/home/admin-wsl/Coq/abc');w=r/'prove2me_workspace';b=w/'.local/adaptation/fermat-riemann-sourceproof-20261114';pre='AbcAdaptation.Tripod.Fermat.Proper.'
v=json.loads((b/'sourceproof-validation.json').read_text());assert v['passed'] and v['exact_platform_types_equal']
# Bind delivery to the exact local files that passed scheduled validation.
for relative, expected in v['definition_hashes'].items():
 assert hashlib.sha256((w/relative).read_bytes()).hexdigest()==expected, relative
for name, expected in v['theorem_hashes'].items():
 relative='Theorems/Thm_'+name.replace('.','_')+'.lean'
 assert hashlib.sha256((w/relative).read_bytes()).hexdigest()==expected, relative
assert hashlib.sha256((b/'decl_graph.jsonl').read_bytes()).hexdigest()==v['declaration_graph_sha256']
assert json.loads((b/'platform-types-equal.json').read_text()) is True
for name in ['functionZeroPoleDegrees','riemannPolarApproximation','riemannBasisPowerLowerBound']:
 relative='.local/adaptation/fermat-riemann-sourceproof-20261114/Solution_'+name+'.lean'
 receipt=json.loads((b/('solution-'+name+'-leaf-result.json')).read_text())
 assert receipt['status']=='succeeded' and receipt['result']['exit_code']==0
 assert receipt['request']['parameters']['source']==relative
 assert receipt['request']['worktree_manifest']['source_sha256']==hashlib.sha256((w/relative).read_bytes()).hexdigest(), relative
exact=json.loads((b/'exact-platform-types-leaf-result.json').read_text())
assert exact['status']=='succeeded' and exact['result']['exit_code']==0
assert exact['request']['worktree_manifest']['source_sha256']==hashlib.sha256((b/'ValidatePlatformTypes.lean').read_bytes()).hexdigest()
# Each submitted Definition must have a matching payload and terminal publication receipt.
for mod in ['FermatCurveFieldDegree','FermatFunctionFiberDegrees','FermatRiemannPolarApproximation','FermatRiemannBasisPowers']:
 tag='def-'+mod
 payload=json.loads((b/(tag+'-payload.json')).read_text())
 assert payload['definition_name']==mod and payload['private'] is True
 assert payload['env']=='0df444a360eaa60ab8c11dca51a86af692955474'
 assert payload['definition']==(w/('Definitions/Def_'+mod+'.lean')).read_text()
 submitted=json.loads((b/(tag+'-submit.json')).read_text())
 jobs=submitted.get('jobs') or [{'job_id':submitted['job_id']}]
 assert jobs
 for job in jobs:
  published=json.loads((b/(tag+'-'+job['job_id']+'-result.json')).read_text())
  assert published['status']=='PUBLISHED' and published['visibility']=='private'
names=['functionZeroPoleDegrees','riemannPolarApproximation','riemannBasisPowerLowerBound'];parents=['riemannRochFiniteDimensional','riemannRochDimensionUpperBound','riemannRochEventuallyLinear','polarPresentationExists'];proofs=[]
for n in names:
 x=json.loads((b/('prove-'+n+'-verify-result.json')).read_text());assert x['status']=='ACCEPTED';s=json.loads((b/('prove-'+n+'-verify-submit.json')).read_text())['submission_id'];proofs.append({'name':pre+n,'submission_id':s,'status':x['status']})
statuses={}
for n in names+parents:
 x=json.loads((b/('platform-after-'+n+'.json')).read_text());assert x['visibility']=='private' and x['mathlib_rev']=='0df444a360eaa60ab8c11dca51a86af692955474';assert x['theorem_name']==pre+n;statuses[pre+n]=x['status']
 assert x['status']=='Proved',(n,x['status'])
for tag in ['sourceproof-closed-review','source-closure-review','all-new-definition-axioms-review','production-gates-review']:
 x=json.loads((b/(tag+'-result.json')).read_text());assert x['status']=='succeeded' and x['result']['exit_code']==0 and x['result']['review']['passed'];assert 'sorryAx' not in x['result']['stdout']
front=json.loads((b/'root-frontier-after.json').read_text());assert front['all_pages_fetched'] and len(front['open_leaves'])==front['total'];assert not {pre+n for n in names+parents}&{x['theorem_name'] for x in front['open_leaves']}
records=[]
for f in b.rglob('*-result.json'):
 x=json.loads(f.read_text())
 if not all(k in x for k in ['request','resources','result','job_id']):continue
 q=x['request'];out=x['result'];a=q['parameters'];wanted=['lean',a['source']] if 'source' in a else ['lean']+a['args'];res=x['resources'];snap=out['snapshot']
 assert q['exclusive'] is True and q['workspace']==str(w);assert snap['workspace_mode']=='exclusive_worktree' and snap['snapshot_id'] is None
 assert out['actual_arguments']==wanted
 if res.get('cpu_time_seconds') is not None:assert math.isclose(res['cpu_time_seconds'],res['cpu_user_seconds']+res['cpu_system_seconds'])
 if res.get('peak_rss_bytes') is not None:assert res['peak_rss_bytes']<=16*1024**3
 assert x['status'] in ['succeeded','failed']
 records.append({'job_id':x['job_id'],'status':x['status'],'receipt':str(f.relative_to(w)),'input_version':q['worktree_manifest']['input_version'],'source_sha256':q['worktree_manifest']['source_sha256'],'actual_arguments':wanted,'exit_code':out['exit_code'],'workspace':q['workspace'],'workspace_mode':snap['workspace_mode'],'snapshot_id':snap['snapshot_id'],'wall_time_seconds':res.get('wall_time_seconds'),'cpu_time_seconds':res.get('cpu_time_seconds'),'cpu_user_seconds':res.get('cpu_user_seconds'),'cpu_system_seconds':res.get('cpu_system_seconds'),'peak_rss_bytes':res.get('peak_rss_bytes'),'peak_pss_bytes':res.get('peak_pss_bytes'),'resource_source':'MCP-CI process-tree physical RSS. PSS missing is unknown; no degraded flag is present in these receipts.','diagnostics':out.get('diagnostics'),'review_passed':out.get('review',{}).get('passed') if out.get('review') else None})
def total(k):return sum(x[k] for x in records) if all(x[k] is not None for x in records) else None
summary={'scope':'Independent reuse of fixed Belyi source proofs for three existing geometric leaves; four transitive Riemann consumers rebuilt and audited; production entry gates included.','records':records,'succeeded':sum(x['status']=='succeeded' for x in records),'failed':sum(x['status']=='failed' for x in records),'wall_time_seconds':total('wall_time_seconds'),'cpu_time_seconds':total('cpu_time_seconds'),'cpu_user_seconds':total('cpu_user_seconds'),'cpu_system_seconds':total('cpu_system_seconds'),'peak_rss_bytes':max(x['peak_rss_bytes'] for x in records if x['peak_rss_bytes'] is not None),'failures':'Canonical rational/quotient scalar structures required explicit instance paths to avoid expensive search. Follow-up repairs preserved original theorem statements.','closed_nodes':statuses,'root_proved':False};(b/'unit-ci-summary.json').write_text(json.dumps(summary,ensure_ascii=False,indent=2)+'\n')
regp=w/'.local/adaptation/platform-node-registry.json';reg=json.loads(regp.read_text());old=reg.get('direct_closed_proofs',[]);reg['direct_closed_proofs']=old+[p for p in proofs if not any(x['name']==p['name'] for x in old)];reg['platform_statuses']=reg.get('platform_statuses',{})|statuses;reg['open_frontier']=[x['theorem_name'] for x in front['open_leaves']];reg['graph_counts']|={'open_frontier':front['total'],'direct_closed_children':len(reg['direct_closed_proofs'])};reg.update(local_open_children_below_root=front['total'],published_open_children_below_root=front['total'],mathematical_root_proved=False);reg['riemann_sourceproof_unit']={'closed_direct':proofs,'closed_transitive':{pre+n:statuses[pre+n] for n in parents},'evidence':'fermat-riemann-sourceproof-20261114','remaining_new_open':0}
reg['recorded_at']=datetime.now(timezone.utc).isoformat()
p=r/'docs/Prove2Me适配状态.md';text=p.read_text();paragraphs=text.split('\n\n')
pending={n:[i for i,paragraph in enumerate(paragraphs) if paragraph.startswith('`Proper.'+n+'`')] for n in names}
assert all(len(indices)==1 for indices in pending.values()) or all(not indices for indices in pending.values()),pending
removed={i for indices in pending.values() for i in indices}
text='\n\n'.join(paragraph for i,paragraph in enumerate(paragraphs) if i not in removed)
p.write_text(text.rstrip()+'\n')
integration=json.loads((b/'integration.json').read_text());integration.update(status='All local checks passed; four Definitions PUBLISHED; three direct proofs ACCEPTED; seven local/platform nodes closed.',direct_proofs=proofs,platform_statuses=statuses);(b/'integration.json').write_text(json.dumps(integration,ensure_ascii=False,indent=2)+'\n')
ledger={'source_pin':integration['source_pin'],'status':'validated complete existing source-proof reuse','original_delivery_ledgers':['fiber-source-consumer.json','riemann-source-consumer.json'],'source_boundary_link':'source-ledger-link.json','definition_hashes':v['definition_hashes'],'theorem_hashes':v['theorem_hashes'],'consumer_chain':['chart residue and ideal valuation identities -> zero/pole fiber degrees','actual minpoly evaluation and all-place pole control -> one global approximation','actual Module.finBasis and powers -> Riemann dimension lower bound','these three source proofs -> finite/upper/eventual -> polarPresentationExists -> ArithmeticDivisorChoices -> canonicalEstimate'],'actual_platform_states':statuses,'new_assumptions':[],'full_abc_closed':False};(b/'current-source-consumer.json').write_text(json.dumps(ledger,ensure_ascii=False,indent=2)+'\n')
for src,name in [('/tmp/p2m-riemann-sourceproof-ci-20261114.py','ci-coordinator.py'),('/tmp/p2m-sourceproof-follow-through-20261114.py','follow-through.py'),('/tmp/p2m-platform-sourceproof-20261114.py','platform-publish.py')]:shutil.copyfile(src,b/name)
plan=r/'docs/开发计划.Prove2Me适配.md';plan_text=plan.read_text()
completed_workflows=[
 '转换已完成 proof term 时，使用 Prove2Me 的声明图与语法位置提取工具确定依赖、源范围和 proof 边界；提取脚本也经 MCP-CI 运行。',
 '对上传前后 elaborated type 作一致性核对；证明重命名和平台命名空间变换不会改变数学陈述。'
]
for entry in completed_workflows:
 old='- [ ] '+entry;new='- [x] '+entry
 assert old in plan_text or new in plan_text,entry
 plan_text=plan_text.replace(old,new)
plan.write_text(plan_text)
(b/'plan-checkbox-evidence.json').write_text(json.dumps({'scope':'Section 8/9 delivered-unit workflows only; all mathematical/global/Act2 gates remain unchanged.','entries':completed_workflows,'evidence':['source-graph-leaf-result.json','decl_graph.jsonl','exact-platform-types-leaf-result.json','platform-types-equal.json','sourceproof-validation.json']},ensure_ascii=False,indent=2)+'\n')
shutil.copyfile('/tmp/p2m-sourceproof-delivery-audit-20261114/report.json',b/'delivery-script-audit.json')
shutil.copyfile('/tmp/p2m-sourceproof-provenance-fix-20261114.py',b/'provenance-fix.py')
shutil.copyfile('/tmp/p2m-finalize-sourceproof-20261114.py',b/'finalize.py')
files=['docs/开发计划.Prove2Me适配.md','docs/Prove2Me适配状态.md','prove2me_workspace/.local/adaptation/platform-node-registry.json']+[str((w/f).relative_to(r)) for f in integration['files']]+['prove2me_workspace/Solutions/Checks_FermatRiemannSourceProofs.lean','prove2me_workspace/Solutions/Checks_FermatRiemannSourceClosure.lean']+[str(f.relative_to(r)) for f in b.rglob('*') if f.is_file() and '__pycache__' not in f.parts];files=list(dict.fromkeys(files))
assert str((w/'credentials.json').relative_to(r)) not in files
credential_values=[]
credentials=json.loads((w/'credentials.json').read_text())
for key in ['access_token','refresh_token','api_key','token']:
 value=credentials.get(key)
 if isinstance(value,str) and len(value)>=16:credential_values.append(value.encode())
for f in files:
 data=(r/f).read_bytes()
 assert (b'p2m_'+b'eyJ') not in data and (b'"access_'+b'token": "eyJ') not in data,f
 assert not any(value in data for value in credential_values),f
 if f.endswith('platform-node-registry.json'):continue
 reg['files'][f]=hashlib.sha256(data).hexdigest()
regp.write_text(json.dumps(reg,ensure_ascii=False,indent=2)+'\n');assert not any(value in regp.read_bytes() for value in credential_values);subprocess.run(['git','add','-f','--']+files,cwd=r,check=True);subprocess.run(['git','diff','--cached','--check'],cwd=r,check=True)
print(json.dumps({'staged':len(files),'graph_counts':reg['graph_counts'],'ci':{k:summary[k] for k in ['succeeded','failed','wall_time_seconds','cpu_time_seconds','peak_rss_bytes']}},ensure_ascii=False),flush=True)
