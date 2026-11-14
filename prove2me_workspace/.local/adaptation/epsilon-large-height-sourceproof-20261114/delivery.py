from pathlib import Path
import json,hashlib,math,sys,importlib.util,re,subprocess,shutil,urllib.request,urllib.error,uuid
from datetime import datetime,timezone
r=Path('/home/admin-wsl/Coq/abc');w=r/'prove2me_workspace';b=w/'.local/adaptation/epsilon-large-height-sourceproof-20261114';u=str(b.relative_to(w))+'/';target='AbcAdaptation.Tripod.epsilonELargeHeight';root='e33ff731-60a7-43ef-87ae-c12aeba23cb5';source='Theorems/Thm_'+target.replace('.','_')+'.lean';sol=u+'Solution_epsilonELargeHeight.lean'
def read(n):return json.loads((b/n).read_text())
def save(n,z):(b/n).write_text(json.dumps(z,ensure_ascii=False,indent=2)+'\n')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def prose(rows):return '\n\n'.join('**'+title+'**\n\n'+'\n\n'.join('`'+z['declaration']+'`\n\n'+z[lang] for z in rows) for lang,title in [('en','English'),('zh_Hans','简体中文'),('ja','日本語')])
def bind_readbacks():
 blind=Path('/tmp/p2m-epsilon-readback-20261114/readbacks.json');rb=json.loads(blind.read_text());rb['declarations']=rb.pop('readbacks');
 for z in rb['declarations']:
  st=z['statements'];z['en']=st.get('en',st.get('English'));z['zh_Hans']=st.get('zh_Hans',st.get('zh',st.get('SimplifiedChinese',st.get('Chinese'))));z['ja']=st.get('ja',st.get('Japanese'))
 shutil.copy2(blind,b/'blind-readbacks-original.json');graph=[json.loads(l) for l in (b/'decl_graph.jsonl').read_text().splitlines()];module='Theorems.Thm_'+target.replace('.','_');by={z.get('userName',z['name']):z for z in graph if z['module']==module and z['startLine']>0};rows=rb['declarations'];assert len(rows)==3
 quote=(b/'mochizuki-quotation.md').read_text().strip()
 for z in rows:
  gr=by[z['declaration']];z.update(path=source,module=module,compiler_name=gr['name'],compiler_source_span={'startLine':gr['startLine'],'endLine':gr['endLine']},elaboratedType=gr['elaboratedType'],source_file_sha256=sha(w/source),proof_status='complete kernel-checked source proof; platform status recorded separately',en_source_quote=quote,en_source_quote_ledger_binding={'file':'source-quotes.json','scope':'Original paper error function and smallness context. Explicit fourth-power sufficient threshold is from the formal Lean implementation.'})
 for z in rows:
  name=z['declaration'].rsplit('.',1)[1];formula=(r'\frac{(60\delta)^2\log(2\delta h)}{\sqrt h}\le\epsilon' if name=='epsilonELargeHeight' else r'\log h\le 4\sqrt{\sqrt h}' if name=='log_le_four_mul_sqrt_sqrt' else r'\log y\le y')
  for lang in ['en','zh_Hans','ja']:z[lang]+='\n\n$$\n'+formula+'\n$$'
 rb['input_file_sha256']={source:sha(w/source)};rb['compiler_bound']=True;save('final-readbacks.json',rb);v=read('delivery-validation.json');v['readbacks_sha256']=sha(b/'final-readbacks.json');save('delivery-validation.json',v)
 return rb

def preflight():
 v=read('delivery-validation.json');assert v['passed'] and v['exact_existing_target_type_equal'] and read('existing-types-equal.json') is True;assert v['new_open_debt']==0
 assert v['source_hashes']=={source:sha(w/source)} and v['solution_hashes']=={sol:sha(w/sol)}
 for f,k in [('decl_graph.jsonl','declaration_graph_sha256'),('syntax-boundaries.json','syntax_boundaries_sha256'),('final-readbacks.json','readbacks_sha256')]:assert sha(b/f)==v[k]
 modes=set()
 for c in v['compiler_checks']:
  z=read(c['tag']+'-result.json');q,rs,resources=z['request'],z['result'],z['resources'];assert z['status']=='succeeded' and rs['exit_code']==0;assert q['exclusive'] and q['workspace']==str(w);assert q['worktree_manifest']['source_sha256']==sha(w/c['source']);assert rs['snapshot']['workspace_mode']=='exclusive_worktree' and rs['snapshot']['snapshot_id'] is None;expected=['lean']+([c['source'],'-o','.lake/build/lib/lean/'+c['source'][:-5]+'.olean'] if c['artifact'] else [c['source']]);assert rs['actual_arguments']==expected;assert 'sorryAx' not in rs['stdout']+rs['stderr'];assert resources['peak_rss_bytes']<=16*1024**3
  if resources.get('cpu_time_seconds') is not None:assert math.isclose(resources['cpu_time_seconds'],resources['cpu_user_seconds']+resources['cpu_system_seconds'],abs_tol=.1)
  if c['review']:assert rs['review']['passed'] and q['worktree_manifest']['input_hashes'][source]==sha(w/source)
  modes.add((c['source'],c['artifact'],c['review']))
 for mode in [(source,False,False),(source,True,False),(sol,False,False),('Solutions/Checks_TripodEpsilonLargeHeight.lean',False,True),(u+'AuditAllConstants.lean',False,True),(u+'ProductionGates.lean',False,True)]:assert mode in modes
 text=(w/sol).read_text();assert not re.search(r'\b(sorry|admit|axiom|unsafe)\b',text);assert not any(l.startswith(('import Theorems.','import Solutions.','import Open.','import Iut.','import Genl.')) for l in text.splitlines())
 graph=[json.loads(l) for l in (b/'decl_graph.jsonl').read_text().splitlines()];by={z['name']:z for z in graph};rb=read('final-readbacks.json');assert len(rb['declarations'])==3;todo=[target];seen=set()
 while todo:
  name=todo.pop()
  if name in seen:continue
  seen.add(name);z=by.get(name)
  if z:todo+=z['typeDeps']+z['valueDeps']
 for z in rb['declarations']:
  gr=by[z['compiler_name']];assert z['compiler_name'] in seen;assert z['elaboratedType']==gr['elaboratedType'] and z['path']==source and z['source_file_sha256']==sha(w/source);assert all(z[k].strip() for k in ['en','zh_Hans','ja'])
 assert not any(z['kind']=='axiom' or 'sorryAx' in z['typeDeps']+z['valueDeps'] for z in graph)
 provenance=read('source-consumer.json');p=r/'refer/iut/Iut/Implication/Corollary22.lean';assert sha(p)==sha(b/'reference/Corollary22.lean');link=read('source-ledger-link.json');assert sha(r/link['production_ledger'])==link['production_ledger_sha256']
 return v

def publish():
 preflight();spec=importlib.util.spec_from_file_location('api',w/'.local/abc-item/api.py');api=importlib.util.module_from_spec(spec);spec.loader.exec_module(api);assert api.base=='https://prove2.me/api/v1';ident=read('target-id.json')['id'];before=read('platform-before-target.json');current=api.request('/theorems/'+ident);assert current['theorem_name']==target and current['visibility']=='private' and current['formal_statement']==before['formal_statement']
 quote=(b/'mochizuki-quotation.md').read_text().strip();rb=read('final-readbacks.json')['declarations'];common='Shinichi Mochizuki, Inter-universal Teichmuller Theory IV, Corollary 2.2(ii),(iii), printed pp.42–43 and proof pp.47–48, https://www.kurims.kyoto-u.ac.jp/~motizuki/Inter-universal%20Teichmuller%20Theory%20IV.pdf . The checked original quotation supplies the exact error-function and smallness context. The explicit fourth-power sufficient threshold is the complete formal source proof Iut/Implication/Corollary22.lean::epsilonE_le, with log_le_four_mul_sqrt_sqrt and log_le_self_of_pos. Archive SHA256 '+sha(b/'reference/Corollary22.lean')+'. Historical upstream revision is unverified. Complete source proof independently rechecked under Mathlib 0df444a; original licence and author notices retained. No new mathematical node, assumption, Open debt, Iut/Genl runtime dependency or global 3.12 claim.'
 explanation=quote+'\n\n'+prose(rb)+'\n\n'+common;request={'theorem_id':ident,'proof_type':'prove','file':sol,'source_sha256':sha(w/sol),'explanation':explanation};sp=b/'verify-submit.json'
 if sp.exists():assert read('verify-request.json')==request;submitted=read(sp.name)
 else:
  assert not (b/'verification-requested.json').exists(),'Reconcile existing intent before POST';save('verify-request.json',request);save('verification-requested.json',request);(b/'submitted-solution.lean').write_bytes((w/sol).read_bytes());boundary='p2m-'+uuid.uuid4().hex;parts=[]
  for k,z in [('theorem_id',ident),('proof_type','prove'),('explanation',explanation)]:parts.append(('--'+boundary+'\r\nContent-Disposition: form-data; name="'+k+'"\r\n\r\n'+z+'\r\n').encode())
  parts.extend([('--'+boundary+'\r\nContent-Disposition: form-data; name="file"; filename="solution.lean"\r\nContent-Type: text/plain; charset=utf-8\r\n\r\n').encode()+(w/sol).read_bytes()+b'\r\n',('--'+boundary+'--\r\n').encode()]);c=json.loads((w/'credentials.json').read_text());req=urllib.request.Request(api.base+'/verify',data=b''.join(parts),headers={'Authorization':'Bearer '+c['access_token'],'Accept':'application/json','Content-Type':'multipart/form-data; boundary='+boundary},method='POST')
  try:
   with api.opener.open(req,timeout=45) as resp:submitted=json.load(resp)
  except urllib.error.HTTPError as e:raise RuntimeError('Verification HTTP '+str(e.code)) from None
  save(sp.name,submitted)
 import time
 while True:
  z=api.request('/verify?submission_id='+submitted['submission_id']);save('verify-result.json',z)
  if z['status']!='PENDING':break
  time.sleep(5)
 assert z['status']=='ACCEPTED' and z['id']==submitted['submission_id'] and z['theorem_id']==ident,z['status'];current=api.request('/theorems/'+ident);assert current['status']=='Proved' and current['formal_statement']==before['formal_statement']
 selected=[z for z in rb if z['declaration']==target];assert len(selected)==1;patch={'natural_language_statement':quote+'\n\n'+prose(selected),'source':common}
 if (b/'metadata-patch-request.json').exists():assert read('metadata-patch-request.json')==patch
 else:save('metadata-patch-request.json',patch)
 if not all(current.get(k)==z for k,z in patch.items()):save('metadata-patch-response.json',api.request('/theorems/'+ident,patch,'PATCH'))
 after=api.request('/theorems/'+ident);assert after['formal_statement']==before['formal_statement'] and after['status']=='Proved' and all(after[k]==z for k,z in patch.items());save('platform-after-target.json',after)
 sys.path.insert(0,str(w/'.local/adaptation/northcott-sourceproof-20261114'));from graph_completion import fetch_complete_math_graph
 save('root-graph-after.json',fetch_complete_math_graph(api,root,save,'root-graph-after'));leaves=[]
 while True:
  off=len(leaves);z=api.request('/theorems/'+root+'/open-leaves?limit=50&offset='+str(off));save('root-frontier-after-page-'+str(off)+'.json',z);leaves+=z['open_leaves']
  if len(leaves)>=z['total']:break
 save('root-frontier-after.json',{'open_leaves':leaves,'total':z['total'],'all_pages_fetched':True});print('Existing epsilonELargeHeight ACCEPTED and Proved; graph read back.',flush=True)

if __name__=='__main__':
 if sys.argv[1]=='bind':bind_readbacks();preflight();print('Epsilon preflight passed.',flush=True)
 elif sys.argv[1]=='publish':publish()
