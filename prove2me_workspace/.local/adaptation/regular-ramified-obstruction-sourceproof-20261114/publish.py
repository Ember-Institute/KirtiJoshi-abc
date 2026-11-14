from pathlib import Path
import json,sys,importlib.util,uuid,urllib.request,urllib.error
s=importlib.util.spec_from_file_location('strong','/tmp/p2m-obstruction-delivery-20261114.py');strong=importlib.util.module_from_spec(s);s.loader.exec_module(strong);w,b=strong.w,strong.b
sys.path.insert(0,str(w/'.local/adaptation/northcott-sourceproof-20261114'));import delivery_draft
s=importlib.util.spec_from_file_location('p2m_api',w/'.local/abc-item/api.py');api=importlib.util.module_from_spec(s);s.loader.exec_module(api);assert api.base=='https://prove2.me/api/v1'
class Adapter:
 def request(self,endpoint,payload=None,method='GET'):return api.request(endpoint,payload,method)
 def verify_file(self,theorem_id,proof_type,absolute_path,explanation):
  boundary='p2m-'+uuid.uuid4().hex;parts=[]
  for k,v in [('theorem_id',theorem_id),('proof_type',proof_type),('explanation',explanation)]:parts.append(('--'+boundary+'\r\nContent-Disposition: form-data; name="'+k+'"\r\n\r\n'+v+'\r\n').encode())
  code=Path(absolute_path).read_bytes();assert b'sorry' not in code
  parts.extend([('--'+boundary+'\r\nContent-Disposition: form-data; name="file"; filename="solution.lean"\r\nContent-Type: text/plain; charset=utf-8\r\n\r\n').encode()+code+b'\r\n',('--'+boundary+'--\r\n').encode()]);credentials=json.loads((w/'credentials.json').read_text());req=urllib.request.Request(api.base+'/verify',data=b''.join(parts),headers={'Authorization':'Bearer '+credentials['access_token'],'Accept':'application/json','Content-Type':'multipart/form-data; boundary='+boundary},method='POST')
  try:
   with api.opener.open(req,timeout=45) as response:return json.load(response)
  except urllib.error.HTTPError as e:raise RuntimeError('Verification HTTP '+str(e.code)) from None
class Delivery(delivery_draft.Delivery):
 preflight=strong.preflight
 def publication(self,tag,endpoint,payload):
  if tag!='obstruction-children' or not (b/'obstruction-children-submit.json').exists():return super().publication(tag,endpoint,payload)
  original=strong.read('obstruction-children-submit.json');results=[];items={z['theorem_name']:z for z in payload['problems']}
  for job in original['jobs']:
   result=self.api.request('/publish-jobs/'+job['job_id']);self.save('obstruction-children-'+job['job_id']+'-result.json',result)
   if result['status']=='PUBLISHED':results.append(result);continue
   assert result['status']=='FAILED' and result['theorem_name'].endswith('.derivAlong_mem'),result['status']
   retry={'problems':[items[result['theorem_name']]],'env':payload['env'],'private':True}
   results.extend(super().publication('obstruction-children-derivAlongMem-retry','/submit-problem',retry))
  assert len(results)==9 and all(z['status']=='PUBLISHED' for z in results)
  self.save('final-child-publications.json',results);return results
 def run(self):
  self.preflight();parent=self.observe(strong.targetid,strong.target)
  if not (b/'platform-before-parent.json').exists():self.save('platform-before-parent.json',strong.read('platform-before-target.json'))
  original=strong.read('platform-before-target.json')['formal_statement'];assert parent['formal_statement']==original
  for mod in self.plan['definitions']:self.publication('def-'+mod['name'],'/submit-definition',self.read(mod['payload']))
  batch=self.read('obstruction-children-payload.json');results=self.publication('obstruction-children','/submit-problem',batch);ids={z['theorem_name']:z['theorem_id'] for z in results};assert set(ids)==set(self.plan['new_mathematical_nodes']);self.save('published-child-ids.json',ids)
  self.verify(strong.target,strong.targetid,{'SKETCH_ACCEPTED','ACCEPTED'})
  for name in self.plan['new_mathematical_nodes']:
   value=self.observe(ids[name],name)
   if value['status']!='Proved':self.verify(name,ids[name],{'ACCEPTED'})
   value=self.observe(ids[name],name);assert value['status']=='Proved';self.save('platform-after-'+name.removeprefix('AbcAdaptation.Tripod.').replace('.','_')+'.json',value)
  # The existing accepted target sketch and finiteness sketch must propagate naturally.
  import time
  for attempt in range(13):
   after=self.observe(strong.targetid,strong.target);finite=self.observe(strong.parentid,strong.parent)
   if after['status']==finite['status']=='Proved':break
   if attempt<12:time.sleep(5)
  assert after['status']==finite['status']=='Proved';assert after['formal_statement']==original
  patch=self.read('parent-metadata-patch-draft.json');self.bind('parent-metadata-patch-request.json',patch)
  if not all(after.get(k)==v for k,v in patch.items()):self.save('parent-metadata-patch-response.json',self.api.request('/theorems/'+strong.targetid,patch,'PATCH'))
  after=self.observe(strong.targetid,strong.target);assert after['formal_statement']==original and all(after[k]==v for k,v in patch.items());self.save('platform-after-parent.json',after)
  self.save('platform-after-finiteness.json',finite)
  # Preserve the already independent parent readback; remove only obsolete status prose from source.
  baseline=strong.read('platform-before-parent.json');src=baseline['source'];src=src.replace('The proof for arbitrary supplied nonconstant functions remains Open: local derivations and finitely many chart generators must supply the finite ramification locus.','The complete accepted local derivative obstruction and derivative bad-place finiteness source proofs supply the existing finite ramification reduction, including all places and the actual transcendental function.').replace('Two actual function-field mathematical children remain Open.','The two actual function-field children have complete accepted source proofs.').replace('The local obstruction child remains Open.','The local obstruction child now has an accepted complete source proof.')
  # Record actual metadata before making any optional correction; exact math statement is unchanged.
  self.save('finite-metadata-before.json',finite)
  if src!=baseline['source']:
   assert finite['formal_statement']==baseline['formal_statement'];fp={'source':src};self.bind('finite-metadata-patch-request.json',fp);self.save('finite-metadata-patch-response.json',self.api.request('/theorems/'+strong.parentid,fp,'PATCH'));finite=self.observe(strong.parentid,strong.parent);self.save('platform-after-finiteness.json',finite)
  from graph_completion import fetch_complete_math_graph
  self.save('root-graph-after.json',fetch_complete_math_graph(self.api,strong.root,self.save,'root-graph-after'));self.frontier('after');root=self.observe(strong.root,'abc.goal.lt_constant_mul_fix');assert root['status']=='Open';self.save('platform-root-after.json',root)
  print('Nine source-proof nodes and existing obstruction accepted; finiteness parent Proved.',flush=True)
if __name__=='__main__':Delivery(Adapter(),b,w).run()
