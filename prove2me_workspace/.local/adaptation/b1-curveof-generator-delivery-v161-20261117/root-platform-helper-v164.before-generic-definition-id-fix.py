from pathlib import Path
import json,hashlib,importlib.util,sys,urllib.request,urllib.parse,uuid,time
W=Path('/home/admin-wsl/Coq/abc/prove2me_workspace');D=W/'.local/adaptation/b1-curveof-generator-publication-v161-20261117';A=W/'.local/adaptation/main-chain-open-20261116';Q=W/'.local/adaptation/b1-curveof-generator-review-v161-20261117/actual/generator-fourrole-correspondence.json'
spec=importlib.util.spec_from_file_location('p2mapi',W/'.local/abc-item/api.py');api=importlib.util.module_from_spec(spec);spec.loader.exec_module(api)
save=lambda p,j:p.write_text(json.dumps(j,ensure_ascii=False,indent=2)+'\n')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def guard():
 q=json.loads(Q.read_text());assert q['allRequiredCorrespondenceChecksPassed'] and q['sourceMembershipCanonicalSolutionPlatformFourRolesCompared'] and q['compiledPlatformShapeComparedAgainstCompleteSourceTYPEAndProof'] and q['platformTheoremNameEqualsActualCanonicalFullName']
 assert len(q['reports'])==4 and all(not r['hasSorryAx'] and set(r['axioms'])<={'propext','Classical.choice','Quot.sound'} and r['completeTYPEKernelEqual'] and r['completeProofOrDataValueKernelEqual'] for r in q['reports'])
 p=json.loads((D/'theorem/payload-final.json').read_text());assert {k:p[k] for k in q['expectedPlatformPayload']}==q['expectedPlatformPayload']
 return q
kind=sys.argv[2] if len(sys.argv)>2 else 'theorem';d=D/kind;mode=sys.argv[1]
if mode=='submit':
 q=guard();p=json.loads((d/'payload-final.json').read_text());assert p['private'] is True and p['env']=='0df444a360eaa60ab8c11dca51a86af692955474'
 if kind=='definition':
  v=json.loads((D/'theorem/proved-readback.json').read_text());assert v['status']=='Proved' and v['visibility']=='private'
  assert p['definition']==(W/'Definitions/Def_AbcAdaptation_Reference_Iut_Tripod_CurveOfGenerator.lean').read_text()
 assert not(d/'publish-intent.json').exists() and not(d/'publish-submit.json').exists(),'Existing POST intent/ack must be resolved before resubmission'
 save(d/'publish-intent.json',{'stage':'intent-before-post','kind':kind,'private':True,'payloadSHA256':sha(d/'payload-final.json'),'fullAudit':str(Q)})
 v=api.request('/submit-problem' if kind=='theorem' else '/submit-definition',p,method='POST');save(d/'publish-submit.json',v)
 if kind=='theorem':
  assert not v.get('errors') and len(v['jobs'])==1;job=v['jobs'][0]['job_id']
 else:job=v['job_id']
 save(d/'publish-journal.json',{'kind':kind,'job_id':job,'status':'PENDING'});print(json.dumps({'kind':kind,'job_id':job}))
elif mode=='poll':
 j=json.loads((d/'publish-journal.json').read_text());v=api.request('/publish-jobs/'+j['job_id']);save(d/'publish-result.json',v);j['status']=v['status'];save(d/'publish-journal.json',j)
 print(json.dumps({'kind':kind,'job_id':j['job_id'],'status':v['status'],'error_message':v.get('error_message')},ensure_ascii=False))
 if v['status']=='PUBLISHED':
  key='theorem_id' if kind=='theorem' else 'definition_id';item=api.request(('/theorems/' if kind=='theorem' else '/definitions/')+v[key]);save(d/'published-item.json',item);p=json.loads((d/'payload-final.json').read_text())
  fields=['theorem_name','preamble','formal_statement','theorem_title','natural_language_statement','source'] if kind=='theorem' else ['definition_name','definition_title','definition','natural_language_statement','source']
  for key in fields:assert item[key]==p[key],key
  assert item['visibility']=='private'
  save(d/'publication-validation.json',{'allSubmittedFieldsExactlyReadBack':True,'private':True,'fieldNames':fields})
  print(json.dumps({'kind':kind,'item_id':item.get('theorem_id',item.get('definition_id')),'allFieldsExact':True}))
elif mode=='verify':
 guard();d=D/'theorem';S=W/'Solutions/Sol_AbcAdaptation_Tripod_mem_fieldOfExtended_self.lean';receipt=json.loads((W/'.local/adaptation/b1-curveof-generator-v157-20261117/mem-fieldofextended-self-solution-leaf-result.json').read_text());assert receipt['status']=='succeeded' and receipt['result']['exit_code']==0
 req=receipt.get('request',receipt.get('snapshot',{}).get('request'));assert req['worktree_manifest']['source_sha256']==sha(S)
 item=json.loads((d/'published-item.json').read_text());assert item['status']=='Open' and item['visibility']=='private';tid=item['theorem_id']
 assert not(d/'verify-intent.json').exists() and not(d/'verify-submit.json').exists(),'Existing verification intent must be resolved before resubmission'
 p=json.loads((d/'proof-explanation.json').read_text());explanation='\n\n'.join('# '+label+'\n\n'+p[key] for label,key in [('English','en'),('简体中文','zh-Hans'),('日本語','ja')]);(d/'proof-explanation-submitted.md').write_text(explanation+'\n')
 api.request('/theorems/'+tid);c=json.loads((W/'credentials.json').read_text());boundary='p2m-'+uuid.uuid4().hex;parts=[]
 for key,value in [('theorem_id',tid),('proof_type','prove'),('explanation',explanation)]:parts.append(('--'+boundary+'\r\nContent-Disposition: form-data; name="'+key+'"\r\n\r\n'+value+'\r\n').encode())
 parts.append(('--'+boundary+'\r\nContent-Disposition: form-data; name="file"; filename="solution.lean"\r\nContent-Type: text/plain; charset=utf-8\r\n\r\n').encode()+S.read_bytes()+b'\r\n');parts.append(('--'+boundary+'--\r\n').encode())
 save(d/'verify-intent.json',{'stage':'intent-before-post','theorem_id':tid,'solutionFile':str(S),'solutionSHA256':sha(S),'acceptedLeafJob':receipt['job_id'],'fullAudit':str(Q),'private':True})
 req=urllib.request.Request(api.base+'/verify',data=b''.join(parts),headers={'Authorization':'Bearer '+c['access_token'],'Accept':'application/json','Content-Type':'multipart/form-data; boundary='+boundary},method='POST')
 with api.opener.open(req,timeout=45) as res:v=json.load(res)
 save(d/'verify-submit.json',v);save(d/'verify-journal.json',{'submission_id':v['submission_id'],'theorem_id':tid,'status':v['status']});print(json.dumps({'submission_id':v['submission_id'],'status':v['status']}))
elif mode=='poll-verify':
 d=D/'theorem';j=json.loads((d/'verify-journal.json').read_text());v=api.request('/verify?submission_id='+j['submission_id']);save(d/'verify-result.json',v);j['status']=v['status'];save(d/'verify-journal.json',j);print(json.dumps({'submission_id':j['submission_id'],'status':v['status'],'error_message':v.get('error_message')},ensure_ascii=False))
 if v['status']=='ACCEPTED':
  r=api.request('/theorems/'+j['theorem_id']);save(d/'proved-readback.json',r);assert r['status']=='Proved' and r['visibility']=='private';print(json.dumps({'theorem_id':j['theorem_id'],'status':r['status']}))
else:raise SystemExit('unknown mode')
