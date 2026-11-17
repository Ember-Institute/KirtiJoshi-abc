from pathlib import Path
import json,hashlib,importlib.util,sys,urllib.parse
W=Path('/home/admin-wsl/Coq/abc/prove2me_workspace');D=W/'.local/adaptation/b1-curveof-assembly-publication-v180-20261117';R=W/'.local/adaptation/b1-curveof-native-review-v175-20261117';A=W/'.local/adaptation/main-chain-open-20261116'
spec=importlib.util.spec_from_file_location('api',W/'.local/abc-item/api.py');api=importlib.util.module_from_spec(spec);spec.loader.exec_module(api)
save=lambda p,j:p.write_text(json.dumps(j,ensure_ascii=False,indent=2)+'\n')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
mode,kind=sys.argv[1:3];assert kind in ['carrier','assembly'];d=D/kind;p=json.loads((d/'payload-final.json').read_text())
def guard():
 r=json.loads((A/'b1-curveof-native-normalized-correspondence-v183-result.json').read_text());assert r['status']=='succeeded' and r['result']['exit_code']==0
 q=json.loads((R/'curveof-native-review.json').read_text());assert q['correspondenceAccepted'] and q['completeExplicitXH3H5AndNineConstructorFieldsRetained'] and not q['newAssumptionsIntroduced']
 assert q['mappedNewDeclarationCount']==9 and q['sourceOnlyProofCount']==1 and len(q['constructorArgumentReports'])==9
 assert all(x['completeTYPEKernelEqual'] and x['strictPublicForallBinderInfoEqual'] and x['completeValueKernelEqual'] and not x['hasSorryAx'] and set(x['axioms'])<={'propext','Classical.choice','Quot.sound'} for x in q['reports'])
 s=q['sourceOnlyProofReport'];assert s['originalCompleteTYPEKernelCheckedIsProp'] and s['originalCompleteValueKernelCheckedAgainstTYPE'] and not s['targetConstantInvented'];assert set(s['valueAxioms'])<={'propext','Classical.choice','Quot.sound'}
 req=r.get('request',r['result']['snapshot'].get('manifest',{}));m=req.get('worktree_manifest',req)
 suffix='CurveOfCarrier' if kind=='carrier' else 'CurveOf';code=W/f'Definitions/Def_AbcAdaptation_Reference_Iut_Tripod_{suffix}.lean'
 assert m['input_hashes'][str(code)]==sha(code) and p['definition']==code.read_text()
 assert p['private'] is True and p['env']=='0df444a360eaa60ab8c11dca51a86af692955474'
if mode=='submit':
 guard();assert not(d/'publish-intent.json').exists() and not(d/'publish-submit.json').exists(),'Resolve existing publication intent before a new POST'
 if kind=='assembly':
  prior=json.loads((D/'carrier/published-item.json').read_text());assert prior['visibility']=='private';assert json.loads((D/'carrier/publication-validation.json').read_text())['allSubmittedFieldsExactlyReadBack']
 hits=api.request('/definitions?q='+urllib.parse.quote(p['definition_name'])+'&limit=100');save(d/'prior-name-search.json',hits);assert not any(x['definition_name']==p['definition_name'] for x in hits.get('definitions',[]))
 save(d/'publish-intent.json',{'stage':'intent-before-post','definitionName':p['definition_name'],'payloadSHA256':sha(d/'payload-final.json'),'private':True,'nativeReviewJob':'ci-018993-9b6adc45'})
 v=api.request('/submit-definition',p,method='POST');save(d/'publish-submit.json',v);save(d/'publish-journal.json',{'job_id':v['job_id'],'status':v['status']});print(json.dumps({'kind':kind,'job_id':v['job_id'],'status':v['status']}))
elif mode=='poll':
 j=json.loads((d/'publish-journal.json').read_text());v=api.request('/publish-jobs/'+j['job_id']);save(d/'publish-result.json',v);j['status']=v['status'];save(d/'publish-journal.json',j);print(json.dumps({'kind':kind,'job_id':j['job_id'],'status':v['status'],'error_message':v.get('error_message')},ensure_ascii=False))
 if v['status']=='PUBLISHED':
  item=api.request('/definitions/'+(v.get('definition_id') or v['theorem_id']));save(d/'published-item.json',item)
  for key in ['definition_name','definition_title','definition','natural_language_statement','source']:assert item[key]==p[key],key
  assert item['visibility']=='private' and item['mathlib_rev']==p['env']
  save(d/'publication-validation.json',{'allSubmittedFieldsExactlyReadBack':True,'private':True,'mathlib_rev':item['mathlib_rev']});print(json.dumps({'definition_id':item['definition_id'],'allFieldsExact':True}))
else:raise SystemExit('unknown mode')
