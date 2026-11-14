from pathlib import Path
import json,copy,ast,hashlib,importlib.util,shutil
sp=importlib.util.spec_from_file_location('unit','/tmp/p2m-northcott-ci-20261114.py');unit=importlib.util.module_from_spec(sp);sp.loader.exec_module(unit);ci=unit.ci;w=ci.w;b=ci.b;pre=unit.pre;urel='.local/adaptation/northcott-sourceproof-20261114/'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def run(*a,**kw):
 kw.setdefault('version','northcott-ascii-v1');return ci.run(*a,**kw)
def full_symbols():
 source='scripts/extract_sketch_info.lean';target='Theorems/Thm_AbcAdaptation_Tripod_northcottPolynomialWitness.lean';tag='rename-witness-symbols'
 q=copy.deepcopy(ci.base);q.update(task_type='full',target='module',parameters={'args':['--run',source,target,'AbcAdaptation.Tripod.Northcott']},expected_duration='60s',expected_memory='16GiB',worktree_manifest=ci.manifest(source));q['worktree_manifest']['symbol_source_sha256']=sha(w/target);q['idempotency_key']='p2m-northcott-symbols-v1-'+sha(w/target)[:20];ci.save(tag+'-request.json',q)
 p=b/(tag+'-submit.json')
 if p.exists():s=json.loads(p.read_text())
 else:s=ci.rpc('ci_submit',q);ci.save(p.name,s)
 print(json.dumps({'tag':tag,'job_id':s['job_id'],'status':'submitted'}),flush=True)
 while True:
  z=ci.rpc('ci_wait',{'job_id':s['job_id'],'timeout_seconds':20})
  if z['status'] not in ['queued','running','preparing_snapshot']:break
 z=ci.rpc('ci_result',{'job_id':s['job_id']});ci.save(tag+'-result.json',z);assert z['status']=='succeeded',z['result'].get('stderr');assert z['result']['exit_code']==0 and z['result']['snapshot']['workspace_mode']=='exclusive_worktree' and z['result']['snapshot']['snapshot_id'] is None;assert z['resources']['peak_rss_bytes']<=16*1024**3;assert z['result']['actual_arguments']==['lean']+q['parameters']['args']
 refs=[json.loads(l) for l in z['result']['stdout'].splitlines() if l.startswith('{')];ci.save('rename-witness-symbol-facts.json',refs);print(json.dumps({'tag':tag,'job_id':s['job_id'],'status':z['status'],'rss':z['resources']['peak_rss_bytes']}),flush=True);return refs
if __name__=='__main__':
 assert json.loads((b/'source-graph-leaf-result.json').read_text())['status']=='succeeded'
 tree=ast.parse(Path('/tmp/p2m-northcott-validation-20261114.py').read_text());syntax=next(ast.literal_eval(node.value) for node in tree.body if isinstance(node,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='syntax' for t in node.targets))
 sources=['Theorems/Thm_'+(pre+n).replace('.','_')+'.lean' for n in unit.new_names+['boundedDegreeFiniteness']]
 syntax=syntax.replace('FILES',', '.join(json.dumps(f,ensure_ascii=False) for f in sources)).replace('OUTPUT',urel+'rename-syntax-boundaries.json');(b/'ExtractRenameSyntax.lean').write_text(syntax)
 run('rename-syntax-leaf',urel+'ExtractRenameSyntax.lean')
 syntax_rows=json.loads((b/'rename-syntax-boundaries.json').read_text());refs=full_symbols()
 mapping={pre+'Northcott.norm_embedding_le_mulHeight₁':pre+'Northcott.norm_embedding_le_mulHeight_one',pre+'Northcott.mulHeight₁_gen_le':pre+'Northcott.mulHeight_one_gen_le'}
 edits={};before={}
 for old,new in mapping.items():
  f='Theorems/Thm_'+old.replace('.','_')+'.lean';raw=(w/f).read_bytes();before[f]=raw.decode();match=[r for r in syntax_rows if r['file']==f and r['nameText']==old.rsplit('.',1)[1]];assert len(match)==1;z=match[0]['nameRange'];edits.setdefault(f,[]).append({'start':z['start']['offset'],'end':z['end']['offset'],'replacement':new.rsplit('.',1)[1],'kind':'Lean AST declaration binding','original':old.rsplit('.',1)[1]})
 witness='Theorems/Thm_AbcAdaptation_Tripod_northcottPolynomialWitness.lean';raw=(w/witness).read_bytes();before[witness]=raw.decode()
 for r in refs:
  if r.get('kind')=='ref' and r['const'] in mapping:
   a,e=r['start']['offset'],r['end']['offset'];old=r['const'];text=raw[a:e].decode();assert text in [old,old.rsplit('.',1)[1]],text
   new=mapping[old] if text==old else mapping[old].rsplit('.',1)[1];edits.setdefault(witness,[]).append({'start':a,'end':e,'replacement':new,'kind':'Lean Stage2 resolved constant reference','original':text})
 assert sum(e['kind'].endswith('reference') for es in edits.values() for e in es)==2
 # Import commands are structured module names on exact complete import lines.
 for old,new in mapping.items():
  oldmod='Theorems.Thm_'+old.replace('.','_');newmod='Theorems.Thm_'+new.replace('.','_');offset=0;hits=[]
  for line in raw.splitlines(keepends=True):
   token=line.rstrip(b'\r\n')
   if token==('import '+oldmod).encode():hits.append((offset+7,offset+len(token)))
   offset+=len(line)
  assert len(hits)==1;aa,ee=hits[0];edits[witness].append({'start':aa,'end':ee,'replacement':newmod,'kind':'exact structured import module','original':oldmod})
 for f,es in edits.items():
  data=before[f].encode();spans=sorted(es,key=lambda x:x['start']);assert all(a['end']<=z['start'] for a,z in zip(spans,spans[1:]))
  for e in reversed(spans):
   assert data[e['start']:e['end']].decode()==e['original'];data=data[:e['start']]+e['replacement'].encode()+data[e['end']:]
  (w/f).write_bytes(data)
 for old,new in mapping.items():
  oldpath=w/('Theorems/Thm_'+old.replace('.','_')+'.lean');newpath=w/('Theorems/Thm_'+new.replace('.','_')+'.lean');assert not newpath.exists();oldpath.rename(newpath)
 checks=w/'Solutions/Checks_TripodNorthcottSourceProofs.lean';text=checks.read_text();old_check=text
 for old,new in mapping.items():
  line='#print axioms '+old;assert text.count(line)==1;text=text.replace(line,'#print axioms '+new)
 checks.write_text(text)
 ci.save('ascii-renaming.json',{'cause':'Prove2Me conservative ASCII theorem-name rule, references/upload_full_project.md:87','mapping':mapping,'source_edits':edits,'original_sources':before,'original_checks':old_check,'all_references_compiler_resolved':True,'no_mathematical_statement_change':True,'deleted_old_active_module_paths':list(before)[:2]})
 # Only affected proof modules are rebuilt; unchanged Definitions, coefficient and root proofs retain their receipts.
 for old,new in mapping.items():
  f='Theorems/Thm_'+new.replace('.','_')+'.lean';tag=new.removeprefix(pre);run(tag+'-leaf',f);run(tag+'-artifact',f,artifact=True)
 for n in ['northcottPolynomialWitness','boundedDegreeFiniteness']:
  f='Theorems/Thm_'+(pre+n).replace('.','_')+'.lean';run('ascii-'+n+'-leaf',f,memory='6GiB');run('ascii-'+n+'-artifact',f,artifact=True)
 run('ascii-closed-axioms-review','Solutions/Checks_TripodNorthcottSourceProofs.lean','review',memory='6GiB')
 run('ascii-source-graph-leaf',urel+'ExtractNorthcottProofGraph.lean',memory='7GiB')
 print('Compiler-resolved ASCII renaming and affected-module revalidation passed.',flush=True)
