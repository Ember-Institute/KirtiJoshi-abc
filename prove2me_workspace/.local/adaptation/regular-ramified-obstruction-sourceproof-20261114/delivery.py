from pathlib import Path
import json,hashlib,math,re,sys,importlib.util,shutil
r=Path('/home/admin-wsl/Coq/abc');w=r/'prove2me_workspace';b=w/'.local/adaptation/regular-ramified-obstruction-sourceproof-20261114';u=str(b.relative_to(w))+'/';root='e33ff731-60a7-43ef-87ae-c12aeba23cb5';pre='AbcAdaptation.Tripod.Fermat.Proper.';env='0df444a360eaa60ab8c11dca51a86af692955474';pin='9ce4d3f793d3bc831f2fc7214b7dbad90ea012d8';target=pre+'noncriticalRegularRamifiedDerivNotMem';targetid='0dd193b0-3f70-4ec3-a54a-5c892c86bb01';parent=pre+'noncriticalRamificationFinite';parentid='9ea35172-fd58-4868-84a0-4d672a037da2'
def read(n):return json.loads((b/n).read_text())
def save(n,x):(b/n).write_text(json.dumps(x,ensure_ascii=False,indent=2)+'\n')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def prose(rows):return '\n\n'.join('**'+title+'**\n\n'+'\n\n'.join('`'+row['declaration']+'`\n\n'+row[lang] for row in rows) for lang,title in [('en','English'),('zh_Hans','简体中文'),('ja','日本語')])
def bind_readbacks():
 graph=[json.loads(l) for l in (b/'decl_graph.jsonl').read_text().splitlines() if l];owners={(row['module'],row.get('userName',row['name'])):row for row in graph if row['startLine']>0};blind=Path('/tmp/p2m-regular-ramified-obstruction-blind-20261114/canonical-readbacks-draft.json');shutil.copy2(blind,b/'blind-readbacks-original.json');rb=json.loads(blind.read_text());inputs={};quote=(b/'mochizuki-quotation.md').read_text().strip()
 for row in rb['declarations']:
  key=(row['module'],row['userName']);gr=owners[key];rel=gr['module'].replace('.','/')+'.lean';row['path']=rel;inputs[rel]=sha(w/rel);row['source_file_sha256']=inputs[rel];row['compiler_name']=gr['name'];row['compiler_source_span']={'startLine':gr['startLine'],'endLine':gr['endLine']};row['elaboratedType']=gr['elaboratedType'];row['final_compatibility_adaptations']='Current compiled owner and source hash supersede the historical draft: exact imports plus canonical Algebra/Module and derived PreValuationRing instance wiring; full statement preserved.';row['en_source_quote']=quote;row['en_source_quote_ledger_binding']={'file':'mochizuki-quotation.md','sha256':sha(b/'mochizuki-quotation.md'),'role':'Geometric context only; exact local derivative and valuation results are separately pinned source proofs.'}
 formulas=json.loads(Path('/tmp/p2m-obstruction-display-formulas-20261114.json').read_text())
 for row in rb['declarations']:
  gr=owners[(row['module'],row['userName'])];lines=(w/row['path']).read_text().splitlines();span='\n'.join(lines[gr['startLine']-1:gr['endLine']]);row['source_span_original_canonical_draft']=row['source_span'];row['source_span']={'start_line':gr['startLine'],'end_line':gr['endLine'],'sha256':hashlib.sha256(span.encode()).hexdigest(),'text':span};row['line']=gr['startLine'];row['kernel_name']=gr['name'];row['identity_key']={'path':row['path'],'userName':row['userName']};row['status']='sourceproof_kernel_checked; platform verification recorded separately'
  if row['visibility']=='public' and row['declaration'].rsplit('.',1)[1] in ['exists_eq_div','exists_pow_mul_derivAlong_mem_integralClosure']:
   row['semantic_reuse']['proof_body_changed']=True;row['semantic_reuse']['final_change']='Explicit existing canonical instance wiring documented in source-proof-provenance.json; generalized theorem type unchanged.'
  if row['visibility']=='public':
   formula=formulas[row['declaration'].rsplit('.',1)[1]]
   for lang in ['en','zh_Hans','ja']:
    display=formula.replace('\\text{irreducible}','\\text{不可约}' if lang=='zh_Hans' else '\\text{既約}' if lang=='ja' else '\\text{irreducible}')
    row[lang]+='\n\n$$\n'+display+'\n$$'
 rb['input_file_sha256']=inputs;rb['compiler_bound']=True;save('final-readbacks.json',rb);return rb

def prepare():
 val=read('delivery-validation.json');assert val['passed'];dag=read('canonical-import-dag.json');names=dag['topological_order'];formals=read('compiler-formals.json');rb=bind_readbacks();rows=rb['declarations'];quote=(b/'mochizuki-quotation.md').read_text().strip();new=[n for n in names if n!=target];common='Shinichi Mochizuki, Noncritical Belyi Maps, Theorem 2.5, printed pp.5–6, https://www.kurims.kyoto-u.ac.jp/~motizuki/Noncritical%20Belyi%20Maps.pdf . The checked original quotation gives geometric context only. The exact local derivative obstruction and its complete auxiliary proofs are independently adapted from lana-agents/belyi at '+pin+', CurveDeriv/Basic.lean, Local.lean, Order.lean and CurveField/Extension.lean, NoncriticalFinite.lean. Actual formally etale derivation, full residue fields, valuation rings and normalized ramification indices are retained. Source copyright, author notices and Apache-2.0 release headers are retained; the included standard license text is separately sourced, not claimed to be a fetched upstream root LICENSE. No new hypothesis, Open debt, Belyi/Iut runtime import or global 3.12 conclusion is introduced. '
 rel='Definitions/Def_FermatCurveFieldUniformizer.lean';selected=[z for z in rows if z['path']==rel];assert len(selected)==1
 save('def-FermatCurveFieldUniformizer-payload.json',{'definition_name':'FermatCurveFieldUniformizer','definition_title':'A chosen actual uniformizer at each curve-field place','definition':(w/rel).read_text(),'natural_language_statement':quote+'\n\n'+prose(selected),'source':common+'Complete actual choice from Place.exists_ord_eq_one; this Definition supplies no Open theorem.','env':env,'private':True,'tags':['abc-conjecture','arithmetic-geometry']})
 problems=[]
 for name in new:
  fr=formals[name];selected=[z for z in rows if z['declaration']==name and z['visibility']=='public'];assert len(selected)==1;problems.append({'theorem_name':name,'theorem_title':name.rsplit('.',1)[1].replace('_',' '),'formal_statement':fr['formal_statement'],'preamble':fr['preamble'],'natural_language_statement':quote+'\n\n'+prose(selected),'source':common+'Source declaration: '+name.rsplit('.',1)[1]+'.','tags':['abc-conjecture','arithmetic-geometry']})
 save('obstruction-children-payload.json',{'problems':problems,'env':env,'private':True})
 solutions=read('solution-inventory.json');deps={z['theorem_name']:z['direct_node_dependencies'] for z in dag['nodes'] if z['direct_node_dependencies']};plan={'unit':'regular-ramified-obstruction-sourceproof-20261114','unit_relative':u,'root_id':root,'parent_name':target,'parent_id':targetid,'mathlib_rev':env,'visibility':'private','definitions':[{'name':'FermatCurveFieldUniformizer','payload':'def-FermatCurveFieldUniformizer-payload.json','source':rel,'source_sha256':sha(w/rel)}],'new_mathematical_nodes':new,'existing_child_matches':{},'solutions':solutions,'true_dependencies':deps}
 save('delivery-plan.json',plan)
 for sol in solutions:
  name=sol['name'];tag='verify-'+name.removeprefix('AbcAdaptation.Tripod.').replace('.','_');selected=[z for z in rows if z['path']==next(z for z in dag['nodes'] if z['theorem_name']==name)['file']];explanation=quote+'\n\n'+prose(selected)+'\n\n'+common;save(tag+'-request-draft.json',{'theorem_name':name,'proof_type':'prove','file':sol['source'],'source_sha256':sol['source_sha256'],'explanation':explanation})
 selected=[z for z in rows if z['declaration']==target and z['visibility']=='public'];save('parent-metadata-patch-draft.json',{'natural_language_statement':quote+'\n\n'+prose(selected),'source':common+'The exact existing obstruction is supplied by the complete source regular-order theorem and its full private source closure.'})
 val['readbacks_sha256']=sha(b/'final-readbacks.json');save('delivery-validation.json',val);return preflight()

def preflight(delivery=None):
 val=read('delivery-validation.json');plan=read('delivery-plan.json');formals=read('compiler-formals.json');dag=read('canonical-import-dag.json');names=dag['topological_order'];assert plan['new_mathematical_nodes']==[n for n in names if n!=target]
 for rel,h in val['source_hashes'].items()|val['solution_hashes'].items():assert sha(w/rel)==h,rel
 for f,k in [('decl_graph.jsonl','declaration_graph_sha256'),('compiler-formals.json','compiler_formals_sha256'),('syntax-boundaries.json','syntax_boundaries_sha256'),('final-readbacks.json','readbacks_sha256')]:assert sha(b/f)==val[k]
 assert val['passed'] and val['exact_existing_target_type_equal'] and val['all_new_formals_type_equal'] and read('existing-types-equal.json') is True
 sources=set(val['source_hashes']);assert sources=={'Definitions/Def_FermatCurveFieldUniformizer.lean'}|{n['file'] for n in dag['nodes']}
 checks=val['compiler_checks'];modes=set()
 for c in checks:
  receipt=read(c['tag']+'-result.json');q=receipt['request'];rs=receipt['result'];v=receipt['resources'];assert receipt['status']=='succeeded' and rs['exit_code']==0 and q['exclusive'] and q['workspace']==str(w);assert q['worktree_manifest']['source_sha256']==sha(w/c['source']);assert rs['snapshot']['workspace_mode']=='exclusive_worktree' and rs['snapshot']['snapshot_id'] is None;expected=['lean']+([c['source'],'-o','.lake/build/lib/lean/'+c['source'][:-5]+'.olean'] if c['artifact'] else [c['source']]);assert rs['actual_arguments']==expected;assert 'sorryAx' not in rs['stdout']+rs['stderr'];assert v['peak_rss_bytes']<=16*1024**3
  if c['review']:
   assert rs['review']['passed']
   for rel,h in val['source_hashes'].items():assert q['worktree_manifest']['input_hashes'][rel]==h
  if v.get('cpu_time_seconds') is not None:assert math.isclose(v['cpu_time_seconds'],v['cpu_user_seconds']+v['cpu_system_seconds'],abs_tol=.1)
  modes.add((c['source'],c['artifact'],c['review']))
 for rel in sources:assert (rel,False,False) in modes and (rel,True,False) in modes
 for rel in val['solution_hashes']:assert (rel,False,False) in modes
 assert any(c['review'] and c['source'].endswith('AuditAllDefinitions.lean') for c in checks);assert any(c['review'] and c['source'].endswith('ProductionGates.lean') for c in checks)
 graph=[json.loads(l) for l in (b/'decl_graph.jsonl').read_text().splitlines() if l];by={z['name']:z for z in graph};rows=read('final-readbacks.json')['declarations'];assert len(rows)==45 and len({z['compiler_name'] for z in rows})==45
 for z in rows:
  gr=by[z['compiler_name']];assert z['elaboratedType']==gr['elaboratedType'] and z['compiler_source_span']=={'startLine':gr['startLine'],'endLine':gr['endLine']};assert z['path']==gr['module'].replace('.','/')+'.lean';assert z['source_file_sha256']==sha(w/z['path']);assert all(z[k].strip() for k in ['en','zh_Hans','ja'])
 visited=set();todo=[target]
 while todo:
  name=todo.pop()
  if name in visited:continue
  visited.add(name)
  if name not in by:assert not name.startswith(('AbcAdaptation.','_private.')),name;continue
  z=by[name];assert z['kind']!='axiom';todo+=z['typeDeps']+z['valueDeps']
 assert {z['compiler_name'] for z in rows}<=visited,'Unconsumed source output'
 for n in dag['nodes']:
  seen=set();todo=by[n['theorem_name']]['typeDeps']+by[n['theorem_name']]['valueDeps'];actual=set()
  while todo:
   name=todo.pop()
   if name in seen:continue
   seen.add(name)
   if name in names:actual.add(name);continue
   z=by.get(name)
   if z and z['module']==n['module']:todo+=z['typeDeps']+z['valueDeps']
  assert actual==set(n['direct_node_dependencies']),(n['theorem_name'],actual)
 for sol in plan['solutions']:
  text=(w/sol['source']).read_text();assert not re.search(r'\b(sorry|admit|axiom|unsafe)\b',text);imports=[l[7:] for l in text.splitlines() if l.startswith('import Theorems.')];assert set(imports)==set(sol['theorem_imports']);assert ('Theorems.Thm_'+sol['name'].replace('.','_')) not in imports
 for p in read('obstruction-children-payload.json')['problems']:
  assert p['theorem_name'].isascii();assert p['formal_statement']==formals[p['theorem_name']]['formal_statement'] and p['preamble']==formals[p['theorem_name']]['preamble'];assert not any(l.startswith('import Theorems.') for l in p['preamble'].splitlines())
 for f,h in read('original-source-consumer.json')['reference_hashes'].items():assert sha(b/'reference'/f)==h
 assert val['new_open_mathematical_obligations']==0
 return val

if __name__=='__main__':
 if len(sys.argv)>1 and sys.argv[1]=='prepare':prepare();print('Obstruction strong preflight passed.',flush=True)
