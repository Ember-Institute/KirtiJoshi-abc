from pathlib import Path
import ast, hashlib, importlib.util, json, sys, time, urllib.request, urllib.error, uuid

r=Path('/home/admin-wsl/Coq/abc');w=r/'prove2me_workspace';b=w/'.local/adaptation/canonical-cusp-split-20261114'
u='.local/adaptation/canonical-cusp-split-20261114/';pre='AbcAdaptation.Tripod.Fermat.Proper.'
parent=pre+'canonicalCuspPolarLinearEquivalence'
children=[pre+n for n in ['canonicalDifferentialChange', 'belyiCanonicalCuspCoefficientIdentity']]
source='Theorems/Thm_'+parent.replace('.','_')+'.lean'
helper='Solutions/Source_FermatCanonicalCuspComposition.lean'
sol=u+'Solution_canonicalCuspPolarLinearEquivalence.lean'
ENV='0df444a360eaa60ab8c11dca51a86af692955474';ROOT='e33ff731-60a7-43ef-87ae-c12aeba23cb5'
def read(n):return json.loads((b/n).read_text())
def save(n,x):(b/n).write_text(json.dumps(x,ensure_ascii=False,indent=2)+'\n')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def child_path(n):return 'Theorems/Thm_'+n.replace('.','_')+'.lean'
def source_child_statement(name):
    path=child_path(name);raw=(w/path).read_bytes()
    matches=[z for z in read('syntax-boundaries.json') if z['file']==path and z['nameText']==name.removeprefix(pre)]
    assert len(matches)==1;span=matches[0];start=span['declStart']['offset']
    if span['docstring'] and span['docstring']['start']['offset']==start:start=span['docstring']['end']['offset']
    ns,ne=span['nameRange']['start']['offset'],span['nameRange']['end']['offset']
    assert raw[ns:ne].decode()==name.removeprefix(pre)
    header=(raw[start:ns]+name.encode()+raw[ne:span['valStart']['offset']]).decode().strip()
    assert header.startswith('theorem '+name+' ')
    return header+' := by sorry'
def child_alias(name,index,item):
    header=item['formal_statement'].replace('theorem '+name,'theorem PlatformChildType'+str(index),1).removesuffix(' := by sorry')
    arguments='M hDVR hRF φ hφ K' if index==0 else 'M hDVR hRF φ hφ hfin'
    return header+' := by\n  exact '+name+' '+arguments+'\n'
def bind():
    graph=[json.loads(l) for l in (b/'decl_graph.jsonl').read_text().splitlines() if l]
    out=[]
    for row in read('normalized-readbacks.json')['declarations']:
        assert sha(Path(row['path']))==row['sha256']
        path=helper if row['userName'] in [pre+'canonicalCuspPolarLinearEquivalence_of_children'] else child_path(row['userName'])
        found=[z for z in graph if z['module']==path[:-5].replace('/','.') and z['userName']==row['userName'] and z['startLine']>0]
        assert len(found)==1,(row['userName'],len(found));z=found[0]
        out.append({'declaration':z['name'],'userName':z['userName'],'path':path,'module':z['module'],'source_sha256':sha(w/path),'compiler_type':z['elaboratedType'],'source_span':{'start_line':z['startLine'],'end_line':z['endLine']},'blind_original_path':row['path'],'blind_original_sha256':row['sha256'],'original_packet':row['original_packet'],'original_packet_sha256':sha(b/row['original_packet']),**row['statements'],'proof_notes':row.get('proof_notes'),'quotation':None})
    assert len(out)==4;save('final-readbacks.json',{'declarations':out,'blind_readback':True,'compiler_bound':True,'paper_quotations_separate':True})
def generate():
    bind();graph=[json.loads(l) for l in (b/'decl_graph.jsonl').read_text().splitlines() if l];index={z['name']:z for z in graph}
    reached=set();todo=[parent]
    while todo:
        name=todo.pop()
        if name in reached:continue
        reached.add(name);row=index.get(name)
        if row:todo+=row['typeDeps']+row['valueDeps']
    authored={z['declaration'] for z in read('final-readbacks.json')['declarations']};assert authored<=reached
    save('consumer-closure.json',{'all_authored_declarations_consumed':True,'declarations':sorted(authored),'root':parent,'actual_open_children':children})
    formal=read('platform-before-parent.json')['formal_statement'];assert formal.startswith('theorem '+parent+' ') and formal.endswith(' := by sorry')
    exact=formal.replace('theorem '+parent,'theorem solution',1).removesuffix(' := by sorry')
    code=''.join('import '+child_path(n)[:-5].replace('/','.')+'\n' for n in children)+(w/helper).read_text().rstrip()+'\n\n'+exact+' := by\n  intro N M hDVR hRF φ hφ hfin K\n  exact '+pre+'canonicalCuspPolarLinearEquivalence_of_children\n    '+children[0]+'\n    '+children[1]+'\n    M hDVR hRF φ hφ hfin K\n'
    assert 'sorry' not in code and 'import '+source[:-5].replace('/','.') not in code and 'import Solutions.' not in code
    (w/sol).write_text(code)
    items=[]
    for name in children:
        path=child_path(name);imports='\n'.join(line for line in (w/path).read_text().splitlines() if line.startswith('import '))
        assert imports and all(line.startswith('import Definitions.') for line in imports.splitlines())
        items.append({'theorem_name':name,'preamble':imports+'\n\nset_option autoImplicit false\n\nopen scoped Classical\nopen AbcAdaptation.Tripod.Fermat.Proper','formal_statement':source_child_statement(name)})
    save('upload-problem-items.json',items)
    for i,item in enumerate(items):
        (b/('UploadType'+str(i)+'.lean')).write_text(item['preamble']+'\n\n'+item['formal_statement']+'\n')
    audit='import Lean\n'+code+'\nopen AbcAdaptation.Tripod.Fermat.Proper\n'+formal.replace('theorem '+parent,'theorem PlatformOriginalParentType',1).removesuffix(' := by sorry')+' := solution\n'
    for i,item in enumerate(items):audit+='\n'+child_alias(item['theorem_name'],i,item)
    audit+='''
open Lean
run_meta do
  let original ← getConstInfo `PlatformOriginalParentType
  let solution ← getConstInfo `solution
  unless ← Lean.Meta.isDefEq original.type solution.type do throwError "Original parent type differs"
  let axs ← collectAxioms `solution
  unless axs.contains `sorryAx do throwError "Missing expected open child dependency"
  for ax in axs do
    unless #[`propext, `Classical.choice, `Quot.sound, `sorryAx].contains ax do throwError "Unexpected reduction axiom {ax}"
  let pairs : Array (Name × Name) := PAIRS
  let mut rows : Array Json := #[]
  for (name, check) in pairs do
    let a ← getConstInfo name
    let t ← getConstInfo check
    unless ← Lean.Meta.isDefEq a.type t.type do throwError "Uploaded child type differs: {name}"
    rows := rows.push (Json.mkObj [("name",toJson name.toString),("type",Json.str (← Lean.Meta.ppExpr a.type).pretty)])
  IO.FS.writeFile "OUTPUT" (Json.pretty (Json.mkObj [("original_parent_type_equal",Json.bool true),("solution_type",Json.str (← Lean.Meta.ppExpr solution.type).pretty),("axioms",toJson (axs.map toString)),("child_types",Json.arr rows)]))
'''.replace('PAIRS','#['+','.join('(`'+name+', `PlatformChildType'+str(i)+')' for i,name in enumerate(children))+']').replace('OUTPUT',u+'type-audit.json')
    (b/'AuditSolution.lean').write_text(audit)
    save('solution-source-closure.json',{'source':sol,'source_sha256':sha(w/sol),'closed_source_sha256':sha(w/helper),'inlined_source_copied_verbatim':True,'only_open_imports':children,'new_definition_nodes':[],'original_parent_type_verbatim':True})
def checked(tag,path,review=False,expected_sorry=False):
    z=read(tag+'-result.json');q=z['request'];rs=z['result']
    assert z['status']=='succeeded' and rs['exit_code']==0,tag
    assert q['exclusive'] and q['workspace']==str(w) and q['parameters']=={'source':path},tag
    assert q['worktree_manifest']['source_sha256']==sha(w/path),tag
    assert rs['actual_arguments']==['lean',path] and rs['snapshot']['workspace_mode']=='exclusive_worktree' and rs['snapshot']['snapshot_id'] is None,tag
    assert ('sorryAx' in rs['stdout'])==expected_sorry,tag
    if review:assert rs['review']['passed'],tag
    return z
def preflight():
    receipts=[checked('composer-source-leaf',helper)]+[checked(n.removeprefix(pre)+'-leaf',child_path(n)) for n in children]+[checked('canonicalCuspPolarLinearEquivalence-leaf',source),checked('closed-axioms-review','Solutions/Checks_FermatCanonicalCuspClosed.lean',True),checked('reduction-axioms-leaf','Solutions/Checks_FermatCanonicalCuspReduction.lean',expected_sorry=True),checked('source-graph-leaf',u+'ExtractCanonicalCuspGraph.lean'),checked('syntax-leaf',u+'ExtractCanonicalCuspSyntax.lean'),checked('all-constants-leaf',u+'AuditAllConstants.lean'),checked('solution-leaf',sol),checked('types-leaf',u+'AuditSolution.lean'),checked('production-gates-review',u+'ProductionGates.lean',True)]
    receipts += [checked('upload-type-'+str(i)+'-leaf',u+'UploadType'+str(i)+'.lean') for i in range(2)]
    for i,item in enumerate(read('upload-problem-items.json')):
        assert (b/('UploadType'+str(i)+'.lean')).read_text()==item['preamble']+'\n\n'+item['formal_statement']+'\n'
    audit=read('type-audit.json');assert audit['original_parent_type_equal'] and 'sorryAx' in audit['axioms'] and set(audit['axioms'])<={'propext','Classical.choice','Quot.sound','sorryAx'}
    graph={z['name']:z for z in map(json.loads,(b/'decl_graph.jsonl').read_text().splitlines()) if z}
    assert len(audit['child_types'])==2 and {z['name'] for z in audit['child_types']}==set(children)
    # The audited Lean code reparses the exact upload strings, then checks Meta.isDefEq.
    # Pretty-print options differ from the graph extractor; string formatting is not a type check.
    audited=(b/'AuditSolution.lean').read_text();items=read('upload-problem-items.json')
    for i,item in enumerate(items):
        name=item['theorem_name'];assert item['formal_statement']==source_child_statement(name)
        assert 'open scoped Classical' in item['preamble'] and 'open AbcAdaptation.Tripod.Fermat.Proper' in item['preamble']
        annotation=child_alias(name,i,item)
        assert annotation in audited
        assert '(`'+name+', `PlatformChildType'+str(i)+')' in audited
    assert 'unless ← Lean.Meta.isDefEq a.type t.type do throwError' in audited
    save('type-roundtrip-evidence.json',{'both_uploaded_child_types_definitionally_equal':True,'proof':'Successful types-leaf receipt executes Meta.isDefEq after parsing exact upload annotations','audited_source_sha256':sha(b/'AuditSolution.lean'),'graph_source':'decl_graph.jsonl','serialization':'Compiler parser byte ranges retain exact original binders, P.1 projections and scope; only theorem name is qualified','pretty_print_types_used_for_upload':False,'no_mathematical_input_changed':True})
    axs=read('all-module-axioms.json');assert len(axs)>=4
    for z in axs:
        assert set(z['axioms'])<={'propext','Classical.choice','Quot.sound'}|({'sorryAx'} if z['open_dependency_expected'] else set())
        assert ('sorryAx' in z['axioms'])==z['open_dependency_expected']
    rb=read('final-readbacks.json')['declarations'];assert len(rb)==4 and all(z['source_sha256']==sha(w/z['path']) for z in rb)
    assert read('consumer-closure.json')['all_authored_declarations_consumed']
    own=[helper,source]+[child_path(n) for n in children]+['Solutions/Checks_FermatCanonicalCuspClosed.lean','Solutions/Checks_FermatCanonicalCuspReduction.lean']
    inputs=read('production-gates-review-result.json')['request']['worktree_manifest']['input_hashes'];assert all(inputs[f]==sha(w/f) for f in own)
    assert read('solution-source-closure.json')['source_sha256']==sha(w/sol) and 'sorry' not in (w/sol).read_text()
    save('delivery-validation.json',{'passed':True,'original_parent_type_equal':True,'both_child_types_equal':True,'readbacks':4,'closed_helper_and_conditional_composer_standard_axioms_only':True,'reduction_has_exactly_expected_open_proof_debt':children,'compiler_checks':[z['job_id'] for z in receipts],'owned_source_hashes':{f:sha(w/f) for f in own}})
def prose(rows):
    return '\n\n'.join('**'+title+'**\n\n'+'\n\n'.join('`'+z['userName']+'`\n\n'+z[lang] for z in rows) for lang,title in [('en','English'),('zh_Hans','简体中文'),('ja','日本語')])
def publish():
    preflight();spec=importlib.util.spec_from_file_location('api',w/'.local/abc-item/api.py');api=importlib.util.module_from_spec(spec);spec.loader.exec_module(api)
    assert api.base=='https://prove2.me/api/v1'
    context=globals()|{'api':api};protocol=(w/'.local/adaptation/platform-tripod-20261113/executed-platform-publish.py').read_text()
    for node in ast.parse(protocol).body:
        if isinstance(node,ast.FunctionDef) and node.name in ['publish','verify']:exec(compile(ast.Module(body=[node],type_ignores=[]),'<established-protocol>','exec'),context)
    rb=read('final-readbacks.json')['declarations'];quote=(b/'quotation.md').read_text().strip()
    common='Shinichi Mochizuki, Arithmetic Elliptic Curves in General Position, February 2009, Theorem 2.1, pp.11–12: canonical sheaf, three-cusp divisor and log-canonical pullback context. Official PDF https://www.kurims.kyoto-u.ac.jp/~motizuki/Arithmetic%20Elliptic%20Curves%20in%20General%20Position.pdf , SHA256 b9dc115af61dca7fe434332ebafddf6a376a9e2926dad4e1ea2dcc0d2441f768. The paper quotation is parent context; it does not state the exact arbitrary-transcendental differential-change lemma or the explicit coefficient formula verbatim. Exact formal sources: Belyi/CurveField/Canonical.lean:144,159 and BelyiRelation.lean:85 at 9ce4d3f793d3bc831f2fc7214b7dbad90ea012d8; derivative chain/reciprocal identities in CurveDeriv/Basic.lean:209,214 and full order formulas in CurveDeriv/Order.lean:61,83 and CurveField/RamIdx.lean:237,257. All source hashes and Apache-2.0 notices retained. Every actual proper place including poles, supplied canonical divisor and cusp-finiteness proof, and original quantifier is retained. No new Definition, constant-field law, source-law field, extra geometric assumption or upstream runtime import. Both exact source child proofs remain Open.'
    items=read('upload-problem-items.json');titles=['Change of canonical differential along a transcendental function','Belyi differential and cusp coefficient identity at every proper place']
    for item,title in zip(items,titles):
        selected=[z for z in rb if z['declaration']==item['theorem_name']];assert len(selected)==1
        item.update(theorem_title=title,natural_language_statement=quote+'\n\n'+prose(selected),source=common,tags=['abc-conjecture','arithmetic-geometry'])
    tag='canonical-cusp-children';payload={'problems':items,'env':ENV,'private':True}
    if (b/(tag+'-submit.json')).exists():assert read(tag+'-payload.json')==payload
    else:
        assert not (b/(tag+'-publication-requested.json')).exists(),'Reconcile missing publication receipt before retry'
        save(tag+'-publication-requested.json',{'endpoint':'/submit-problem','payload':payload})
    published=context['publish'](tag,'/submit-problem',payload);assert len(published)==2
    ids={z['theorem_name']:z['theorem_id'] for z in published};assert set(ids)==set(children);save('published-child-ids.json',ids)
    ident=read('target-id.json')['id'];before=read('platform-before-parent.json');current=api.request('/theorems/'+ident)
    assert current['formal_statement']==before['formal_statement'] and current['visibility']=='private' and current['mathlib_rev']==ENV
    selected=[z for z in rb if z['declaration']==parent];assert len(selected)==1
    explanation=quote+'\n\n'+prose(selected)+'\n\n'+common+' The reduction obtains q from the exact differential-change child and takes r=(phi*(phi-1))*q. Transcendence proves phi and phi-1 nonzero; q is nonzero by the child statement. Only after these checks does the proof add their orders. The second child supplies the exact Belyi coefficient identity at every proper place. The principal sign remains positive. Both mathematical child proofs are still Open.'
    assert len(explanation)<=50000;tag='reduce-parent';request={'theorem_id':ident,'proof_type':'prove','file':sol,'source_sha256':sha(w/sol),'explanation':explanation}
    if (b/(tag+'-verify-submit.json')).exists():assert read(tag+'-verify-request.json')==request
    else:
        assert not (b/(tag+'-verification-requested.json')).exists(),'Reconcile missing verification receipt before retry'
        save(tag+'-verification-requested.json',request)
    result=context['verify'](tag,ident,sol,explanation);assert result['status']=='SKETCH_ACCEPTED'
    patch={'natural_language_statement':quote+'\n\n'+prose(selected),'source':common};save('parent-metadata-patch-request.json',patch)
    current=api.request('/theorems/'+ident)
    if not all(current.get(k)==v for k,v in patch.items()):save('parent-metadata-patch-response.json',api.request('/theorems/'+ident,patch,'PATCH'))
    for name,tid in [(parent,ident)]+list(ids.items()):
        z=api.request('/theorems/'+tid);assert z['theorem_name']==name and z['status']=='Open' and z['visibility']=='private' and z['mathlib_rev']==ENV
        if name==parent:
            assert z['formal_statement']==before['formal_statement'] and all(z[k]==v for k,v in patch.items());save('platform-after-parent.json',z)
        else:
            expected=next(item for item in items if item['theorem_name']==name)
            assert z['formal_statement']==expected['formal_statement'] and z['preamble']==expected['preamble']
            assert z['natural_language_statement']==expected['natural_language_statement'];save('platform-after-'+name.removeprefix(pre)+'.json',z)
    sys.path.insert(0,str(w/'.local/adaptation/northcott-sourceproof-20261114'));from graph_completion import fetch_complete_math_graph
    graph=fetch_complete_math_graph(api,ROOT,save,'root-graph-after');save('root-graph-after.json',graph)
    mathematical={z['theorem_id']:z for z in graph['nodes'] if z['node_type']=='theorem' and z['status']!='Definition'}
    sketches=[z for z in graph['nodes'] if z['node_type']=='sketch' and z['parent_theorem_id']==ident and z['submission_id']==result['id']]
    assert len(sketches)==1 and sketches[0]['status']=='SKETCH_ACCEPTED'
    actual={e['source'] for e in graph['edges'] if e['kind']=='sketch' and e['target']==sketches[0]['node_id'] and e['source'] in mathematical}
    assert actual==set(ids.values());assert mathematical[ident]['status']=='Open' and mathematical[ROOT]['status']=='Open'
    save('direct-graph-evidence.json',{'parent_id':ident,'submission_id':result['id'],'actual_child_ids':sorted(actual),'expected_child_ids':sorted(ids.values()),'both_children_open':True,'no_new_definition':True,'parent_and_root_open':True})
    leaves=[]
    while True:
        z=api.request('/theorems/'+ROOT+'/open-leaves?limit=50&offset='+str(len(leaves)));save('root-frontier-after-page-'+str(len(leaves))+'.json',z);leaves+=z['open_leaves']
        if len(leaves)>=z['total']:break
    assert len(leaves)==z['total'];save('root-frontier-after.json',{'open_leaves':leaves,'total':z['total'],'all_pages_fetched':True})
    print('Exact two-child reduction SKETCH_ACCEPTED; both children, parent and root remain Open.',flush=True)
if __name__=='__main__':{'bind':bind,'generate':generate,'preflight':preflight,'publish':publish}[sys.argv[1]]()
