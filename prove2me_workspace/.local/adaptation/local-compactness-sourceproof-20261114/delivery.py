from pathlib import Path
import ast, hashlib, importlib.util, json, sys, time, urllib.request, urllib.error, uuid

r=Path('/home/admin-wsl/Coq/abc');w=r/'prove2me_workspace';b=w/'.local/adaptation/local-compactness-sourceproof-20261114'
u='.local/adaptation/local-compactness-sourceproof-20261114/';pre='AbcAdaptation.Tripod.Fermat.Proper.'
target=pre+'localCompactness';dependencies=[]
source='Theorems/Thm_'+target.replace('.','_')+'.lean'
helpers=['Solutions/Source_'+n+'.lean' for n in ['FermatLocalSequence','FermatLocalProjectiveConvergence','FermatLocalValuedPlace','FermatLocalLimitValuation','FermatLocalCompactnessBridge','FermatLocalCompactness']]
sol=u+'Solution_localCompactness.lean'
ENV='0df444a360eaa60ab8c11dca51a86af692955474';ROOT='e33ff731-60a7-43ef-87ae-c12aeba23cb5'
def read(n):return json.loads((b/n).read_text())
def save(n,z):(b/n).write_text(json.dumps(z,ensure_ascii=False,indent=2)+'\n')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def generate():
    graph=[json.loads(l) for l in (b/'decl_graph.jsonl').read_text().splitlines() if l.strip()]
    rows={z['name']:z for z in graph};reached=set();todo=[target]
    while todo:
        n=todo.pop()
        if n in reached:continue
        reached.add(n);z=rows.get(n)
        if z:todo+=z['typeDeps']+z['valueDeps']
    helpermods={f[:-5].replace('/','.') for f in helpers}
    hs=[z for z in graph if z['module'] in helpermods and z['startLine']>0]
    # Include registered instances as roots; their use may disappear by elaboration.
    for row in hs:
        if row['isInstance']:
            todo=[row['name']]
            while todo:
                n=todo.pop()
                if n in reached:continue
                reached.add(n);info=rows.get(n)
                if info:todo+=info['typeDeps']+info['valueDeps']
    assert len(hs)>=50
    save('helper-consumption.json',{'helpers':[{'name':z['name'],'kind':z['kind'],'line':z['startLine'],'reached':z['name'] in reached} for z in hs],'unreached':[z['name'] for z in hs if z['name'] not in reached]})
    raw=(w/source).read_bytes();syntax=[z for z in read('syntax-boundaries.json') if z['file']==source]
    assert len(syntax)==1;span=syntax[0]['nameRange'];assert raw[span['start']['offset']:span['end']['offset']].decode()=='localCompactness'
    raw=raw[:span['start']['offset']]+b'closedCompactnessSource'+raw[span['end']['offset']:]
    imports=[];body=[]
    for text in [(w/f).read_text() for f in helpers]+[raw.decode()]:
        lines=[]
        for line in text.splitlines(keepends=True):
            if line.startswith('import '):
                imp=line.strip()
                if imp.removeprefix('import ') in helpermods:continue
                assert imp!='import Theorems.Thm_'+target.replace('.','_')
                if imp not in imports:imports.append(imp)
            else:lines.append(line)
        body.append(''.join(lines).strip())
    assert all(imp.startswith(('import Mathlib.','import Definitions.')) or imp=='import Lean.Elab.Tactic.Omega' for imp in imports)
    formal=read('platform-before-parent.json')['formal_statement'];assert formal.startswith('theorem '+target+' : ') and formal.endswith(' := by sorry')
    exact=formal.replace('theorem '+target+' : ','theorem solution : ',1).removesuffix(' := by sorry')
    code='\n'.join(imports)+'\n\n'+'\n\n'.join(body)+'\n\n'+exact+' :=\n  '+pre+'closedCompactnessSource\n'
    assert 'sorry' not in code and 'import Solutions.' not in code and ('theorem '+target) not in code
    (w/sol).write_text(code)
    expected=formal.replace('theorem '+target+' : ','theorem PlatformOriginalType : ',1).removesuffix(' := by sorry')+' := solution\n'
    audit=code+'\n'+expected+'''\nopen Lean
run_meta do
  let a ← getConstInfo `solution
  let e ← getConstInfo `PlatformOriginalType
  unless ← Lean.Meta.isDefEq a.type e.type do throwError "Original platform type differs"
  let axs ← collectAxioms `solution
  for ax in axs do
    unless #[`propext, `Classical.choice, `Quot.sound].contains ax do throwError "Unexpected solution axiom {ax}"
  IO.FS.writeFile "OUTPUT" (Json.pretty (Json.mkObj [("type",Json.str (← Lean.Meta.ppExpr a.type).pretty),("axioms",toJson (axs.map toString)),("original_type_equal",Json.bool true)]))
'''.replace('OUTPUT',u+'solution-type-axioms.json')
    (b/'AuditSolution.lean').write_text(audit)
    bind()
    original=[z for z in read('final-readbacks.json')['declarations'] if z['declaration']!=target]
    assert len(original)==61 and all(z['declaration'] in reached for z in original)
    save('solution-source-closure.json',{'source':sol,'source_sha256':sha(w/sol),'inlined_helpers':[z['declaration'] for z in original],'all_authored_helpers_consumed':True,'compiler_reached_helpers':[z['name'] for z in hs if z['name'] in reached],'unreached_generated_structure_methods':[z['name'] for z in hs if z['name'] not in reached],'existing_dependencies':dependencies,'type_source':'platform-before-parent.json formal_statement verbatim','name_rewrite':'Compiler parser nameRange only','no_new_nodes':True,'no_open_debt':True})
def bind():
    graph=[json.loads(l) for l in (b/'decl_graph.jsonl').read_text().splitlines() if l.strip()]
    original=read('blind-readbacks-original.json')['declarations'];rb=[]
    for row in original:
        assert sha(Path(row['path']))==row['sha256']
        path=source if row['userName']==target else 'Solutions/'+Path(row['path']).name
        module=path[:-5].replace('/','.')
        found=[x for x in graph if x['module']==module and x['startLine']>0 and ((x['userName']==row['userName']) if row['userName'] else (x['isInstance'] and x['startLine']==row['source_span']['start_line']))]
        if not found and row['userName']:
            suffix='.'.join(row['userName'].split('.')[-2:]) if '.EPlace.' in row['userName'] or '.TendstoP1.' in row['userName'] or '.PadicAlgCl.' in row['userName'] else row['userName'].split('.')[-1]
            found=[x for x in graph if x['module']==module and x['startLine']>0 and x['userName'].endswith('.'+suffix)]
        assert len(found)==1,(row.get('userName'),len(found));x=found[0]
        rb.append({'declaration':x['name'],'userName':x['userName'],'path':path,'module':module,'source_sha256':sha(w/path),'compiler_type':x['elaboratedType'],'source_span':{'start_line':x['startLine'],'end_line':x['endLine']},'blind_original_path':row['path'],'blind_original_sha256':row['sha256'],'binding':'compiler name and module, or unambiguous namespace-resolved suffix in that module','blind_static_name':row['userName'],'original_packet':row['original_packet'],'original_packet_sha256':row['original_packet_sha256'],'fields':row.get('fields'),**row['statements'],'proof_notes':row.get('proof_notes'),'quotation':None})
    correction=read('blind-readback-exists_subseq_limit-compiler-type.json')
    selected=[z for z in rb if z['declaration']==correction['target']];assert len(selected)==1
    row=selected[0];assert row['compiler_type']==correction['compiler_type'] and row['source_sha256']==correction['sourceSHA']
    row['superseded_original_packet']=row['original_packet'];row['superseded_blind_original_path']=row['blind_original_path'];row['superseded_blind_original_sha256']=row['blind_original_sha256']
    row['original_packet']='blind-readback-exists_subseq_limit-compiler-type.json';row['original_packet_sha256']=sha(b/row['original_packet'])
    row.update(correction['statements']);row['readback_scope_correction']='Fresh independent actual compiler-type readback; original source-only packet retained unchanged'
    row['requested_model']=correction['requested_model'];row['actual_model']=correction['actual_model']
    assert len(rb)==62;save('final-readbacks.json',{'declarations':rb,'blind_readback':True,'compiler_bound':True,'quotations_separate':True,'scope_correction':'exists_subseq_limit includes the actual retained CharZero K binder'})
def checked(tag,path,review=False):
    z=read(tag+'-result.json');q=z['request'];rs=z['result']
    assert z['status']=='succeeded' and rs['exit_code']==0 and 'sorryAx' not in rs['stdout'],tag
    assert q['exclusive'] and q['workspace']==str(w) and q['parameters']=={'source':path},tag
    assert q['worktree_manifest']['source_sha256']==sha(w/path),tag
    assert rs['actual_arguments']==['lean',path] and rs['snapshot']['workspace_mode']=='exclusive_worktree' and rs['snapshot']['snapshot_id'] is None,tag
    if review:assert rs['review']['passed'],tag
    return z
def preflight():
    receipts=[checked(Path(f).stem.removeprefix('Source_')+'-leaf',f) for f in helpers]+[checked('localCompactness-leaf',source),checked('closed-axioms-review','Solutions/Checks_FermatLocalCompactness.lean',True),checked('source-graph-leaf',u+'ExtractCompactnessGraph.lean'),checked('syntax-leaf',u+'ExtractCompactnessSyntax.lean'),checked('direct-solution-leaf',sol),checked('solution-type-axioms-review',u+'AuditSolution.lean',True),checked('all-constants-review',u+'AuditAllConstants.lean',True),checked('production-gates-review',u+'ProductionGates.lean',True)]
    assert read('solution-type-axioms.json')['original_type_equal']
    assert set(read('solution-type-axioms.json')['axioms'])<={'propext','Classical.choice','Quot.sound'}
    axs=read('all-module-axioms.json');graph=[json.loads(l) for l in (b/'decl_graph.jsonl').read_text().splitlines() if l.strip()];modules={f[:-5].replace('/','.') for f in helpers+[source]};expected={z['name'] for z in graph if z['module'] in modules};assert expected<={z['name'] for z in axs} and all(set(z['axioms'])<={'propext','Classical.choice','Quot.sound'} for z in axs)
    closure=read('solution-source-closure.json');assert closure['source_sha256']==sha(w/sol) and len(closure['inlined_helpers'])>=50
    rb=read('final-readbacks.json');assert len(rb['declarations'])>=50
    for row in rb['declarations']:assert row['source_sha256']==sha(w/row['path'])
    gate=receipts[-1]['request']['worktree_manifest']['input_hashes'];assert all(gate[f]==sha(w/f) for f in helpers+[source])
    for dep in dependencies:
        old=read('platform-existing-'+dep.removeprefix(pre)+'.json');assert old['theorem_name']==dep and old['status']=='Proved' and old['visibility']=='private' and old['mathlib_rev']==ENV
    save('delivery-validation.json',{'passed':True,'original_platform_type_equal':True,'new_platform_nodes':[],'new_open_debt':0,'closed_source_reuse':True,'readbacks':len(rb['declarations']),'compiler_checks':[z['job_id'] for z in receipts],'owned_source_hashes':{f:sha(w/f) for f in helpers+[source,'Solutions/Checks_FermatLocalCompactness.lean']}})
def prose(rows):
    return '\n\n'.join('**'+title+'**\n\n'+'\n\n'.join('`'+z['userName']+'`\n\n'+z[lang] for z in rows) for lang,title in [('en','English'),('zh_Hans','简体中文'),('ja','日本語')])
def publish():
    preflight();spec=importlib.util.spec_from_file_location('api',w/'.local/abc-item/api.py');api=importlib.util.module_from_spec(spec);spec.loader.exec_module(api)
    assert api.base=='https://prove2.me/api/v1';ident=read('target-id.json')['id'];before=read('platform-before-parent.json');current=api.request('/theorems/'+ident)
    assert current['formal_statement']==before['formal_statement'] and current['visibility']=='private' and current['mathlib_rev']==ENV
    for name in dependencies:
        dep=api.request('/theorems/'+read('platform-existing-'+name.removeprefix(pre)+'.json')['theorem_id']);assert dep['theorem_name']==name and dep['status']=='Proved'
    ctx=globals()|{'api':api}
    protocol=(w/'.local/adaptation/platform-tripod-20261113/executed-platform-publish.py').read_text()
    for node in ast.parse(protocol).body:
        if isinstance(node,ast.FunctionDef) and node.name=='verify':exec(compile(ast.Module(body=[node],type_ignores=[]),'<established-protocol>','exec'),ctx)
    all_rows=read('final-readbacks.json')['declarations'];rows=[z for z in all_rows if z['declaration']==target or z['declaration'].endswith('.localCompactness_source') or z['declaration'].endswith('.exists_subseq_bounded')];assert len(rows)==3;quote=(b/'quotation.md').read_text().strip()
    origin='Shinichi Mochizuki, Arithmetic Elliptic Curves in General Position (February 2009), proof of Theorem 2.1, printed/PDF p.12, official PDF https://www.kurims.kyoto-u.ac.jp/~motizuki/Arithmetic%20Elliptic%20Curves%20in%20General%20Position.pdf . The original compactness passage concerns unordered tuples of conjugates; the precise formal subsequence and all-embeddings theorem is the source-code realization below. Complete proof sources: Heights/Local/Compactness.lean, Heights/Local/LimitPlace.lean and Heights/Curve/Compactness.lean:233 at 721496ca4c158e511d25d8ccf6bfe8503eda73c1, pinned by hashes in source-consumer.json. All embeddings of each same actual full point field are retained. Countability is derived from the existing Model finite function-field presentation, and field finiteness from hRF. Both complex and 2-adic limit places contribute to one actual finite set, chosen before the test function; one constant after that function bounds every embedding on a common tail. No local compactness assumption on the full p-adic algebraic closure is made. The existing hDVR binder remains in the unchanged parent type. Apache-2.0 notices retained; no new theorem node, open debt, law field, Fermat geometry assumption or upstream project dependency is added. All helper-level trilingual independent readbacks are preserved in the local source evidence; this platform explanation displays the original parent and the two main source statements.'
    explanation=quote+'\n\n'+prose(rows)+'\n\n'+origin
    assert len(explanation)<=50000
    req={'theorem_id':ident,'proof_type':'prove','file':sol,'source_sha256':sha(w/sol),'explanation':explanation};tag='prove-localCompactness'
    if (b/(tag+'-verify-submit.json')).exists():assert read(tag+'-verify-request.json')==req
    else:
        assert not (b/(tag+'-verification-requested.json')).exists(),'Reconcile prior POST before retry'
        save(tag+'-verification-requested.json',req)
    z=ctx['verify'](tag,ident,sol,explanation);assert z['status']=='ACCEPTED'
    patch={'natural_language_statement':quote+'\n\n'+prose([row for row in rows if row['declaration']==target]),'source':origin};save('parent-metadata-patch-request.json',patch)
    current=api.request('/theorems/'+ident)
    if not all(current.get(k)==v for k,v in patch.items()):save('parent-metadata-patch-response.json',api.request('/theorems/'+ident,patch,'PATCH'))
    current=api.request('/theorems/'+ident);assert current['status']=='Proved' and current['formal_statement']==before['formal_statement'] and all(current[k]==v for k,v in patch.items());save('platform-after-parent.json',current)
    sys.path.insert(0,str(w/'.local/adaptation/northcott-sourceproof-20261114'));from graph_completion import fetch_complete_math_graph
    save('root-graph-after.json',fetch_complete_math_graph(api,ROOT,save,'root-graph-after'));ls=[]
    while True:
        page=api.request('/theorems/'+ROOT+'/open-leaves?limit=50&offset='+str(len(ls)));save('root-frontier-after-page-'+str(len(ls))+'.json',page);ls+=page['open_leaves']
        if len(ls)>=page['total']:break
    assert len(ls)==page['total'];save('root-frontier-after.json',{'open_leaves':ls,'total':page['total'],'all_pages_fetched':True})
    print('localCompactness ACCEPTED and Proved; original graph and frontier read back.',flush=True)
if __name__=='__main__':{'generate':generate,'bind':bind,'preflight':preflight,'publish':publish}[sys.argv[1]]()
