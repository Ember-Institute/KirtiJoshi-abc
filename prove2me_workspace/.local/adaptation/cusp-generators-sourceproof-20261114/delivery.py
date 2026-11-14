from pathlib import Path
import ast, hashlib, importlib.util, json, sys, time, urllib.request, urllib.error, uuid

r=Path('/home/admin-wsl/Coq/abc');w=r/'prove2me_workspace';b=w/'.local/adaptation/cusp-generators-sourceproof-20261114'
u='.local/adaptation/cusp-generators-sourceproof-20261114/';pre='AbcAdaptation.Tripod.Fermat.Proper.'
target=pre+'cuspGeneratorsExists';dependencies=[pre+n for n in ['riemannRochFiniteDimensional','riemannRochDimensionUpperBound','riemannRochEventuallyLinear']]
source='Theorems/Thm_'+target.replace('.','_')+'.lean'
helper='Solutions/Source_FermatCoordRingSource.lean'
sol=u+'Solution_cuspGeneratorsExists.lean'
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
    hs=[z for z in graph if z['module']==helper[:-5].replace('/','.') and z['startLine']>0]
    assert len(hs)==8 and all(z['name'] in reached for z in hs)
    assert set(dependencies)<=reached
    raw=(w/source).read_bytes();syntax=[z for z in read('syntax-boundaries.json') if z['file']==source]
    assert len(syntax)==1;span=syntax[0]['nameRange'];assert raw[span['start']['offset']:span['end']['offset']].decode()=='cuspGeneratorsExists'
    raw=raw[:span['start']['offset']]+b'closedCuspSource'+raw[span['end']['offset']:]
    imports=[];body=[]
    for text in [(w/helper).read_text(),raw.decode()]:
        lines=[]
        for line in text.splitlines(keepends=True):
            if line.startswith('import '):
                imp=line.strip()
                if imp=='import Solutions.Source_FermatCoordRingSource':continue
                assert imp!='import Theorems.Thm_'+target.replace('.','_')
                if imp not in imports:imports.append(imp)
            else:lines.append(line)
        body.append(''.join(lines).strip())
    assert all(imp.startswith(('import Mathlib.','import Definitions.')) or imp in {'import Theorems.Thm_'+n.replace('.','_') for n in dependencies} for imp in imports)
    formal=read('platform-before-parent.json')['formal_statement'];assert formal.startswith('theorem '+target+' : ') and formal.endswith(' := by sorry')
    exact=formal.replace('theorem '+target+' : ','theorem solution : ',1).removesuffix(' := by sorry')
    code='\n'.join(imports)+'\n\n'+'\n\n'.join(body)+'\n\n'+exact+' :=\n  '+pre+'closedCuspSource\n'
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
    save('solution-source-closure.json',{'source':sol,'source_sha256':sha(w/sol),'inlined_helpers':[z['name'] for z in hs],'all_helpers_consumed':True,'existing_dependencies':dependencies,'type_source':'platform-before-parent.json formal_statement verbatim','name_rewrite':'Compiler parser nameRange only','no_new_nodes':True,'no_open_debt':True})
    bind()
def bind():
    graph=[json.loads(l) for l in (b/'decl_graph.jsonl').read_text().splitlines() if l.strip()]
    original=read('blind-readbacks-original.json')['declarations'];rb=[]
    for z in original:
        assert sha(Path(z['path']))==z['whole-file-sha256']
        path=helper if z['userName']!=target else source
        found=[x for x in graph if x['module']==path[:-5].replace('/','.') and x['userName']==z['userName'] and x['startLine']>0]
        assert len(found)==1,(z['userName'],len(found));x=found[0]
        rb.append({'declaration':x['name'],'userName':x['userName'],'path':path,'module':x['module'],'source_sha256':sha(w/path),'compiler_type':x['elaboratedType'],'source_span':{'start_line':x['startLine'],'end_line':x['endLine']},'blind_original_path':z['path'],'blind_original_sha256':z['whole-file-sha256'],**z['statements'],'proof_notes':z.get('proof_notes'),'quotation':None})
    assert len(rb)==9;save('final-readbacks.json',{'declarations':rb,'blind_readback':True,'compiler_bound':True,'quotations_separate':True})
    quotes=read('mochizuki-source-quotations.json')['quotations'];q=next(z for z in quotes if z['id']=='NBM-T25-P6-CANONICAL-CONTEXT')
    rendered=q['exact_quotation']
    for expr in ['D \\overset{\\mathrm{def}}{=} \\sum_{t\\in T}[t]','\\mathcal{O}_X(D)','\\mathcal{L}','\\omega_X']:
        rendered=rendered.replace(expr,'$'+expr+'$')
    quote='> '+rendered+'\n\n— Shinichi Mochizuki, *Noncritical Belyi Maps*, proof of Theorem 2.5, printed p.6.\n\nSource context: '+q['official_url']+' . PDF SHA256 '+q['pdf_sha256']+'. The quotation supplies the divisor and canonical-bundle context; the exact coordinate-ring finite-generation construction below is an independently adapted formal-source argument.'
    (b/'quotation.md').write_text(quote+'\n')
def checked(tag,path,review=False):
    z=read(tag+'-result.json');q=z['request'];rs=z['result']
    assert z['status']=='succeeded' and rs['exit_code']==0 and 'sorryAx' not in rs['stdout'],tag
    assert q['exclusive'] and q['workspace']==str(w) and q['parameters']=={'source':path},tag
    assert q['worktree_manifest']['source_sha256']==sha(w/path),tag
    assert rs['actual_arguments']==['lean',path] and rs['snapshot']['workspace_mode']=='exclusive_worktree' and rs['snapshot']['snapshot_id'] is None,tag
    if review:assert rs['review']['passed'],tag
    return z
def preflight():
    receipts=[checked('source-helper-leaf',helper),checked('cuspGeneratorsExists-leaf',source),checked('closed-axioms-review','Solutions/Checks_FermatCuspGeneratorsClosed.lean',True),checked('source-graph-leaf',u+'ExtractCuspGraph.lean'),checked('syntax-leaf',u+'ExtractCuspSyntax.lean'),checked('direct-solution-leaf',sol),checked('solution-type-axioms-review',u+'AuditSolution.lean',True),checked('all-constants-review',u+'AuditAllConstants.lean',True),checked('production-gates-review',u+'ProductionGates.lean',True)]
    assert read('solution-type-axioms.json')['original_type_equal']
    assert set(read('solution-type-axioms.json')['axioms'])<={'propext','Classical.choice','Quot.sound'}
    axs=read('all-module-axioms.json');assert len(axs)>=9 and all(set(z['axioms'])<={'propext','Classical.choice','Quot.sound'} for z in axs)
    closure=read('solution-source-closure.json');assert closure['source_sha256']==sha(w/sol) and len(closure['inlined_helpers'])==8
    rb=read('final-readbacks.json');assert len(rb['declarations'])==9
    for row in rb['declarations']:assert row['source_sha256']==sha(w/row['path'])
    gate=receipts[-1]['request']['worktree_manifest']['input_hashes'];assert gate[helper]==sha(w/helper) and gate[source]==sha(w/source)
    for dep in dependencies:
        old=read('platform-existing-'+dep.removeprefix(pre)+'.json');assert old['theorem_name']==dep and old['status']=='Proved' and old['visibility']=='private' and old['mathlib_rev']==ENV
    save('delivery-validation.json',{'passed':True,'original_platform_type_equal':True,'new_platform_nodes':[],'new_open_debt':0,'closed_source_reuse':True,'readbacks':9,'compiler_checks':[z['job_id'] for z in receipts],'owned_source_hashes':{helper:sha(w/helper),source:sha(w/source),'Solutions/Checks_FermatCuspGeneratorsClosed.lean':sha(w/'Solutions/Checks_FermatCuspGeneratorsClosed.lean')}})
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
    rows=read('final-readbacks.json')['declarations'];quote=(b/'quotation.md').read_text().strip()
    origin='Shinichi Mochizuki, Noncritical Belyi Maps (May 2004), proof of Theorem 2.5, p.6; official PDF https://www.kurims.kyoto-u.ac.jp/~motizuki/Noncritical%20Belyi%20Maps.pdf . The quotation supplies divisor and regular-function context. The exact coordinate-ring argument is independently adapted from Belyi/CurveField/CoordRing.lean:38–163 at 9ce4d3f793d3bc831f2fc7214b7dbad90ea012d8, SHA256 d21848a412ff4da577615f237816c973cbe3dfd0790f0123f8ff3bc5b11eb180, and Genl/Curves/BelyiDescent.lean:292–306 at ea2846c877d1e16d8f0b911a5fed07f5ee69eaaf. Existing Proved Riemann statements supply actual large effective polar realization. The complete original coordinate ring and all three fixed tripod functions are retained, as are the actual Model, all proper places, and original hypotheses. Apache-2.0 notices retained. No new theorem node, open debt, free law, weakened target or Iut/Genl/Belyi runtime dependency is added.'
    explanation=quote+'\n\n'+prose(rows)+'\n\n'+origin
    req={'theorem_id':ident,'proof_type':'prove','file':sol,'source_sha256':sha(w/sol),'explanation':explanation};tag='prove-cuspGeneratorsExists'
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
    print('cuspGeneratorsExists ACCEPTED and Proved; original graph and frontier read back.',flush=True)
if __name__=='__main__':{'generate':generate,'bind':bind,'preflight':preflight,'publish':publish}[sys.argv[1]]()
