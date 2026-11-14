from pathlib import Path
import ast, hashlib, importlib.util, json, sys, time, urllib.request, urllib.error, uuid
r=Path('/home/admin-wsl/Coq/abc');w=r/'prove2me_workspace';b=w/'.local/adaptation/belyi-cusp-coefficient-sourceproof-20261114'
u='.local/adaptation/belyi-cusp-coefficient-sourceproof-20261114/';pre='AbcAdaptation.Tripod.Fermat.Proper.'
target=pre+'belyiCanonicalCuspCoefficientIdentity';source='Theorems/Thm_'+target.replace('.','_')+'.lean'
helper='Solutions/Source_FermatBelyiCuspCoefficient.lean';coord='Solutions/Source_FermatCoordRingSource.lean';coordname=pre+'CuspCoordRingSource.cuspDivisor_apply'
sol=u+'Solution_belyiCanonicalCuspCoefficientIdentity.lean';ENV='0df444a360eaa60ab8c11dca51a86af692955474';ROOT='e33ff731-60a7-43ef-87ae-c12aeba23cb5'
def read(n):return json.loads((b/n).read_text())
def save(n,z):(b/n).write_text(json.dumps(z,ensure_ascii=False,indent=2)+'\n')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def graph():return [json.loads(l) for l in (b/'decl_graph.jsonl').read_text().splitlines() if l.strip()]
def span(path,name):
    hits=[s for s in read('syntax-boundaries.json') if s['file']==path and s['nameText']==name];assert len(hits)==1,(path,name)
    return hits[0]
def header(path,name):
    s=span(path,name);raw=(w/path).read_bytes();a=s['declStart']['offset'];d=s['docstring']
    if d and d['start']['offset']==a:a=d['end']['offset']
    return raw[a:s['valStart']['offset']].decode().strip()
def bind():
    g={z['name']:z for z in graph()};out=[]
    for row in read('blind-readbacks-source.json')['readbacks']:
        n=row['qualified_name'];z=g[n];p=helper;assert z['module']==p[:-5].replace('/','.')
        assert sha(Path(row['path']))==row['source_sha256']
        assert header(p,n.split('.')[-1])==row['signature']
        out.append({'declaration':n,'userName':n,'path':p,'module':z['module'],'source_sha256':sha(w/p),'compiler_type':z['elaboratedType'],'source_span':{'start_line':z['startLine'],'end_line':z['endLine']},'original_packet':'blind-readbacks-source.json','original_packet_sha256':sha(b/'blind-readbacks-source.json'),'blind_original_path':row['path'],'blind_original_sha256':row['source_sha256'],'binding':'Original parsed declaration header byte-identical; provenance comment only was finalized; compiler resolves same exact declaration',**row['statements'],'proof_notes':row['proof_notes'],'quotation':None})
    for folder,n,p in [('canonical-cusp-split-20261114',target,source),('cusp-generators-sourceproof-20261114',coordname,coord)]:
        packet=w/'.local/adaptation'/folder/'final-readbacks.json';old=next(z for z in json.loads(packet.read_text())['declarations'] if z['declaration']==n);z=g[n]
        assert old['compiler_type']==z['elaboratedType'],n
        if n==coordname:assert old['source_sha256']==sha(w/p)
        bound=old|{'path':p,'source_sha256':sha(w/p),'compiler_type':z['elaboratedType'],'source_span':{'start_line':z['startLine'],'end_line':z['endLine']},'reused_from':str(packet.relative_to(w)),'reused_packet_sha256':sha(packet),'reuse_basis':'Unchanged compiler type; existing independent readback'}
        if n==target:
            bound['original_proof_notes']=old.get('proof_notes')
            bound['proof_notes']={'scope':'Original blind statement readback is reused unchanged; its original proof notes describe the earlier placeholder and are retained under original_proof_notes.','current_formal_body':'Exact application of BelyiCuspCoefficientSource.belyiCanonicalCuspCoefficientIdentity_source; no placeholder.','current_validation':'coefficient-target-leaf-result.json and closed-axioms-review-result.json'}
        out.append(bound)
    assert len(out)==4;save('final-readbacks.json',{'declarations':out,'blind_readback':True,'compiler_bound':True,'quotations_separate':True})
def generate():
    bind();g=graph();rows={z['name']:z for z in g};reached=set();todo=[target]
    while todo:
        n=todo.pop()
        if n in reached:continue
        reached.add(n);z=rows.get(n)
        if z:todo+=z['typeDeps']+z['valueDeps']
    helpermods={helper[:-5].replace('/','.'),coord[:-5].replace('/','.')}
    selected=[z for z in g if z['name'] in reached and z['module'] in helpermods and z['startLine']>0]
    assert {z['name'] for z in selected}=={coordname,pre+'BelyiCuspCoefficientSource.ramIdx_of_residue_eq',pre+'BelyiCuspCoefficientSource.belyiCanonicalCuspCoefficientIdentity_source'}
    s=span(coord,'cuspDivisor_apply');raw=(w/coord).read_bytes();decl=raw[s['declStart']['offset']:s['declEnd']['offset']].decode()
    # Preserve original lexical context for the one needed reused declaration.
    before=raw[:span(coord,'mem_chartRing_iff_forall')['declStart']['offset']].decode()
    coordpart=before+decl+'\n\nend '+pre+'CuspCoordRingSource\n'
    imports=[];bodies=[]
    for text in [coordpart,(w/helper).read_text()]:
        lines=[]
        for line in text.splitlines(keepends=True):
            if line.startswith('import '):
                imp=line.strip()
                if imp.removeprefix('import ') in helpermods:continue
                assert imp.startswith(('import Definitions.','import Mathlib.'))
                if imp not in imports:imports.append(imp)
            else:lines.append(line)
        bodies.append(''.join(lines).strip())
    before=read('platform-before-parent.json');formal=before['formal_statement'];assert formal.startswith('theorem '+target+' {') and formal.endswith(' := by sorry')
    exact=formal.replace('theorem '+target,'theorem solution',1).removesuffix(' := by sorry')
    body=' := by\n  exact '+pre+'BelyiCuspCoefficientSource.belyiCanonicalCuspCoefficientIdentity_source M hDVR hRF φ hφ hfin\n'
    code='\n'.join(imports)+'\n\n'+'\n\n'.join(bodies)+'\n\nopen '+pre.rstrip('.')+'\n\n'+exact+body
    assert 'sorry' not in code and 'import Solutions.' not in code and 'import Theorems.' not in code
    (w/sol).write_text(code)
    expected=formal.replace('theorem '+target,'theorem PlatformOriginalType',1).removesuffix(' := by sorry')+' := by\n  exact solution M hDVR hRF φ hφ hfin\n'
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
    save('solution-source-closure.json',{'source':sol,'source_sha256':sha(w/sol),'inlined_helpers':[z['name'] for z in selected],'all_authored_helpers_consumed':True,'reused_helper':coordname,'reused_source_file':coord,'reused_source_sha256':sha(w/coord),'reused_declaration_parser_span':s,'whole_coordinate_ring_module_inlined':False,'type_source':'Existing raw binder-style platform formal_statement, only theorem name changed','new_nodes':[],'new_open_debt':0})
def checked(tag,path,review=False):
    z=read(tag+'-result.json');q=z['request'];rs=z['result']
    assert z['status']=='succeeded' and rs['exit_code']==0 and 'sorryAx' not in rs['stdout'],tag
    assert q['exclusive'] and q['workspace']==str(w) and q['parameters']=={'source':path},tag
    assert q['worktree_manifest']['source_sha256']==sha(w/path),tag
    assert rs['actual_arguments']==['lean',path] and rs['snapshot']['workspace_mode']=='exclusive_worktree' and rs['snapshot']['snapshot_id'] is None,tag
    if review:assert rs['review']['passed'],tag
    return z
def preflight():
    checks=[('coefficient-source-leaf',helper,False),('coefficient-target-leaf',source,False),('closed-axioms-review','Solutions/Checks_FermatBelyiCuspCoefficient.lean',True),('source-graph-leaf',u+'ExtractCoefficientGraph.lean',False),('syntax-leaf',u+'ExtractCoefficientSyntax.lean',False),('all-constants-review',u+'AuditAllConstants.lean',True),('direct-solution-leaf',sol,False),('solution-type-axioms-review',u+'AuditSolution.lean',True),('production-gates-review',u+'ProductionGates.lean',True)]
    receipts=[checked(*z) for z in checks];axs=read('all-module-axioms.json');assert len(axs)>=3
    expected={z['name'] for z in graph() if z['module'] in {helper[:-5].replace('/','.'),source[:-5].replace('/','.')}}
    assert expected<={z['name'] for z in axs} and all(set(z['axioms'])<={'propext','Classical.choice','Quot.sound'} for z in axs)
    assert read('solution-type-axioms.json')['original_type_equal'] and set(read('solution-type-axioms.json')['axioms'])<={'propext','Classical.choice','Quot.sound'}
    own=[helper,source,'Solutions/Checks_FermatBelyiCuspCoefficient.lean'];gate=receipts[-1]['request']['worktree_manifest']['input_hashes'];assert all(gate[f]==sha(w/f) for f in own)
    rb=read('final-readbacks.json')['declarations'];assert len(rb)==4 and all(z['source_sha256']==sha(w/z['path']) for z in rb)
    assert read('solution-source-closure.json')['source_sha256']==sha(w/sol) and 'sorry' not in (w/sol).read_text()
    save('delivery-validation.json',{'passed':True,'original_platform_type_equal':True,'new_platform_nodes':[],'new_open_debt':0,'closed_source_reuse':True,'readbacks':4,'compiler_checks':[z['job_id'] for z in receipts],'owned_source_hashes':{f:sha(w/f) for f in own}})
def prose(rows):
    return '\n\n'.join('**'+title+'**\n\n'+'\n\n'.join('`'+z['userName']+'`\n\n'+z[lang] for z in rows) for lang,title in [('en','English'),('zh_Hans','简体中文'),('ja','日本語')])
def publish():
    preflight();s=importlib.util.spec_from_file_location('api',w/'.local/abc-item/api.py');api=importlib.util.module_from_spec(s);s.loader.exec_module(api)
    assert api.base=='https://prove2.me/api/v1';ident=read('target-id.json')['id'];before=read('platform-before-parent.json');current=api.request('/theorems/'+ident)
    assert current['formal_statement']==before['formal_statement'] and current['visibility']=='private' and current['mathlib_rev']==ENV
    ctx=globals()|{'api':api};protocol=(w/'.local/adaptation/platform-tripod-20261113/executed-platform-publish.py').read_text()
    for node in ast.parse(protocol).body:
        if isinstance(node,ast.FunctionDef) and node.name=='verify':exec(compile(ast.Module(body=[node],type_ignores=[]),'<established-protocol>','exec'),ctx)
    rb=read('final-readbacks.json')['declarations'];quote=(b/'quotation.md').read_text().strip()
    origin='Shinichi Mochizuki, Arithmetic Elliptic Curves in General Position (February 2009), Theorem 2.1, pp.11–12, canonical sheaf, reduced three-cusp divisor and log-canonical pullback context. Official PDF https://www.kurims.kyoto-u.ac.jp/~motizuki/Arithmetic%20Elliptic%20Curves%20in%20General%20Position.pdf ; SHA256 b9dc115af61dca7fe434332ebafddf6a376a9e2926dad4e1ea2dcc0d2441f768. The explicit coefficient formula is a formal-source realization, not a verbatim paper theorem. Complete exact sources: Belyi/CurveField/BelyiRelation.lean:85–139 and RamIdx.lean:218–223 at 9ce4d3f793d3bc831f2fc7214b7dbad90ea012d8. Apache-2.0 notices and file hashes retained in local evidence. The existing actual cusp-divisor coefficient theorem is reused with the same supplied finiteness proof. All proper places including poles and infinity, the integer index, actual residue minimal polynomial and total order convention remain. The four cases are zero, value one, pole and noncusp; nonzero factors are established before order additivity. No new node, source-law field, model condition or upstream package import is added. The separate canonicalDifferentialChange node remains Open.'
    notes=r'''Write $a_\varphi(P)$ for the displayed differential coefficient, $C(P)$ for the reduced cusp coefficient, and $b_\varphi(P)=\max(0,-\operatorname{ord}_P\varphi)$. The proved identity is

$$a_\varphi(P)+C(P)=b_\varphi(P)+\operatorname{ord}_P(\varphi(\varphi-1)).$$

Transcendence makes both product factors nonzero. At a zero of $\varphi$, the two sides equal its index $e$. At a value-one cusp, the actual residue is one, so its minimal polynomial is $X-1$; again both sides equal $e$. At a pole, the index is $-\operatorname{ord}_P\varphi$ and $\operatorname{ord}_P(\varphi-1)=\operatorname{ord}_P\varphi$, so both sides equal $-e$. Away from these cusps, index positivity and the Belyi condition imply index one, and both sides vanish. These cases cover every proper place.'''
    explanation=notes+'\n\n'+quote+'\n\n'+prose(rb)+'\n\n'+origin;assert len(explanation)<=50000
    tag='prove-belyiCanonicalCuspCoefficientIdentity';req={'theorem_id':ident,'proof_type':'prove','file':sol,'source_sha256':sha(w/sol),'explanation':explanation}
    if (b/(tag+'-verify-submit.json')).exists():assert read(tag+'-verify-request.json')==req
    else:
        assert not (b/(tag+'-verification-requested.json')).exists(),'Reconcile prior POST before retry'
        save(tag+'-verification-requested.json',req)
    z=ctx['verify'](tag,ident,sol,explanation);assert z['status']=='ACCEPTED'
    patch={'natural_language_statement':quote+'\n\n'+prose([z for z in rb if z['declaration']==target]),'source':origin};save('parent-metadata-patch-request.json',patch)
    current=api.request('/theorems/'+ident)
    if not all(current.get(k)==v for k,v in patch.items()):save('parent-metadata-patch-response.json',api.request('/theorems/'+ident,patch,'PATCH'))
    current=api.request('/theorems/'+ident);assert current['status']=='Proved' and current['formal_statement']==before['formal_statement'] and all(current[k]==v for k,v in patch.items());save('platform-after-parent.json',current)
    sys.path.insert(0,str(w/'.local/adaptation/northcott-sourceproof-20261114'));from graph_completion import fetch_complete_math_graph
    save('root-graph-after.json',fetch_complete_math_graph(api,ROOT,save,'root-graph-after'));ls=[]
    while True:
        page=api.request('/theorems/'+ROOT+'/open-leaves?limit=50&offset='+str(len(ls)));save('root-frontier-after-page-'+str(len(ls))+'.json',page);ls+=page['open_leaves']
        if len(ls)>=page['total']:break
    assert len(ls)==page['total'];save('root-frontier-after.json',{'open_leaves':ls,'total':page['total'],'all_pages_fetched':True})
    print('Exact coefficient identity ACCEPTED and Proved; full graph and frontier fetched.',flush=True)
if __name__=='__main__':{'bind':bind,'generate':generate,'preflight':preflight,'publish':publish}[sys.argv[1]]()
