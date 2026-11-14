from pathlib import Path
import ast, hashlib, importlib.util, json, sys, time, urllib.request, urllib.error, uuid
r=Path('/home/admin-wsl/Coq/abc');w=r/'prove2me_workspace';b=w/'.local/adaptation/canonical-differential-sourceproof-20261114'
u='.local/adaptation/canonical-differential-sourceproof-20261114/';pre='AbcAdaptation.Tripod.Fermat.Proper.'
target=pre+'canonicalDifferentialChange';source='Theorems/Thm_'+target.replace('.','_')+'.lean'
helpers=['Solutions/Source_'+n+'.lean' for n in ['FermatDifferentialChain','FermatDifferentialOrder','FermatCanonicalDifferentialChange']]
dependencies=[pre+'CurveDeriv.'+n for n in ['derivAlong_eq_unit_mul_pow_of_aeval','derivAlong_unit_mul_pow']]
sol=u+'Solution_canonicalDifferentialChange.lean';ENV='0df444a360eaa60ab8c11dca51a86af692955474';ROOT='e33ff731-60a7-43ef-87ae-c12aeba23cb5'
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
    g=graph();out=[];packet=read('blind-readbacks-source.json')
    for row in packet['declarations']:
        n=row['qualified_name'];path='Solutions/'+Path(row['source']['path']).name
        assert sha(Path(row['source']['path']))==row['source']['sha256']
        hits=[z for z in g if z['module']==path[:-5].replace('/','.') and z['userName']==n and z['startLine']>0];assert len(hits)==1,(n,len(hits));z=hits[0]
        # Compiler declStart may include private modifiers/attributes omitted by the blind raw signature.
        actual=header(path,n.split('.')[-1]);assert actual.endswith(row['raw_signature']),n
        out.append({'declaration':z['name'],'userName':z['userName'],'path':path,'module':z['module'],'source_sha256':sha(w/path),'compiler_type':z['elaboratedType'],'source_span':{'start_line':z['startLine'],'end_line':z['endLine']},'blind_original_path':row['source']['path'],'blind_original_sha256':row['source']['sha256'],'original_packet':'blind-readbacks-source.json','original_packet_sha256':sha(b/'blind-readbacks-source.json'),'raw_signature':row['raw_signature'],'section_namespace_binders':row['section_namespace_binders'],'original_blind_elaboration':row['elaboration'],'elaboration':{'status':'compiler_bound','compiler_qualified_name':z['name'],'scope':'Current compiler evidence; original blind elaboration limits retained separately'},'en':row['readback']['en'],'zh_Hans':row['readback']['zh-CN'],'ja':row['readback']['ja'],'original_blind_proof_notes':packet['proof_notes'],'proof_notes':{'scope':'Original blind auditor did not compile or assess proof correctness; its historical notes are retained separately.','current_binding':'The exact current declaration name, type and source span come from successful compiler graph/parser receipts.'},'quotation':None})
    packetpath=w/'.local/adaptation/canonical-cusp-split-20261114/final-readbacks.json';old=next(z for z in json.loads(packetpath.read_text())['declarations'] if z['declaration']==target);z=next(z for z in g if z['name']==target);assert old['compiler_type']==z['elaboratedType']
    out.append(old|{'path':source,'source_sha256':sha(w/source),'compiler_type':z['elaboratedType'],'source_span':{'start_line':z['startLine'],'end_line':z['endLine']},'reused_from':str(packetpath.relative_to(w)),'reused_packet_sha256':sha(packetpath),'reuse_basis':'Unchanged compiler type; independent statement readback reused','original_proof_notes':old.get('proof_notes'),'proof_notes':{'scope':'Original blind statement readback unchanged; original_proof_notes describes earlier placeholder.','current_formal_body':'Exact application of canonicalDifferentialChange_source; no placeholder.','validation':'Current leaf and closed-axioms CI receipts'}})
    assert len(out)==23;save('final-readbacks.json',{'declarations':out,'blind_readback':True,'compiler_bound':True,'quotations_separate':True,'retained_binder_review':'Independent compiler-type audit required before upload'})
def generate():
    bind();g=graph();index={z['name']:z for z in g};reached=set();todo=[target]
    while todo:
        n=todo.pop()
        if n in reached:continue
        reached.add(n);z=index.get(n)
        if z:todo+=z['typeDeps']+z['valueDeps']
    mods={f[:-5].replace('/','.') for f in helpers};hs=[z for z in g if z['module'] in mods and z['startLine']>0]
    assert len(hs)==22 and all(z['name'] in reached for z in hs)
    assert all(n in reached for n in dependencies)
    imports=[];bodies=[]
    for f in helpers:
        lines=[]
        for line in (w/f).read_text().splitlines(keepends=True):
            if line.startswith('import '):
                imp=line.strip()
                if imp.removeprefix('import ') in mods:continue
                assert imp.startswith(('import Definitions.','import Mathlib.')) or imp in ['import Theorems.Thm_'+n.replace('.','_') for n in dependencies]
                if imp not in imports:imports.append(imp)
            else:lines.append(line)
        bodies.append(''.join(lines).strip())
    formal=read('platform-before-parent.json')['formal_statement'];assert formal.startswith('theorem '+target+' {') and formal.endswith(' := by sorry')
    exact=formal.replace('theorem '+target,'theorem solution',1).removesuffix(' := by sorry')
    body=' := by\n  exact '+pre+'canonicalDifferentialChange_source M hDVR hRF φ hφ K\n'
    code='\n'.join(imports)+'\n\n'+'\n\n'.join(bodies)+'\n\nopen '+pre.rstrip('.')+'\n\n'+exact+body
    assert 'sorry' not in code and 'import Solutions.' not in code and ('import Theorems.Thm_'+target.replace('.','_')) not in code
    (w/sol).write_text(code)
    expected=formal.replace('theorem '+target,'theorem PlatformOriginalType',1).removesuffix(' := by sorry')+' := by\n  exact solution M hDVR hRF φ hφ K\n'
    audit=code+'\n'+expected+'''\nopen Lean
run_meta do
  let a ← getConstInfo `solution
  let e ← getConstInfo `PlatformOriginalType
  unless ← Lean.Meta.isDefEq a.type e.type do throwError "Original platform type differs"
  let axs ← collectAxioms `solution
  for ax in axs do
    unless #[`propext, `Classical.choice, `Quot.sound].contains ax do throwError "Unexpected solution axiom {ax}"
  IO.FS.writeFile "OUTPUT" (Json.pretty (Json.mkObj [("type",Json.str (← Lean.Meta.ppExpr a.type).pretty),("axioms",toJson (axs.map toString)),("original_type_equal",Json.bool true)]))
'''.replace('OUTPUT',u+'solution-type-axioms.json');(b/'AuditSolution.lean').write_text(audit)
    save('solution-source-closure.json',{'source':sol,'source_sha256':sha(w/sol),'inlined_helpers':[z['name'] for z in hs],'all_authored_helpers_consumed':True,'imports_only_existing_proved_theorems':dependencies,'no_own_target_import':True,'type_source':'Existing raw binder-style platform formal_statement; theorem name only changed','new_nodes':[],'new_open_debt':0})
def checked(tag,path,review=False):
    z=read(tag+'-result.json');q=z['request'];rs=z['result']
    assert z['status']=='succeeded' and rs['exit_code']==0 and 'sorryAx' not in rs['stdout'],tag
    assert q['exclusive'] and q['workspace']==str(w) and q['parameters']=={'source':path},tag
    assert q['worktree_manifest']['source_sha256']==sha(w/path),tag
    assert rs['actual_arguments']==['lean',path] and rs['snapshot']['workspace_mode']=='exclusive_worktree' and rs['snapshot']['snapshot_id'] is None,tag
    if review:assert rs['review']['passed'],tag
    return z
def preflight():
    checks=[(Path(f).stem.removeprefix('Source_')+'-leaf',f,False) for f in helpers+[source]]+ [('closed-axioms-review','Solutions/Checks_FermatCanonicalDifferentialChange.lean',True),('source-graph-leaf',u+'ExtractDifferentialGraph.lean',False),('syntax-leaf',u+'ExtractDifferentialSyntax.lean',False),('all-constants-review',u+'AuditAllConstants.lean',True),('direct-solution-leaf',sol,False),('solution-type-axioms-review',u+'AuditSolution.lean',True),('production-gates-review',u+'ProductionGates.lean',True),('consumer-parent-leaf','Theorems/Thm_AbcAdaptation_Tripod_Fermat_Proper_canonicalCuspPolarLinearEquivalence.lean',False),('consumer-closed-review',u+'ChecksCanonicalCuspClosed.lean',True)]
    receipts=[checked(*z) for z in checks];axs=read('all-module-axioms.json');mods={f[:-5].replace('/','.') for f in helpers+[source]};expected={z['name'] for z in graph() if z['module'] in mods}
    assert expected<={z['name'] for z in axs} and all(set(z['axioms'])<={'propext','Classical.choice','Quot.sound'} for z in axs)
    assert read('solution-type-axioms.json')['original_type_equal'] and set(read('solution-type-axioms.json')['axioms'])<={'propext','Classical.choice','Quot.sound'}
    own=helpers+[source,'Solutions/Checks_FermatCanonicalDifferentialChange.lean'];gate=read('production-gates-review-result.json')['request']['worktree_manifest']['input_hashes'];assert all(gate[f]==sha(w/f) for f in own)
    rb=read('final-readbacks.json')['declarations'];assert len(rb)==23 and all(z['source_sha256']==sha(w/z['path']) for z in rb)
    binder=read('compiler-readback-type-review.json');assert binder['passed']
    assert binder['compiler_evidence']['graph_sha256']==sha(b/'decl_graph.jsonl')
    assert binder['original_packet']['sha256']==sha(b/'blind-readbacks-source.json')
    bound={z['declaration']:z for z in rb}
    assert len(binder['declarations'])==22
    for row in binder['declarations']:
        z=bound[row['compiler_name']]
        assert row['passed'] and row['compiler_type']==z['compiler_type']
        assert row['current_source']['sha256']==z['source_sha256']
    assert read('solution-source-closure.json')['source_sha256']==sha(w/sol) and 'sorry' not in (w/sol).read_text()
    for n in dependencies:
        z=read('platform-existing-'+n.removeprefix(pre)+'.json');assert z['theorem_name']==n and z['status']=='Proved' and z['visibility']=='private' and z['mathlib_rev']==ENV
    save('delivery-validation.json',{'passed':True,'original_platform_type_equal':True,'new_platform_nodes':[],'new_open_debt':0,'closed_source_reuse':True,'readbacks':23,'compiler_checks':[z['job_id'] for z in receipts],'existing_proved_dependencies':dependencies,'owned_source_hashes':{f:sha(w/f) for f in own}})
def prose(rows):
    return '\n\n'.join('**'+title+'**\n\n'+'\n\n'.join('`'+z['userName']+'`\n\n'+z[lang] for z in rows) for lang,title in [('en','English'),('zh_Hans','简体中文'),('ja','日本語')])
def publish():
    preflight();s=importlib.util.spec_from_file_location('api',w/'.local/abc-item/api.py');api=importlib.util.module_from_spec(s);s.loader.exec_module(api)
    assert api.base=='https://prove2.me/api/v1';ident=read('target-id.json')['id'];before=read('platform-before-parent.json');current=api.request('/theorems/'+ident)
    assert current['formal_statement']==before['formal_statement'] and current['visibility']=='private' and current['mathlib_rev']==ENV
    for n in dependencies:
        old=read('platform-existing-'+n.removeprefix(pre)+'.json');z=api.request('/theorems/'+old['theorem_id']);assert z['status']=='Proved' and z['theorem_name']==n and z['visibility']=='private' and z['mathlib_rev']==ENV
    ctx=globals()|{'api':api};protocol=(w/'.local/adaptation/platform-tripod-20261113/executed-platform-publish.py').read_text()
    for node in ast.parse(protocol).body:
        if isinstance(node,ast.FunctionDef) and node.name=='verify':exec(compile(ast.Module(body=[node],type_ignores=[]),'<established-protocol>','exec'),ctx)
    rb=read('final-readbacks.json')['declarations'];selected=[z for z in rb if z['userName'] in [target,pre+'canonicalDifferentialChange_source',pre+'DifferentialOrderSource.ord_derivAlong_of_mem',pre+'DifferentialOrderSource.ord_derivAlong_of_notMem']];assert len(selected)==4;quote=(b/'quotation.md').read_text().strip()
    origin='Shinichi Mochizuki, Arithmetic Elliptic Curves in General Position (February 2009), Theorem 2.1, pp.11–12, canonical sheaf and log-canonical pullback context. Official PDF https://www.kurims.kyoto-u.ac.jp/~motizuki/Arithmetic%20Elliptic%20Curves%20in%20General%20Position.pdf ; SHA256 b9dc115af61dca7fe434332ebafddf6a376a9e2926dad4e1ea2dcc0d2441f768. The arbitrary-transcendental differential-change equality is a formal-source auxiliary, not a verbatim paper quotation. Exact formal sources: Belyi/CurveField/Canonical.lean:144,159; CurveDeriv/Basic.lean:209,214; CurveDeriv/Order.lean:83; CurveField/RamIdx.lean:237,257 at 9ce4d3f793d3bc831f2fc7214b7dbad90ea012d8. Original Apache-2.0 notices and exact source hashes retained. Reuses the existing Proved regular local derivative theorem and unit-times-power theorem; no new open node or external source-law assumption. Every supplied CanonicalDivisorData and all proper places, including poles and infinity, are retained. The integer index, residue minimal polynomial, and total order convention are unchanged. All 23 new/reused declaration readbacks are preserved in local evidence; the platform explanation displays the target, main source and two local coefficient theorems.'
    notes=r'''Let $K_u(P)$ be the coefficient fixed by the supplied canonical datum, and put

$$q=\frac{du}{d\varphi}.$$

The reciprocal derivative identity proves $q\ne0$. At a regular place, the local power formula and the actual residue minimal polynomial give $\operatorname{ord}_P(d\psi/d\pi)=e_\psi(P)-1$. At a pole, write $\psi^{-1}=u\pi^e$ with $u$ a unit; differentiating the inverse gives order $-e_\psi(P)-1$. The integer ramification index is retained, with an explicit positive natural exponent only in this local power expression. These two cases compute the differential coefficient $K_\varphi(P)$ at every proper place. The chain rule gives

$$\frac{du}{d\pi}=\frac{d\varphi}{d\pi}\,q.$$

Both factors are proved nonzero before applying additivity of their orders. The supplied canonical coefficient contract therefore yields

$$K_u(P)=K_\varphi(P)+\operatorname{ord}_P(q).$$

This is the required positive principal-order identity for the same supplied canonical divisor, without excluding poles or infinity.'''
    explanation=notes+'\n\n'+quote+'\n\n'+prose(selected)+'\n\n'+origin;assert len(explanation)<=50000,len(explanation)
    tag='prove-canonicalDifferentialChange';req={'theorem_id':ident,'proof_type':'prove','file':sol,'source_sha256':sha(w/sol),'explanation':explanation}
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
    parentid='d6a1ff14-5bc3-4b24-bdda-966c29d20c2c';p=api.request('/theorems/'+parentid);assert p['status']=='Proved';save('platform-after-canonicalCuspPolarLinearEquivalence.json',p)
    print('Exact canonical differential change ACCEPTED and Proved; canonical-cusp parent Proved; full graph fetched.',flush=True)
if __name__=='__main__':{'bind':bind,'generate':generate,'preflight':preflight,'publish':publish}[sys.argv[1]]()
