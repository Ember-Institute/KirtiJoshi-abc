from pathlib import Path
import ast, hashlib, importlib.util, json, re, sys, time, urllib.request, urllib.error, uuid

r=Path('/home/admin-wsl/Coq/abc');w=r/'prove2me_workspace';b=w/'.local/adaptation/avoidance-regularity-sourceproof-20261114'
u='.local/adaptation/avoidance-regularity-sourceproof-20261114/';pre='AbcAdaptation.Tripod.Fermat.Proper.'
target=pre+'avoidanceRegularity';source='Theorems/Thm_'+target.replace('.','_')+'.lean';sol=u+'Solution_avoidanceRegularity.lean'
ENV='0df444a360eaa60ab8c11dca51a86af692955474';ROOT='e33ff731-60a7-43ef-87ae-c12aeba23cb5'
def read(n):return json.loads((b/n).read_text())
def save(n,z):(b/n).write_text(json.dumps(z,ensure_ascii=False,indent=2)+'\n')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def generate():
    facts=read('compiler-facts.json');assert facts['name']==target and facts['file']==source
    spans=facts['name_spans'];assert len(spans)==1 and spans[0]['nameText']=='avoidanceRegularity'
    sp=spans[0];raw=(w/source).read_bytes();assert raw[sp['start']:sp['end']]==b'avoidanceRegularity'
    renamed=raw[:sp['start']]+b'closedAvoidanceSource'+raw[sp['end']:]
    code=renamed.decode();assert all(line.startswith('import Definitions.') for line in code.splitlines() if line.startswith('import '))
    formal=read('platform-before-parent.json')['formal_statement'];assert formal.startswith('theorem '+target+' : ') and formal.endswith(' := by sorry')
    exact=formal.replace('theorem '+target+' : ','theorem solution : ',1).removesuffix(' := by sorry')
    code=code.rstrip()+'\n\n'+exact+' :=\n  '+pre+'closedAvoidanceSource\n';assert 'sorry' not in code and 'import Theorems.' not in code
    (w/sol).write_text(code)
    expected=formal.replace('theorem '+target+' : ','theorem PlatformOriginalType : ',1).removesuffix(' := by sorry')+' := solution\n'
    audit='import Lean\n'+code+'\n'+expected+'''\nopen Lean
run_meta do
  let a ← getConstInfo `solution
  let e ← getConstInfo `PlatformOriginalType
  unless ← Lean.Meta.isDefEq a.type e.type do throwError "Original platform type differs"
  let axs ← collectAxioms `solution
  for ax in axs do
    unless #[`propext, `Classical.choice, `Quot.sound].contains ax do throwError "Unexpected solution axiom {ax}"
  IO.FS.writeFile "OUTPUT" (Json.pretty (Json.mkObj [("type",Json.str (← Lean.Meta.ppExpr a.type).pretty),("axioms",toJson (axs.map toString)),("original_type_equal",Json.bool true)]))
'''.replace('OUTPUT',u+'solution-type-axioms.json');(b/'AuditSolution.lean').write_text(audit)
    rows=read('blind-readbacks-original.json')['declarations'];assert len(rows)==1;row=rows[0];assert row['userName']==target and sha(Path(row['path']))==row['sha256']
    save('final-readbacks.json',{'declarations':[{'declaration':target,'userName':target,'path':source,'source_sha256':sha(w/source),'compiler_type':facts['type'],'source_span':{'start_line':facts['start_line'],'end_line':facts['end_line']},'blind_original_path':row['path'],'blind_original_sha256':row['sha256'],**row['statements'],'proof_notes':row.get('proof_notes'),'quotation':None}],'blind_readback':True,'compiler_bound':True})
    save('solution-source-closure.json',{'source':sol,'source_sha256':sha(w/sol),'source_theorem_sha256':sha(w/source),'compiler_name_span':sp,'proof_copied_verbatim':True,'no_theorem_imports':True,'new_nodes':[],'new_open_debt':0})
    quotes=read('mochizuki-source-quotations.json')['quotations'];q=next(z for z in quotes if z['id']=='NBM-T25-P6-BRANCH-CONTEXT')
    text=q['exact_quotation']
    # Preserve quoted words and render its original mathematical notation.
    expressions=['X=\\mathbb{P}^1_{\\overline{\\mathbb{Q}}}','\\mathbb{P}^1_{\\overline{\\mathbb{Q}}}','\\psi(S)','\\psi','T=\\{\\beta\\}','\\beta\\in\\mathbb{P}^1(\\overline{\\mathbb{Q}})\\backslash\\{\\infty\\}']
    text=re.sub('|'.join(re.escape(e) for e in sorted(expressions,key=len,reverse=True)),lambda match:'$'+match.group(0)+'$',text)
    quote='> '+text+'\n\n— Shinichi Mochizuki, *Noncritical Belyi Maps*, proof of Theorem 2.5, printed p.6.\n\nSource context: '+q['official_url']+' . PDF SHA256 '+q['pdf_sha256']+'. This quotation gives the noncritical-map and branch-locus context; the exact local regularity lemma is the formal-source consequence stated below.'
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
    receipts=[checked('avoidanceRegularity-leaf',source),checked('closed-axioms-review','Solutions/Checks_FermatAvoidanceRegularity.lean',True),checked('compiler-facts-leaf',u+'ExtractAvoidanceFacts.lean'),checked('direct-solution-leaf',sol),checked('solution-type-axioms-review',u+'AuditSolution.lean',True),checked('production-gates-review',u+'ProductionGates.lean',True)]
    facts=read('compiler-facts.json');assert facts['name']==target and facts['module_axioms']
    assert all(set(z['axioms'])<={'propext','Classical.choice','Quot.sound'} for z in facts['module_axioms'])
    types=read('solution-type-axioms.json');assert types['original_type_equal'] and types['type']==facts['type']
    assert set(types['axioms'])<={'propext','Classical.choice','Quot.sound'}
    closure=read('solution-source-closure.json');assert closure['source_sha256']==sha(w/sol)
    rb=read('final-readbacks.json')['declarations'];assert len(rb)==1 and rb[0]['source_sha256']==sha(w/source) and rb[0]['compiler_type']==facts['type']
    inputs=receipts[-1]['request']['worktree_manifest']['input_hashes'];assert inputs[source]==sha(w/source)
    save('delivery-validation.json',{'passed':True,'original_platform_type_equal':True,'new_nodes':[],'new_open_debt':0,'compiler_checks':[z['job_id'] for z in receipts],'readbacks':1,'owned_source_hashes':{source:sha(w/source),'Solutions/Checks_FermatAvoidanceRegularity.lean':sha(w/'Solutions/Checks_FermatAvoidanceRegularity.lean')}})
def prose(rows):
    return '\n\n'.join('**'+title+'**\n\n'+'\n\n'.join('`'+z['userName']+'`\n\n'+z[lang] for z in rows) for lang,title in [('en','English'),('zh_Hans','简体中文'),('ja','日本語')])
def publish():
    preflight();spec=importlib.util.spec_from_file_location('api',w/'.local/abc-item/api.py');api=importlib.util.module_from_spec(spec);spec.loader.exec_module(api)
    assert api.base=='https://prove2.me/api/v1';ident=read('target-id.json')['id'];before=read('platform-before-parent.json');current=api.request('/theorems/'+ident)
    assert current['formal_statement']==before['formal_statement'] and current['visibility']=='private' and current['mathlib_rev']==ENV
    ctx=globals()|{'api':api};protocol=(w/'.local/adaptation/platform-tripod-20261113/executed-platform-publish.py').read_text()
    for node in ast.parse(protocol).body:
        if isinstance(node,ast.FunctionDef) and node.name=='verify':exec(compile(ast.Module(body=[node],type_ignores=[]),'<established-protocol>','exec'),ctx)
    rows=read('final-readbacks.json')['declarations'];quote=(b/'quotation.md').read_text().strip()
    origin='Shinichi Mochizuki, Noncritical Belyi Maps (May 2004), proof of Theorem 2.5, p.6; official PDF https://www.kurims.kyoto-u.ac.jp/~motizuki/Noncritical%20Belyi%20Maps.pdf . The quotation supplies the noncritical-map context. Exact formal-source lemma Genl.Curves.mem_of_notMem_belyiCusps, Genl/Curves/BelyiDescent.lean:127–139 at ea2846c877d1e16d8f0b911a5fed07f5ee69eaaf, SHA256 fab56e0073e8ad10a1cea54552ba10a62df5cef54da2f572136975cffe375596. The local consumer returns the already regular (phi-1) inverse directly; it omits the source final sign change for (1-phi) inverse. All actual proper places and exact original hypotheses retained, including formal zero/unit boundary cases; no new nonzero, transcendence, Belyi, or source-law assumption is added. Apache-2.0 attribution retained; no Iut/Genl runtime import or new theorem node.'
    explanation=quote+'\n\n'+prose(rows)+'\n\n'+origin;tag='prove-avoidanceRegularity';req={'theorem_id':ident,'proof_type':'prove','file':sol,'source_sha256':sha(w/sol),'explanation':explanation}
    if (b/(tag+'-verify-submit.json')).exists():assert read(tag+'-verify-request.json')==req
    else:
        assert not (b/(tag+'-verification-requested.json')).exists(),'Reconcile prior POST before retry'
        save(tag+'-verification-requested.json',req)
    result=ctx['verify'](tag,ident,sol,explanation);assert result['status']=='ACCEPTED'
    patch={'natural_language_statement':quote+'\n\n'+prose(rows),'source':origin};save('parent-metadata-patch-request.json',patch);current=api.request('/theorems/'+ident)
    if not all(current.get(k)==v for k,v in patch.items()):save('parent-metadata-patch-response.json',api.request('/theorems/'+ident,patch,'PATCH'))
    current=api.request('/theorems/'+ident);assert current['status']=='Proved' and current['formal_statement']==before['formal_statement'] and all(current[k]==v for k,v in patch.items());save('platform-after-parent.json',current)
    sys.path.insert(0,str(w/'.local/adaptation/northcott-sourceproof-20261114'));from graph_completion import fetch_complete_math_graph
    save('root-graph-after.json',fetch_complete_math_graph(api,ROOT,save,'root-graph-after'));ls=[]
    while True:
        page=api.request('/theorems/'+ROOT+'/open-leaves?limit=50&offset='+str(len(ls)));save('root-frontier-after-page-'+str(len(ls))+'.json',page);ls+=page['open_leaves']
        if len(ls)>=page['total']:break
    assert len(ls)==page['total'];save('root-frontier-after.json',{'open_leaves':ls,'total':page['total'],'all_pages_fetched':True});print('avoidanceRegularity ACCEPTED and Proved; actual graph read back.',flush=True)
if __name__=='__main__':{'generate':generate,'preflight':preflight,'publish':publish}[sys.argv[1]]()
