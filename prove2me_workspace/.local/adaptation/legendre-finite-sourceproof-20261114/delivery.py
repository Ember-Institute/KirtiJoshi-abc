from pathlib import Path
import ast, hashlib, importlib.util, json, sys, time, urllib.request, urllib.error, uuid

r=Path('/home/admin-wsl/Coq/abc');w=r/'prove2me_workspace';b=w/'.local/adaptation/legendre-finite-sourceproof-20261114'
u='.local/adaptation/legendre-finite-sourceproof-20261114/';pre='AbcAdaptation.Tripod.'
targets=['legendreFiniteUpperBound','legendreFiniteLowerBound'];parent=pre+'canonicalLegendreHeightComparison'
ROOT='e33ff731-60a7-43ef-87ae-c12aeba23cb5';ENV='0df444a360eaa60ab8c11dca51a86af692955474'
mods=['TripodLegendreValuationBounds','TripodFinitePlaceArithmetic','TripodFiniteHeightSupport','TripodLegendreFinitePlaceBounds','TripodFinitePrimeCounting']
def read(n):return json.loads((b/n).read_text())
def save(n,z):(b/n).write_text(json.dumps(z,ensure_ascii=False,indent=2)+'\n')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def generate():
    graph=[json.loads(l) for l in (b/'decl_graph.jsonl').read_text().splitlines() if l.strip()]
    syntax=read('syntax-boundaries.json');rows={z['name']:z for z in graph}
    selectedmods=['Solutions.Source_'+m for m in mods]
    closure={}
    for target in targets:
        reached=set();todo=[pre+target]
        while todo:
            n=todo.pop()
            if n in reached:continue
            reached.add(n);z=rows.get(n)
            if z:todo+=z['typeDeps']+z['valueDeps']
        imported=[];bodies=[];selected=[]
        files=['Solutions/Source_'+m+'.lean' for m in mods]+['Theorems/Thm_'+pre.replace('.','_')+target+'.lean']
        for path in files:
            module=path[:-5].replace('/','.');decls=[z for z in graph if z['module']==module and z['startLine']>0]
            keep=[z for z in decls if z['name'] in reached]
            if not keep:continue
            raw=(w/path).read_bytes();edits=[]
            for z in decls:
                found=[q for q in syntax if q['file']==path and q['nameText']==z['userName'].rsplit('.',1)[-1]]
                assert len(found)==1,(z['name'],len(found));q=found[0]
                if z['name'] not in reached:
                    start=q['declStart']['offset'];doc=q.get('docstring')
                    if doc:start=min(start,doc['start']['offset'])
                    edits.append((start,q['declEnd']['offset'],b''))
                elif z['name']==pre+target:
                    span=q['nameRange'];assert raw[span['start']['offset']:span['end']['offset']].decode()==target
                    edits.append((span['start']['offset'],span['end']['offset'],b'closedFiniteSource'))
                else:selected.append(z['name'])
            for start,end,value in sorted(edits,reverse=True):raw=raw[:start]+value+raw[end:]
            text=raw.decode();lines=[]
            for line in text.splitlines(keepends=True):
                if line.startswith('import '):
                    imp=line.strip()
                    if imp.startswith('import Solutions.Source_'):continue
                    assert not imp.startswith('import Theorems.'),imp
                    if imp not in imported:imported.append(imp)
                else:lines.append(line)
            bodies.append(''.join(lines).strip())
        assert not any(x.startswith('import Solutions.') for x in imported)
        pred='LegendreFiniteUpperBound' if 'Upper' in target else 'LegendreFiniteLowerBound'
        code='\n'.join(imported)+'\n\n'+'\n\n'.join(bodies)+'\n\ntheorem solution : '+pre+pred+' := '+pre+'closedFiniteSource\n'
        assert 'sorry' not in code and ('theorem '+target) not in code
        out=b/('Solution_'+target+'.lean');out.write_text(code)
        # Same exact source prefix, followed only by a type/axiom check.
        audit=code+'''\nopen Lean
run_meta do
  let info ← getConstInfo `solution
  let expected := Lean.mkConst `PREDICATE
  unless ← Lean.Meta.isDefEq info.type expected do throwError "Exact original target type differs"
  let axs ← collectAxioms `solution
  for ax in axs do
    unless #[`propext, `Classical.choice, `Quot.sound].contains ax do throwError "Unexpected solution axiom {ax}"
  IO.FS.writeFile "OUTPUT" (Json.pretty (Json.mkObj [("type",Json.str (← Lean.Meta.ppExpr info.type).pretty),("axioms",toJson (axs.map toString))]))
'''.replace('PREDICATE',pre+pred).replace('OUTPUT',u+'solution-'+target+'-type.json')
        (b/('Audit_'+target+'.lean')).write_text(audit)
        closure[target]={'source':str(out.relative_to(w)),'source_sha256':sha(out),'inlined_declarations':selected,'exact_target_predicate':pre+pred,'compiler_name_spans_used':True,'no_source_module_imports':True}
    new={z['name'] for z in graph if z['module'] in selectedmods and z['startLine']>0}
    consumed=set().union(*(set(z['inlined_declarations']) for z in closure.values()))
    assert new<=consumed,sorted(new-consumed)
    save('solution-source-closure.json',closure)
def bind():
    original=read('blind-readbacks-original.json')['declarations'];graph=[json.loads(l) for l in (b/'decl_graph.jsonl').read_text().splitlines() if l.strip()]
    out=[];mapping=read('module-path-map.json')
    for row in original:
        path=row['path'];rel=str(Path(path).relative_to('/tmp/p2m-legendre-finite-next-20261114'))
        newpath=mapping.get(rel,rel);module=newpath[:-5].replace('/','.')
        assert sha(Path(path))==row['sha256'],path
        name=row['userName'];found=[z for z in graph if z['module']==module and z['userName']==name and z['startLine']>0]
        assert len(found)==1,(name,module,len(found));z=found[0]
        out.append({'declaration':z['name'],'userName':name,'path':newpath,'module':module,'source_sha256':sha(w/newpath),'compiler_type':z['elaboratedType'],'source_span':{'start_line':z['startLine'],'end_line':z['endLine']},'blind_original_sha256':row['sha256'],**row['statements'],'quotation':None,'proof_notes':row.get('proof_notes')})
    assert len(out)==48,len(out)
    save('final-readbacks.json',{'declarations':out,'blind_readback':True,'compiler_bound':True,'paper_quotations_separate':True})
def check(tag,source,review=False):
    z=read(tag+'-result.json');q=z['request'];rs=z['result']
    assert z['status']=='succeeded' and rs['exit_code']==0 and 'sorryAx' not in rs['stdout'],tag
    assert q['exclusive'] and q['workspace']==str(w) and q['parameters']=={'source':source},tag
    assert q['worktree_manifest']['source_sha256']==sha(w/source),tag
    assert rs['actual_arguments']==['lean',source] and rs['snapshot']['workspace_mode']=='exclusive_worktree' and rs['snapshot']['snapshot_id'] is None,tag
    if review:assert rs['review']['passed'],tag
    return z
def preflight():
    receipts=[]
    for m in mods:receipts.append(check(m+'-leaf','Solutions/Source_'+m+'.lean'))
    for n in targets:receipts.append(check(n+'-leaf','Theorems/Thm_'+pre.replace('.','_')+n+'.lean'))
    receipts.append(check('parent-solution-leaf','Solutions/Sol_LegendreFiniteSourceClosure.lean'))
    receipts.append(check('closed-axioms-review','Solutions/Checks_LegendreFiniteSourceClosure.lean',True))
    receipts.append(check('source-graph-leaf',u+'ExtractFiniteGraph.lean'))
    receipts.append(check('syntax-leaf',u+'ExtractFiniteSyntax.lean'))
    receipts.append(check('all-constants-review',u+'AuditAllConstants.lean',True))
    for n in targets:
        receipts.append(check('direct-'+n+'-leaf',u+'Solution_'+n+'.lean'))
        receipts.append(check('direct-'+n+'-audit',u+'Audit_'+n+'.lean',True))
        z=read('solution-'+n+'-type.json');assert set(z['axioms'])<={'propext','Classical.choice','Quot.sound'}
    receipts.append(check('production-gates-review',u+'ProductionGates.lean',True))
    axs=read('all-module-axioms.json');assert len(axs)>=47 and all(set(z['axioms'])<={'propext','Classical.choice','Quot.sound'} for z in axs)
    closure=read('solution-source-closure.json');assert all(sha(w/z['source'])==z['source_sha256'] for z in closure.values())
    rb=read('final-readbacks.json');assert rb['compiler_bound'] and len(rb['declarations'])==48
    for z in rb['declarations']:assert sha(w/z['path'])==z['source_sha256']
    save('delivery-validation.json',{'passed':True,'exact_target_types_preserved':True,'no_new_platform_nodes':True,'no_open_debt_added':True,'closed_source_chain':True,'compiler_checks':[z['job_id'] for z in receipts],'readbacks':48,'owned_source_hashes':{z['path']:z['source_sha256'] for z in rb['declarations']}})
def prose(rows):
    assert rows
    return '\n\n'.join('**'+title+'**\n\n'+'\n\n'.join('`'+z['userName']+'`\n\n'+z[lang] for z in rows) for lang,title in [('en','English'),('zh_Hans','简体中文'),('ja','日本語')])
def publish():
    preflight();spec=importlib.util.spec_from_file_location('api',w/'.local/abc-item/api.py');api=importlib.util.module_from_spec(spec);spec.loader.exec_module(api)
    assert api.base=='https://prove2.me/api/v1'
    ctx=globals()|{'api':api}
    protocol=(w/'.local/adaptation/platform-tripod-20261113/executed-platform-publish.py').read_text()
    for node in ast.parse(protocol).body:
        if isinstance(node,ast.FunctionDef) and node.name=='verify':exec(compile(ast.Module(body=[node],type_ignores=[]),'<established-protocol>','exec'),ctx)
    quote=(b/'quotation.md').read_text().strip();rb=read('final-readbacks.json')['declarations'];closure=read('solution-source-closure.json');ids=read('target-ids.json')
    source=read('source-consumer-ledger.json');sourcehash={z['path']:z['sha256'] for z in source['source_files']}
    common='Shinichi Mochizuki, Inter-universal Teichmuller Theory IV, Corollary 2.2(i), p.41 and proof p.43; Arithmetic Elliptic Curves in General Position, Proposition 3.4 and Lemma 3.7, pp.17,19. Official quotations are recorded above. Explicit integer valuation case splits, finite-place weights f log p, and precise constants are archived formal-source auxiliary arguments, not verbatim paper quotations. Full copied source proof independently adapted under Mathlib 0df444a; Apache-2.0 notices retained. Source hashes: '+json.dumps(sourcehash,sort_keys=True)+'. Historical upstream source revision unverified. No Iut/Genl runtime import or added mathematical assumption; no Scene1/Prologue boundary change and no global 3.12 proof.'
    for n in targets:
        ident=ids[pre+n];before=read('platform-before-'+n+'.json');current=api.request('/theorems/'+ident)
        assert current['formal_statement']==before['formal_statement'] and current['visibility']=='private' and current['mathlib_rev']==ENV
        selectednames=set(closure[n]['inlined_declarations'])|{pre+n};selected=[z for z in rb if z['declaration'] in selectednames]
        assert len(selected)==len(selectednames)
        explanation=quote+'\n\n'+prose(selected)+'\n\n'+common
        tag='prove-'+n;file=closure[n]['source'];request={'theorem_id':ident,'proof_type':'prove','file':file,'source_sha256':sha(w/file),'explanation':explanation}
        if (b/(tag+'-verify-submit.json')).exists():assert read(tag+'-verify-request.json')==request
        else:
            assert not (b/(tag+'-verification-requested.json')).exists(),'Reconcile prior POST before retry'
            save(tag+'-verification-requested.json',request)
        result=ctx['verify'](tag,ident,file,explanation);assert result['status']=='ACCEPTED'
        after=api.request('/theorems/'+ident);assert after['status']=='Proved' and after['formal_statement']==before['formal_statement'];save('platform-after-'+n+'.json',after)
    # Existing canonical Legendre reduction must close through these exact children.
    p=api.request('/theorems/84dbea7a-d8ba-4240-8676-b0260f50392e');assert p['theorem_name']==parent and p['status']=='Proved';save('platform-after-parent.json',p)
    sys.path.insert(0,str(w/'.local/adaptation/northcott-sourceproof-20261114'));from graph_completion import fetch_complete_math_graph
    save('root-graph-after.json',fetch_complete_math_graph(api,ROOT,save,'root-graph-after'));leaves=[]
    while True:
        z=api.request('/theorems/'+ROOT+'/open-leaves?limit=50&offset='+str(len(leaves)));save('root-frontier-after-page-'+str(len(leaves))+'.json',z);leaves+=z['open_leaves']
        if len(leaves)>=z['total']:break
    assert len(leaves)==z['total'];save('root-frontier-after.json',{'open_leaves':leaves,'total':z['total'],'all_pages_fetched':True})
    print('Both finite source proofs ACCEPTED; existing canonical Legendre parent Proved.',flush=True)
if __name__=='__main__':
    {'generate':generate,'bind':bind,'preflight':preflight,'publish':publish}[sys.argv[1]]()
