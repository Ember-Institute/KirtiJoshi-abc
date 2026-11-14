from pathlib import Path
import ast, hashlib, importlib.util, json, sys, time, urllib.request, urllib.error, uuid

r=Path('/home/admin-wsl/Coq/abc');w=r/'prove2me_workspace';b=w/'.local/adaptation/legendre-height-20261114'
u='.local/adaptation/legendre-height-20261114/';pre='AbcAdaptation.Tripod.'
ENV='0df444a360eaa60ab8c11dca51a86af692955474';ROOT='e33ff731-60a7-43ef-87ae-c12aeba23cb5'
modules=['TripodLegendreHeightComparisonInputs','TripodLegendreHeightBasics','TripodLegendreHeightComparisonComposition']
children=['legendreFiniteUpperBound','legendreFiniteLowerBound','legendreArchimedeanTripleBound','legendreZeroJRootOfUnity']
closed=children[2:]
def read(n):return json.loads((b/n).read_text())
def save(n,z):(b/n).write_text(json.dumps(z,ensure_ascii=False,indent=2)+'\n')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def checked(tag,source,review=False,expected_sorry=False):
    z=read(tag+'-result.json');q=z['request'];rs=z['result']
    assert z['status']=='succeeded' and rs['exit_code']==0,tag
    assert q['workspace']==str(w) and q['exclusive'] and q['parameters']=={'source':source},tag
    assert q['worktree_manifest']['source_sha256']==sha(w/source),tag
    assert rs['actual_arguments']==['lean',source] and rs['snapshot']['workspace_mode']=='exclusive_worktree' and rs['snapshot']['snapshot_id'] is None,tag
    assert ('sorryAx' in rs['stdout'])==expected_sorry,tag
    if review:assert rs['review']['passed'],tag
    return z
def bind():
    graph=[json.loads(l) for l in (b/'decl_graph.jsonl').read_text().splitlines() if l.strip()]
    rows=read('blind-readbacks-original.json')['declarations'];out=[]
    for row in rows:
        if row['scope']!='draft' and row['userName']!=pre+'canonicalLegendreHeightComparison':continue
        found=[z for z in graph if z['module']==row['module'] and z['userName']==row['userName'] and z['startLine']>0]
        assert len(found)==1,(row['userName'],len(found))
        z=found[0];path=z['module'].replace('.','/')+'.lean';p=w/path
        old=Path(row['path']);assert sha(old)==row['sha256'],old
        out.append({'declaration':z['name'],'userName':z['userName'],'module':z['module'],'path':path,'source_sha256':sha(p),'compiler_type':z['elaboratedType'],'source_span':{'start_line':z['startLine'],'end_line':z['endLine']},**row['statements'],'blind_original_path':row['path'],'blind_original_sha256':row['sha256'],'proof_notes':row.get('proof_notes'),'quotation':None})
    assert len(out)==21,len(out)
    save('final-readbacks.json',{'declarations':out,'blind_readback':True,'compiler_bound':True,'paper_quotations_separate':True})
    current={z['name']:z for z in graph};new={z['name'] for z in graph if z['module'] in ['Definitions.Def_'+m for m in modules] and z['startLine']>0}
    reached=set();todo=['solution',pre+'legendreArchimedeanTripleBound',pre+'legendreZeroJRootOfUnity']
    while todo:
        n=todo.pop()
        if n in reached:continue
        reached.add(n);z=current.get(n)
        if z:todo+=z['typeDeps']+z['valueDeps']
    assert new<=reached,sorted(new-reached)
    assert not any(z['kind']=='axiom' for z in graph if z['name'] in new)
    save('consumer-closure.json',{'all_new_definitions_consumed':True,'declarations':sorted(new),'roots':['solution']+[pre+n for n in closed]})
def preflight():
    receipts=[]
    for m in modules:receipts.append(checked(m+'-leaf','Definitions/Def_'+m+'.lean'))
    for n in children:receipts.append(checked(n+'-leaf','Theorems/Thm_'+pre.replace('.','_')+n+'.lean'))
    receipts.append(checked('parent-solution-leaf','Solutions/Sol_CanonicalLegendreHeightComparison.lean'))
    receipts.append(checked('closed-axioms-review','Solutions/Checks_TripodLegendreHeightClosed.lean',True))
    receipts.append(checked('reduction-axioms-leaf','Solutions/Checks_TripodLegendreHeightReduction.lean',expected_sorry=True))
    for n in closed:receipts.append(checked('solution-'+n+'-leaf',u+'Solution_'+n+'.lean'))
    receipts.append(checked('source-graph-leaf',u+'ExtractLegendreGraph.lean'))
    receipts.append(checked('types-leaf',u+'ValidateTypes.lean'))
    receipts.append(checked('all-constants-review',u+'AuditAllConstants.lean',True))
    receipts.append(checked('production-gates-review',u+'ProductionGates.lean',True))
    assert read('parent-types-equal.json') is True
    graph={z['name']:z for z in map(json.loads,(b/'decl_graph.jsonl').read_text().splitlines()) if z}
    pp=read('upload-elaborated-types.json');assert len(pp)==4
    assert all(z['type']==graph[z['name']]['elaboratedType'] for z in pp)
    axs=read('all-module-axioms.json');assert len(axs)>=17
    assert all(set(z['axioms'])<={'propext','Classical.choice','Quot.sound'} for z in axs)
    owned=['Definitions/Def_'+m+'.lean' for m in modules]+['Theorems/Thm_'+pre.replace('.','_')+n+'.lean' for n in children]+['Solutions/Sol_CanonicalLegendreHeightComparison.lean']
    last=receipts[-1]['request']['worktree_manifest']['input_hashes']
    assert all(last[f]==sha(w/f) for f in owned)
    assert len(read('final-readbacks.json')['declarations'])==21
    for f in ['Solutions/Sol_CanonicalLegendreHeightComparison.lean']+[u+'Solution_'+n+'.lean' for n in closed]:
        assert b'sorry' not in (w/f).read_bytes()
    assert sha(r/'refer/iut/Iut/Tripod/Height.lean')==sha(b/'reference/Height.lean')
    save('delivery-validation.json',{'passed':True,'exact_parent_type_preserved':True,'child_types_preserved':True,'all_new_definitions_consumed':True,'closed_axioms':['propext','Classical.choice','Quot.sound'],'open_children':children[:2],'compiler_checks':[z['job_id'] for z in receipts],'owned_source_hashes':{f:sha(w/f) for f in owned}})
def prose(rows):
    assert rows
    return '\n\n'.join('**'+title+'**\n\n'+'\n\n'.join('`'+z['userName']+'`\n\n'+z[lang] for z in rows) for lang,title in [('en','English'),('zh_Hans','简体中文'),('ja','日本語')])
def publish():
    preflight();spec=importlib.util.spec_from_file_location('api',w/'.local/abc-item/api.py');api=importlib.util.module_from_spec(spec);spec.loader.exec_module(api)
    assert api.base=='https://prove2.me/api/v1'
    # Reuse protocol functions; do not execute the old unit's top-level actions.
    protocol=(w/'.local/adaptation/platform-tripod-20261113/executed-platform-publish.py').read_text()
    context=globals()|{'api':api}
    for node in ast.parse(protocol).body:
        if isinstance(node,ast.FunctionDef) and node.name in ['publish','verify']:
            exec(compile(ast.Module(body=[node],type_ignores=[]),'<established-protocol>','exec'),context)
    oldpublish,oldverify=context['publish'],context['verify']
    def pub(tag,endpoint,payload):
        if (b/(tag+'-submit.json')).exists():assert read(tag+'-payload.json')==payload
        else:
            assert not (b/(tag+'-publication-requested.json')).exists(),'Reconcile pending publication '+tag
            save(tag+'-publication-requested.json',{'endpoint':endpoint,'payload':payload})
        return oldpublish(tag,endpoint,payload)
    def verify(tag,ident,file,explanation,expected):
        req={'theorem_id':ident,'proof_type':'prove','file':file,'source_sha256':sha(w/file),'explanation':explanation}
        if (b/(tag+'-verify-submit.json')).exists():
            previous=read(tag+'-verify-request.json')
            if previous!=req:
                archived=read(tag+'-submitted-source.json');raw=archived['source_text'].encode()
                assert previous==req|{'source_sha256':archived['sha256']}
                assert hashlib.sha256(raw).hexdigest()==archived['sha256'] and raw.rstrip()+b'\n'==(w/file).read_bytes()
            submitted=read(tag+'-verify-submit.json');z=api.request('/verify?submission_id='+submitted['submission_id'])
            assert z['status']==expected;save(tag+'-verify-result.json',z);return z
        else:
            assert not (b/(tag+'-verification-requested.json')).exists(),'Reconcile pending verification '+tag
            save(tag+'-verification-requested.json',req)
        z=oldverify(tag,ident,file,explanation);assert z['status']==expected,(tag,z['status']);return z
    rb=read('final-readbacks.json')['declarations'];quote=(b/'quotation.md').read_text().strip()
    common='Shinichi Mochizuki, Inter-universal Teichmuller Theory IV, Corollary 2.2(i), printed p.41 and proof p.43; https://www.kurims.kyoto-u.ac.jp/~motizuki/Inter-universal%20Teichmuller%20Theory%20IV.pdf . Arithmetic Elliptic Curves in General Position, Proposition 3.4 and proof of Lemma 3.7, pp.17,19. The original quotations provide mathematical context; the explicit local bounds and zero-j algebra belong to the archived formal source Iut/Tripod/Height.lean, SHA256 '+sha(b/'reference/Height.lean')+'. Historical upstream revision unverified. Independently adapted under Mathlib 0df444a, with Apache-2.0 notices retained; no Iut/Genl/Heights/Belyi runtime dependency. No degree bound is added and the actual point field Q(x) is retained. The numeric height definition does not construct separate elliptic-curve providers or prove a 3.12 theorem.'
    for m in modules:
        path='Definitions/Def_'+m+'.lean';selected=[z for z in rb if z['path']==path];assert selected
        pub('def-'+m,'/submit-definition',{'definition_name':m,'definition_title':m+' — Legendre height comparison','definition':(w/path).read_text(),'natural_language_statement':quote+'\n\n'+prose(selected),'source':common,'env':ENV,'private':True,'tags':['abc-conjecture','arithmetic-geometry']})
    items=read('upload-problem-items.json')
    titles=['Finite upper bound for the Legendre j-height','Finite lower bound for the Legendre j-height on compactly bounded sets','Archimedean error bounds for the three Legendre coordinates','Vanishing Legendre j-invariant implies a sixth root of unity']
    for item,title in zip(items,titles):
        selected=[z for z in rb if z['declaration']==item['theorem_name']];assert len(selected)==1
        item.update(theorem_title=title,natural_language_statement=quote+'\n\n'+prose(selected),source=common,tags=['abc-conjecture','arithmetic-geometry'])
    results=pub('legendre-children','/submit-problem',{'problems':items,'env':ENV,'private':True});assert len(results)==4
    ids={z['theorem_name']:z['theorem_id'] for z in results};save('published-child-ids.json',ids)
    for n in closed:
        selected=[z for z in rb if z['declaration']==pre+n]
        verify('prove-'+n,ids[pre+n],u+'Solution_'+n+'.lean',quote+'\n\n'+prose(selected)+'\n\n'+common,'ACCEPTED')
    parent=read('target-id.json')['id'];before=read('platform-before-parent.json');current=api.request('/theorems/'+parent)
    assert current['formal_statement']==before['formal_statement'] and current['visibility']=='private'
    selected=[z for z in rb if z['declaration'] in [pre+'canonicalLegendreHeightComparison_of_source_children','solution']]
    explanation=quote+'\n\n'+prose(selected)+'\n\n'+common+' The upper bound has error log(2)/3. The nonzero-j lower bound has error c|V|+c+log(2)/3; in the zero-j case the sixth-root identity makes its logarithmic height zero. Their maximum supplies a uniform absolute-discrepancy bound, including empty compactly bounded sets. The two finite-place source estimates remain explicit Open children.'
    verify('reduce-parent',parent,'Solutions/Sol_CanonicalLegendreHeightComparison.lean',explanation,'SKETCH_ACCEPTED')
    selected=[z for z in rb if z['declaration']==pre+'canonicalLegendreHeightComparison'];assert len(selected)==1
    patch={'natural_language_statement':quote+'\n\n'+prose(selected),'source':common}
    save('parent-metadata-patch-request.json',patch)
    current=api.request('/theorems/'+parent)
    if not all(current.get(k)==v for k,v in patch.items()):save('parent-metadata-patch-response.json',api.request('/theorems/'+parent,patch,'PATCH'))
    for name,ident in [(pre+n,ids[pre+n]) for n in children]+[(pre+'canonicalLegendreHeightComparison',parent)]:
        z=api.request('/theorems/'+ident);assert z['theorem_name']==name and z['mathlib_rev']==ENV and z['visibility']=='private'
        assert z['status']==('Proved' if name in [pre+n for n in closed] else 'Open')
        if ident==parent:
            assert z['formal_statement']==before['formal_statement'] and all(z[k]==v for k,v in patch.items());save('platform-after-parent.json',z)
        else:save('platform-after-'+name.removeprefix(pre)+'.json',z)
    sys.path.insert(0,str(w/'.local/adaptation/northcott-sourceproof-20261114'));from graph_completion import fetch_complete_math_graph
    graph=fetch_complete_math_graph(api,ROOT,save,'root-graph-after');save('root-graph-after.json',graph)
    mathnodes={z['theorem_id']:z for z in graph['nodes'] if z['node_type']=='theorem' and z['status']!='Definition'}
    submission=read('reduce-parent-verify-result.json')['id']
    sketches=[z for z in graph['nodes'] if z['node_type']=='sketch' and z['parent_theorem_id']==parent and z['submission_id']==submission]
    assert len(sketches)==1 and sketches[0]['status']=='SKETCH_ACCEPTED'
    actual={e['source'] for e in graph['edges'] if e['kind']=='sketch' and e['target']==sketches[0]['node_id'] and e['source'] in mathnodes}
    assert actual==set(ids.values()),('Actual parent dependencies differ',actual,set(ids.values()))
    for n in children:assert mathnodes[ids[pre+n]]['status']==('Proved' if n in closed else 'Open')
    assert mathnodes[parent]['status']=='Open' and mathnodes[ROOT]['status']=='Open'
    save('direct-graph-evidence.json',{'parent_id':parent,'submission_id':submission,'actual_child_ids':sorted(actual),'expected_child_ids':sorted(ids.values()),'two_proved_two_open':True,'parent_and_root_remain_open':True})
    leaves=[]
    while True:
        z=api.request('/theorems/'+ROOT+'/open-leaves?limit=50&offset='+str(len(leaves)));save('root-frontier-after-page-'+str(len(leaves))+'.json',z);leaves+=z['open_leaves']
        if len(leaves)>=z['total']:break
    assert len(leaves)==z['total'];save('root-frontier-after.json',{'open_leaves':leaves,'total':z['total'],'all_pages_fetched':True})
    print('Legendre four-child reduction accepted; two direct children Proved; two finite source ports remain Open.',flush=True)
if __name__=='__main__':
    if sys.argv[1]=='bind':bind()
    elif sys.argv[1]=='preflight':preflight()
    elif sys.argv[1]=='publish':publish()
