#!/usr/bin/env python3
"""Generate two numeric-only nodes from accepted compiler ranges; no Lean/API/Git calls."""
import argparse
import hashlib
import json
from pathlib import Path

TASK=Path('/tmp/p2m-numeric-assembly-mechanical-adapter-20261115')
PREFIX='AbcAdaptation.Reference'
ROOTS={'Iut.assembly':'Iut.Implication.Theorem110','Iut.c2_final':'Iut.Implication.Corollary22'}
IMPORTS=['Mathlib.Data.Real.Basic','Mathlib.Tactic.Linarith','Mathlib.Tactic.NormNum',
         'Mathlib.Tactic.Positivity','Mathlib.Tactic.Ring']
ALLOWED_AXIOMS={'propext','Classical.choice','Quot.sound'}

def check(c,m):
    if not c:raise ValueError(m)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def hashed(data):return hashlib.sha256(data).hexdigest()
def load(p):return json.loads(Path(p).read_text())
def lines(p):return [json.loads(l) for l in Path(p).read_text().splitlines() if l.strip()]
def rng(r):return r['start']['offset'],r['end']['offset']
def span(d):return d['declStart']['offset'],d['declEnd']['offset']
def walk(stx):
    if isinstance(stx,dict):
        yield stx
        for c in stx.get('children',[]):yield from walk(c)
def apply(data,changes):
    previous=0
    for a,b,replacement in sorted(changes):
        check(previous<=a<=b<=len(data),'Overlapping/outside compiler edits')
        previous=b
    for a,b,replacement in sorted(changes,reverse=True):data=data[:a]+replacement+data[b:]
    return data

def accept_ci(path,expected_job=None,expected_sha=None):
    if expected_sha:check(sha(path)==expected_sha,'Full CI receipt hash mismatch')
    ci=load(path);r=ci['result']
    check(ci['status']=='succeeded' and r['exit_code']==0,'CI not terminal success')
    if expected_job:check(ci['job_id']==expected_job,'CI job identity mismatch')
    check(all(d.get('severity') == 'warning' for d in r.get('diagnostics',[])), 'Outer compiler error/unknown diagnostics')
    text=(r.get('stdout','')+'\n'+r.get('stderr','')).casefold()
    check('panic' not in text and 'error:' not in text,'Outer compiler panic/error')
    check(r['snapshot']['workspace_mode']=='exclusive_worktree' and r['snapshot']['snapshot_id'] is None,'CI mode mismatch')
    return ci

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    for arg in ['graph','graph-receipt','graph-ci-result','oracle-receipt','oracle-ci-result',
                'source-facts-acceptance','source-facts-ci-result','keywords','original-exprs','out']:
        ap.add_argument('--'+arg,required=True)
    args=ap.parse_args()
    out=Path(args.out).resolve()
    check(TASK in out.parents,'Output must stay below assigned /tmp task directory')
    out.mkdir(parents=True,exist_ok=True)
    report={'status':'inputs-pending','compilation':'not-run','api':'not-used','generatedFiles':[],
            'scope':'Two conditional real-number inequalities, with no arithmetic-geometry object implementation',
            'platform':{'lean':'4.33.1','mathlib':'0df444a'}}
    try:
        for name,value in vars(args).items():
            if name!='out':check(Path(value).is_file(),'Required compiler input missing: '+value)
        graph=lines(args.graph);rows={r['name']:r for r in graph if r.get('record')=='decl'}
        gr=load(args.graph_receipt)
        check(gr['graphSha256']==sha(args.graph),'Graph identity mismatch')
        gci=accept_ci(args.graph_ci_result,gr['compilerJobId'],gr['compilerReceiptSha256'])
        receipt=load(args.oracle_receipt)
        check(receipt['receiptValidation']=='source-output-sha256-and-terminal-summaries-v1' and receipt['complete'] and receipt['noPanicOrErrorDiagnostics'] is True,'Oracle receipt not accepted')
        oci=accept_ci(args.oracle_ci_result,receipt['compilerJobId'],receipt['compilerReceiptSha256'])
        check(sha(receipt['configPath'])==receipt['configSha256'] and load(receipt['configPath'])==receipt['config'],'Oracle config changed')
        accepted=load(args.source_facts_acceptance)
        check(accepted['status']=='accepted' and accepted['noPanicOrErrorDiagnostics'] is True,'Narrow facts not accepted')
        fci=accept_ci(args.source_facts_ci_result,accepted['job_id'],accepted['receipt_sha256'])
        check(accepted['keywords_sha256']==sha(args.keywords) and accepted['original_exprs_sha256']==sha(args.original_exprs),'Narrow artifact hash mismatch')
        keywords=lines(args.keywords)
        originals=load(args.original_exprs)
        check(originals['compilerVersion']=='4.35.0-rc3','Unexpected source Expr compiler')
        records={r['name']:r for r in originals['records']}
        check(set(records)==set(ROOTS),'Original Expr root set mismatch')
        results={r['module']:r for r in receipt['results']}
        check(set(results)==set(ROOTS.values()),'Oracle module set mismatch')
        ledger=[];mapping=[];nodes=[]
        for name,module in ROOTS.items():
            row=rows[name]
            check(row['module']==module and row['kind']=='theorem' and not row['typeDeps'] and not row['valueDeps'],'Numeric root has project dependencies')
            check(not row['isPrivate'] and not row['hasSorryAx'] and set(row['axioms'])<=ALLOWED_AXIOMS,'Invalid original declaration privacy/axioms')
            result=results[module]
            check(result['status']=='success','Oracle module failed')
            for p,h in [('source','rawSha256'),('coordinateSource','normalizedSha256'),('output','outputSha256'),('diagnostics','diagnosticsSha256')]:
                check(sha(result[p])==result[h],'Oracle artifact hash mismatch: '+p)
            check(gr['sourceFiles'][module]=={k:result[k] for k in ['rawSha256','normalizedSha256']},'Graph/oracle source identities unbound')
            diagnostic=load(result['diagnostics'])
            check(diagnostic['hasErrors'] is False and diagnostic['messages']==[],'Source diagnostics nonempty')
            facts=lines(result['output']);source,=[f for f in facts if f['kind']=='source']
            check(source['module']==module and source['namePrefixes']==[] and source['offsetCoordinate']=='lean-normalized-utf8' and source['coordinateSource']==result['coordinateSource'],'Oracle source scope mismatch')
            check(facts[-1]['kind']=='summary' and facts[-1]['status']=='success','Missing terminal source summary')
            for k,v in [('declarationCount','decl'),('referenceCount','ref')]:
                check(sum(f['kind']==v for f in facts)==result[k]==facts[-1][k],'Fact count mismatch')
            data=Path(result['coordinateSource']).read_bytes()
            check(len(data)==result['byteLength']==source['byteLength'],'Source byte length mismatch')
            check(data==Path(result['source']).read_bytes().replace(b'\r\n',b'\n'),'Source normalization mismatch')
            ks,=[r for r in keywords if r['kind']=='source' and r['name']==name]
            kw,=[r for r in keywords if r['kind']=='keyword' and r['name']==name]
            check(ks['module']==module and ks['normalizedSha256']==result['normalizedSha256']==sha(ks['coordinateSource']),'Keyword source mismatch')
            expr=records[name]
            check(expr['module']==module and expr['sourceSha256']==result['normalizedSha256'] and set(expr['axioms'])<=ALLOWED_AXIOMS,'Original Expr/source mismatch')
            # Reject any source project constant inside the actual compiler type.
            def decode_name(v):
                if not v:return ''
                return (decode_name(v[0])+'.' if v[0] else '')+str(v[2])
            def reject_project_constants(v):
                if isinstance(v,dict):
                    if v.get('kind') in ['const','proj']:
                        n=decode_name(v['name']);check(not (n=='Iut' or n.startswith('Iut.') or n.startswith('Genl.')),'Original numeric type references project object')
                    for child in v.values():reject_project_constants(child)
                elif isinstance(v,list):
                    for child in v:reject_project_constants(child)
            reject_project_constants(expr['elaboratedExpr'])
            decls=[f for f in facts if f['kind']=='decl'];commands=[f for f in facts if f['kind']=='command']
            p=(row.get('selectionRange') or row['range'])['start']
            d,=[f for f in decls if (f['declStart']['line'],f['declStart']['col'])<=(p['line'],p['col'])<(f['declEnd']['line'],f['declEnd']['col'])]
            check(not d['generationIssue'] and d['nameText']==name.split('.')[-1] and d['privateTok'] is None and d['valKind']=='simple','Unsupported target command')
            # Full compiler source ranges, not token searches, delete every other
            # command. Only target-ancestor namespace/end and original universe
            # declarations are retained; no variable/open/option effects survive
            # unless explicitly admitted below. Unrelated project variable/open
            # commands are recorded as removed, not silently imported.
            stack=[];kept_context=[];removed=[];target_context=None
            for c in commands:
                kind=c['syntaxKind'];r=c.get('range')
                if kind=='Lean.Parser.Command.eoi':continue
                check(r is not None,'Command missing source range')
                if c['isDeclaration']:
                    if rng(r)==span(d):target_context=list(stack)
                    continue
                if kind=='Lean.Parser.Command.namespace':
                    ids=[s['identifier'] for s in walk(c['contextSyntax']) if 'identifier' in s]
                    check(len(ids)==1,'Unsupported namespace form')
                    stack.append((ids[0],c))
                elif kind=='Lean.Parser.Command.end':
                    check(stack,'Unexpected end context')
                    current,opening=stack.pop()
                    ids=[s['identifier'] for s in walk(c['contextSyntax']) if 'identifier' in s]
                    check(ids in [[],[current]],'Namespace/section mismatch')
                    if target_context and any(o is opening for _,o in target_context):kept_context.extend([opening,c])
                elif kind=='Lean.Parser.Command.section':
                    raise ValueError('Section context unsupported; preserve needed variables explicitly after review')
            check(target_context is not None and [n for n,_ in target_context]==['Iut'],'Unexpected numeric target namespace')
            for c in commands:
                if not c['isDeclaration'] and c['syntaxKind']=='Lean.Parser.Command.universe':
                    kept_context.append(c)
            # Only the semantic source options present in both compiled copies
            # are retained. Exact AST command spans supply their bytes.
            for c in commands:
                if not c['isDeclaration'] and c['syntaxKind']=='Lean.Parser.Command.set_option':
                    atoms=[s.get('identifier',s.get('atom')) for s in walk(c['contextSyntax']) if 'identifier' in s or 'atom' in s]
                    if atoms in [['set_option','relaxedAutoImplicit','false'],['set_option','maxSynthPendingDepth','3']]:kept_context.append(c)
                    else:raise ValueError('Unreviewed source option context')
            keep_ranges={rng(c['range']) for c in kept_context}
            for c in commands:
                if c['isDeclaration'] or c['syntaxKind']=='Lean.Parser.Command.eoi' or rng(c['range']) in keep_ranges:continue
                removed.append({'syntaxKind':c['syntaxKind'],'range':c['range'],'reason':'Unused source context for isolated numeric target; no project type/value dependencies; exact original Expr must match after transplant'})
            header=source['headerSyntax']['range'];ha,hb=rng(header)
            headertext=''.join('import '+i+'\n' for i in IMPORTS).encode()+b'\nnamespace AbcAdaptation.Reference\n'
            changes=[(ha,hb,headertext)]
            changes.extend((a,b,b'') for a,b in map(span,decls))
            changes.extend((*rng(c['range']),b'') for c in commands if not c['isDeclaration'] and c['syntaxKind']!='Lean.Parser.Command.eoi' and rng(c['range']) not in keep_ranges)
            skeleton=apply(data,changes)+b'\nend AbcAdaptation.Reference\n'
            a,b=rng(d['nameRange']);x,y=rng(kw['keywordRange']);start,end=span(d)
            check(start<=x<y<=a<b<=d['valStart']['offset']<end and data[x:y]==kw['keyword'].encode() and kw['keyword'] in ['lemma','theorem'],'Invalid parser keyword/binding boundary')
            def target(newname,stub):
                modifications=[(a-start,b-start,newname.encode()),(x-start,y-start,b'theorem')]
                if d['docstring']:
                    q,z=rng(d['docstring']);modifications.append((q-start,z-start,b''))
                if stub:modifications.append((d['valStart']['offset']-start,end-start,b':= by\n  sorry'))
                return apply(data[start:end],modifications)
            full=PREFIX+'.'+name;slug=full.replace('.','_')
            formal=target(full,True);preamble=skeleton
            # No namespace opens are needed: the signature is self-contained and
            # the actual compiler type contains no project constants.
            sol=skeleton+target('solution',False)+b'\n'
            for mod,text in [('Theorems.Thm_'+slug,preamble+formal+b'\n'),('Solutions.Sol_'+slug,sol)]:
                path=out/(mod.replace('.','/')+'.lean');path.parent.mkdir(parents=True,exist_ok=True);path.write_bytes(text)
                report['generatedFiles'].append({'module':mod,'path':str(path),'sha256':sha(path),'bytes':len(text)})
            payload={'theorem_name':full,'preamble':preamble.decode(),'formal_statement':formal.decode(),'solution':sol.decode()}
            path=out/'payloads'/(slug+'.json');path.parent.mkdir(exist_ok=True);path.write_text(json.dumps(payload,ensure_ascii=False,indent=2)+'\n')
            proof=data[d['valStart']['offset']:end];signature=data[b:d['valStart']['offset']]
            check(sol.endswith(proof+b'\n'),'Proof bytes changed')
            nodes.append({'originalName':name,'theoremName':full,'proofLines':d['declEnd']['line']-d['valStart']['line'],
                          'proofSha256':hashed(proof),'signatureSha256':hashed(signature),'proofBytesIdentical':True,
                          'commandRange':list(span(d)),'sourceModule':module,'sourceNormalizedSha256':result['normalizedSha256'],
                          'removedContextCommands':removed,'retainedContextCommands':[{'syntaxKind':c['syntaxKind'],'range':c['range']} for c in kept_context],
                          'payload':str(path),'dependencies':[]})
            mapping.append({'originalName':name,'wrappedName':full,'solutionName':'solution','originalExpr':expr,
                            'wrappedElaboratedExpr':None,'exactGeneratedFormalStatement':formal.decode(),
                            'typeValidation':'pending main-agent Lean 4.33.1 Expr comparison; no project constant relocation'})
            ledger.append({'producer':full,'sourceModule':module,'originalName':name,
                           'sourceCommandRange':{'start':d['declStart'],'end':d['declEnd']},'sourceNormalizedSha256':result['normalizedSha256'],
                           'fidelity':'Original signature and proof bytes preserved; lemma keyword and theorem binding changed only at parser ranges; unrelated context removed at AST command ranges.',
                           'mathematicalScope':'Conditional inequality between real-number parameters. No construction of arithmetic-geometric objects is supplied.',
                           'originalConsumer':'Iut.Theorem110Invariants.theorem110' if name=='Iut.assembly' else 'Iut.Corollary22Inputs.c2',
                           'existingCanonicalConsumerConnected':False})
        report.update(status='generated-draft-main-CI-pending',nodes=nodes,definitionsBundleCount=0,
                      compilerJobs={'graph':gci['job_id'],'oracle':oci['job_id'],'narrowFacts':fci['job_id']},
                      acceptance={'exactTextCompilation':False,'originalExprComparison':False,'wrappedAxiomAudit':False})
        (out/'SOURCE_LEDGER.json').write_text(json.dumps({'status':'draft-main-CI-pending','entries':ledger},ensure_ascii=False,indent=2)+'\n')
        (out/'original-wrapped-expr-name-map.json').write_text(json.dumps({'status':'original-Expr-bound-generated-Expr-pending','nodes':mapping},ensure_ascii=False,indent=2)+'\n')
    except (ValueError,KeyError,FileNotFoundError) as e:
        report['error']=str(e);report['status']='inputs-pending' if 'missing:' in str(e) else 'refused-unbound-or-unsupported-input'
    (out/'dry-run-report.json').write_text(json.dumps(report,ensure_ascii=False,indent=2)+'\n')
    print(json.dumps(report,ensure_ascii=False,indent=2))
    return 0 if report['status'].startswith('generated-') else 2

if __name__=='__main__':raise SystemExit(main())
