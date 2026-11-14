#!/usr/bin/env python3
"""Final numeric wrapper from two accepted small-source oracles. No compilation/API/Git."""
import argparse,json
from pathlib import Path
from generate_numeric import ROOTS,IMPORTS,ALLOWED_AXIOMS,check,sha,hashed,load,lines,rng,span,walk,apply,accept_ci,TASK

PREFIX='AbcAdaptation.Reference'
LIMIT=16*1024**3
REPO='https://github.com/lana-agents/iut'
COMMIT='07cb1da58f6d428a670dbb5dd6093d428bcbcdd8'

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    for a in ['root-only-report','graph','graph-receipt','source-build-plan','parser-acceptance','source-facts-acceptance','source-facts-ci-result','original-exprs','out']:
        ap.add_argument('--'+a,required=True)
    ap.add_argument('--oracle-receipt',action='append',required=True)
    ap.add_argument('--oracle-ci-result',action='append',required=True)
    args=ap.parse_args();out=Path(args.out).resolve();check(TASK in out.parents,'Output outside task /tmp directory')
    out.mkdir(parents=True,exist_ok=True)
    report={'status':'inputs-pending','generatedFiles':[],'nodes':[],'compilation':'not-run','api':'not-used'}
    try:
        for k,v in vars(args).items():
            if k=='out':continue
            for p in v if isinstance(v,list) else [v]:check(Path(p).is_file(),'Required compiler input missing: '+p)
        build_plan=load(args.source_build_plan);build_modules={m['module']:m for m in build_plan['input_modules']}
        check(build_plan['original_source_commit']==COMMIT,'Original repository commit differs from source build plan')
        rootsplit=load(args.root_only_report);split={n['name']:n for n in rootsplit['nodes']}
        check(set(split)==set(ROOTS) and rootsplit['status']=='root-only-draft-generated-needs-small-source-CI','Invalid root-only split report')
        rows={r['name']:r for r in lines(args.graph) if r.get('record')=='decl'};gr=load(args.graph_receipt)
        check(set(rows)==set(ROOTS) and gr['graphSha256']==sha(args.graph)==rootsplit['graphSha256'],'Original graph binding mismatch')
        pa=load(args.parser_acceptance)
        check(pa['status']=='accepted' and pa['noPanicOrErrorDiagnostics'] is True and sha(args.parser_acceptance)==rootsplit['parserAcceptanceSha256'] and pa['graphSha256']==sha(args.graph),'Original parser acceptance binding mismatch')
        parser_outputs={r['name']:r for r in pa['outputs']}
        fa=load(args.source_facts_acceptance)
        check(fa['status']=='accepted' and fa['noPanicOrErrorDiagnostics'] is True,'Original Expr export not accepted')
        fci=accept_ci(args.source_facts_ci_result,fa['job_id'],fa.get('compilerReceiptSha256',fa.get('receipt_sha256')))
        check(fci['resources']['peak_rss_bytes']<=LIMIT and fa['original_exprs_sha256']==sha(args.original_exprs),'Original Expr export memory/hash mismatch')
        original=load(args.original_exprs);exprs={r['name']:r for r in original['records']}
        check(original['compilerVersion']=='4.35.0-rc3' and set(exprs)==set(ROOTS),'Original compiler/Expr root mismatch')
        check(len(args.oracle_receipt)==len(args.oracle_ci_result)==2,'Need two independently accepted single-file oracles')
        modules={};ci_jobs=[]
        for rp,cp in zip(args.oracle_receipt,args.oracle_ci_result):
            receipt=load(rp)
            check(receipt['receiptValidation']=='source-output-sha256-and-terminal-summaries-v1' and receipt['complete'] and receipt['noPanicOrErrorDiagnostics'] is True,'Small-source receipt not accepted')
            ci=accept_ci(cp,receipt['compilerJobId'],receipt['compilerReceiptSha256'])
            check(ci['resources']['peak_rss_bytes']<=LIMIT,'Small-source oracle RSS exceeds 16 GiB')
            check(receipt['configSha256']==sha(receipt['configPath']) and load(receipt['configPath'])==receipt['config'],'Small oracle config changed')
            result,=receipt['results'];module=result['module'];check(module not in modules and module in ROOTS.values() and result['status']=='success','Duplicate/unknown/failed small module')
            for p,h in [('source','rawSha256'),('coordinateSource','normalizedSha256'),('output','outputSha256'),('diagnostics','diagnosticsSha256')]:check(sha(result[p])==result[h],'Small-source artifact changed: '+p)
            diag=load(result['diagnostics']);check(diag['hasErrors'] is False and diag['messages']==[],'Small-source diagnostics nonempty')
            modules[module]=(result,receipt,ci);ci_jobs.append({'jobId':ci['job_id'],'ciReceipt':str(Path(cp).resolve()),'ciReceiptSha256':sha(cp),'validatedReceipt':str(Path(rp).resolve()),'validatedReceiptSha256':sha(rp),'peakRssBytes':ci['resources']['peak_rss_bytes']})
        ledger=[];mapping=[];static=[];readbacks=[]
        for name,module in ROOTS.items():
            row=rows[name];spl=split[name];expr=exprs[name]
            check(row['module']==module and row['typeDeps']==row['valueDeps']==[] and not row['isPrivate'] and not row['hasSorryAx'] and set(row['axioms'])<=ALLOWED_AXIOMS,'Original root project dependencies/privacy/axioms changed')
            oldhash=spl['originalSourceNormalizedSha256'];check(gr['sourceFiles'][module]['normalizedSha256']==oldhash==expr['sourceSha256'],'Original whole-source identity mismatch')
            check(set(expr['axioms'])<=ALLOWED_AXIOMS,'Original Expr axiom mismatch')
            # The exported numeric Expr must contain no original project constant.
            def name_text(v):return '' if not v else (name_text(v[0])+'.' if v[0] else '')+str(v[2])
            def visit(v):
                if isinstance(v,dict):
                    if v.get('kind')in ['const','proj']:
                        n=name_text(v['name']);check(not n.startswith(('Iut.','Genl.')),'Numeric Expr mentions a project object')
                    for x in v.values():visit(x)
                elif isinstance(v,list):
                    for x in v:visit(x)
            visit(expr['elaboratedExpr'])
            pe=parser_outputs[name];check(sha(pe['path'])==pe['sha256'],'Original parser facts changed')
            pf=lines(pe['path']);olddecl,=[f for f in pf if f['kind']=='decl'];oldsource,=[f for f in pf if f['kind']=='source']
            olddata=Path(oldsource['coordinateSource']).read_bytes()
            check(hashed(olddata)==oldhash==pe['normalizedSha256'],'Original parser source changed')
            oldcommand=olddata[slice(*span(olddecl))]
            result,receipt,ci=modules[module];data=Path(result['coordinateSource']).read_bytes()
            check(hashed(data)==result['normalizedSha256']==spl['sourceSha256'],'Small source SHA does not match parser-first split')
            check(data==Path(result['source']).read_bytes().replace(b'\r\n',b'\n') and len(data)==result['byteLength'],'Small-source normalization mismatch')
            fs=lines(result['output']);source,=[f for f in fs if f['kind']=='source'];d,=[f for f in fs if f['kind']=='decl']
            check(source['module']==module and source['namePrefixes']==[] and source['offsetCoordinate']=='lean-normalized-utf8' and source['coordinateSource']==result['coordinateSource'],'Small-source scope mismatch')
            check(fs[-1]['kind']=='summary' and fs[-1]['status']=='success','Missing small-source terminal summary')
            for k,v in [('declarationCount','decl'),('referenceCount','ref')]:check(sum(f['kind']==v for f in fs)==result[k]==fs[-1][k],'Small-source count mismatch')
            check(d['nameText']==name.split('.')[-1] and d['valKind']=='simple' and d['privateTok'] is None and not d['generationIssue'],'Small-source target mismatch')
            command=data[slice(*span(d))];proof=data[d['valStart']['offset']:d['declEnd']['offset']]
            check(command==oldcommand and hashed(command)==spl['targetCommandSha256'] and hashed(proof)==spl['proofSha256'],'Original/small command or proof bytes differ')
            check(olddecl['name']==name and olddecl['declStart']==spl['originalCommandRange']['start'] and olddecl['declEnd']==spl['originalCommandRange']['end'],'Original command provenance mismatch')
            header=source['headerSyntax'];imports=[n for n in walk(header) if n['syntaxKind']=='Lean.Parser.Module.import']
            check([[n['identifier'] for n in walk(i) if 'identifier'in n] for i in imports]==[[n] for n in IMPORTS],'Expected exactly five precise Mathlib imports')
            commands=[f for f in fs if f['kind']=='command'];stack=[];target_scope=None;namespace_pairs=[]
            for c in commands:
                k=c['syntaxKind']
                check(c['isDeclaration'] or k in ['Lean.Parser.Command.namespace','Lean.Parser.Command.end','Lean.Parser.Command.universe','Lean.Parser.Command.set_option','Lean.Parser.Command.eoi'],'Unreviewed small-source context')
                if c['isDeclaration']:
                    check(rng(c['range'])==span(d),'Small source has another declaration');target_scope=list(stack)
                elif k=='Lean.Parser.Command.namespace':
                    ids=[n['identifier']for n in walk(c['contextSyntax'])if 'identifier'in n];check(ids==['Iut'],'Unexpected small namespace');stack.append('Iut');namespace_pairs.append(c)
                elif k=='Lean.Parser.Command.end':check(stack==['Iut'],'Unexpected small end');stack.pop();namespace_pairs.append(c)
                elif k=='Lean.Parser.Command.set_option':
                    tokens=[n.get('identifier',n.get('atom'))for n in walk(c['contextSyntax'])if 'identifier'in n or 'atom'in n]
                    check(tokens in [['set_option','relaxedAutoImplicit','false'],['set_option','maxSynthPendingDepth','3']],'Unreviewed semantic option')
            check(target_scope==['Iut'] and not stack and len(namespace_pairs)==2,'Small-source root scope mismatch')
            # Original parser keyword range transfers through a proven byte-equal
            # command. No keyword token search and no original whole-file offset
            # is applied to the small source directly.
            oldx,oldy=rng(olddecl['keywordRange']);start,end=span(d);oldstart=olddecl['declStart']['offset']
            x,y=start+oldx-oldstart,start+oldy-oldstart
            a,b=rng(d['nameRange'])
            for ref in [f for f in fs if f['kind']=='ref' and f['const'].startswith(('Iut.','Genl.'))]:
                check(ref['const']==name and (ref['start']['offset'],ref['end']['offset'])==(a,b),'Small-source InfoTree contains a project use dependency')
            check(start<=x<y<=a<b<=d['valStart']['offset']<end and data[x:y]==olddecl['keyword'].encode(),'Mapped parser keyword range invalid')
            check(data[b:d['valStart']['offset']]==olddata[olddecl['nameRange']['end']['offset']:olddecl['valStart']['offset']],'Original signature bytes changed')
            def target(newname,stub):
                changes=[(a-start,b-start,newname.encode()),(x-start,y-start,b'theorem')]
                if d['docstring']:
                    q,z=rng(d['docstring']);changes.append((q-start,z-start,b''))
                if stub:changes.append((d['valStart']['offset']-start,end-start,b':= by\n  sorry'))
                return apply(command,changes)
            # Keep imports/options/universes, original Iut namespace skeleton,
            # then close the upload wrapper before each top-level declaration.
            header_end=max(rng(i['range'])[1]for i in imports)
            preamble=apply(data,[(start,end,b''),(header_end,header_end,('\n\nnamespace '+PREFIX+'\n').encode())])+('\nend '+PREFIX+'\n').encode()
            full=PREFIX+'.'+name;slug=full.replace('.','_');formal=target(full,True);solution=preamble+target('solution',False)+b'\n'
            check(solution.endswith(proof+b'\n'),'Final solution proof bytes changed')
            payload={'theorem_name':full,'preamble':preamble.decode(),'formal_statement':formal.decode(),'solution':solution.decode()}
            for mod,text in [('Theorems.Thm_'+slug,preamble+formal+b'\n'),('Solutions.Sol_'+slug,solution)]:
                path=out/(mod.replace('.','/')+'.lean');path.parent.mkdir(parents=True,exist_ok=True);path.write_bytes(text)
                entry={'module':mod,'path':str(path),'sha256':sha(path),'bytes':len(text)};report['generatedFiles'].append(entry);readbacks.append(entry|{'text':text.decode()})
            pp=out/'payloads'/(slug+'.json');pp.parent.mkdir(exist_ok=True);pp.write_text(json.dumps(payload,ensure_ascii=False,indent=2)+'\n')
            # Invert the recorded semantic-option insertion before assigning
            # repository line numbers. Theorem110 also has a documented later
            # compatibility edit, so require exact inverse prefix through the
            # selected command rather than falsely equating whole copied files.
            build=build_modules[module];mirror=build['configuration_mirror']
            repo_data=Path(build['source']).read_bytes();copied_data=Path(build['workspace_source']).read_bytes()
            check(hashed(repo_data)==build['original_sha256'],'Repository original file hash differs from build plan')
            check(hashed(copied_data)==build['sha256']==oldhash and copied_data==olddata,'Compiled copied source differs from build plan/parser bytes')
            insertion=mirror['text'].encode();insertion_at=mirror['insertion_original_offset']
            check(b'\r\n' not in repo_data and b'\r\n' not in copied_data,'Source inverse mapping expects raw LF UTF8')
            check(copied_data[insertion_at:insertion_at+len(insertion)]==insertion,'Recorded semantic insertion bytes differ')
            old_start,old_end=span(olddecl)
            check(insertion_at+len(insertion)<=old_start,'Selected command crosses semantic insertion')
            repo_start,repo_end=old_start-len(insertion),old_end-len(insertion)
            inverse=copied_data[:insertion_at]+copied_data[insertion_at+len(insertion):]
            check(inverse[:repo_end]==repo_data[:repo_end] and repo_data[repo_start:repo_end]==oldcommand,'Repository command/prefix not recovered by exact inverse insertion')
            def source_position(offset):
                prefix=repo_data[:offset];tail=prefix.rsplit(b'\n',1)[-1]
                return {'line':prefix.count(b'\n')+1,'col':len(tail.decode()),'offset':offset}
            repo_range={'start':source_position(repo_start),'end':source_position(repo_end)}
            originalfile=row['sourceFile'];url=REPO+'/blob/'+COMMIT+'/'+originalfile+f"#L{repo_range['start']['line']}-L{repo_range['end']['line']}"
            repository_identity={'path':build['source'],'rawSha256':hashed(repo_data),'commandRange':repo_range,'sourceURL':url,
                'commandSha256':hashed(repo_data[repo_start:repo_end]),
                'copiedSourceInverseMapping':{'sourceBuildPlan':str(Path(args.source_build_plan).resolve()),'sourceBuildPlanSha256':sha(args.source_build_plan),
                    'insertionOriginalOffset':insertion_at,'insertedByteLength':len(insertion),'insertedLineCount':insertion.count(b'\n'),
                    'insertedTextSha256':hashed(insertion),'inversePrefixThroughTargetByteIdentical':True,'inverseWholeFileByteIdentical':inverse==repo_data,
                    'otherCopiedSourceCompatibilityFix':build.get('compatibility_fix')}}
            provenance={'repositoryOriginalSource':repository_identity,
                        'compilerCopiedWholeSource':{'path':spl['originalSource'],'normalizedSha256':oldhash,'commandRange':spl['originalCommandRange'],'graphRange':row['range']},
                        'smallSource':{'path':result['source'],'normalizedSha256':hashed(data),'module':module,'commandRange':{'start':d['declStart'],'end':d['declEnd']},'oracleJobId':ci['job_id']},
                        'commandSha256':hashed(command),'proofSha256':hashed(proof),'signatureSha256':hashed(data[b:d['valStart']['offset']]),
                        'keywordRangeMapping':{'original':olddecl['keywordRange'],'smallSource':{'startOffset':x,'endOffset':y},'basis':'Exact original/small command byte equality'}}
            node={'originalName':name,'theoremName':full,'payload':str(pp),'proofBytesIdentical':True,'dependencies':[],'provenance':provenance};report['nodes'].append(node)
            ledger.append({'producer':full,'source':url,'originalConsumer':'Iut.Theorem110Invariants.theorem110'if name=='Iut.assembly'else'Iut.Corollary22Inputs.c2','existingCanonicalConsumerConnected':False,
                           'scope':'Conditional inequality between real-number parameters; no arithmetic-geometric object construction.',
                           'fidelity':'Original signature and proof bytes preserved. Original/small source coordinates separately bound by exact command and proof hashes. Keyword and binding edits use parser/oracle ranges only.',
                           'provenance':provenance,'originalAxioms':expr['axioms'],'wrappedAxioms':'pending main CI'})
            mapping.append({'originalName':name,'wrappedName':full,'solutionName':'solution','originalExpr':expr,'sourceURL':url,'provenance':provenance,'wrappedExpr':None,'status':'original actual Expr bound; wrapped actual Expr comparison pending main CI','formalStatement':formal.decode()})
            static.append({'name':name,'originalSmallCommandExact':True,'originalFinalProofExact':True,'originalFinalSignatureExact':True,'payloadMatchesLeanFiles':True,'selfTargetImported':False,'MathlibImports':IMPORTS,'provenance':provenance})
        report.update(status='generated-final-draft-main-platform-CI-pending',definitionsBundleCount=0,oracleJobs=ci_jobs,originalExprJobId=fci['job_id'],
                      acceptance={'platformExactTextCompilation':False,'originalExprKernelComparison':False,'solutionAxiomAudit':False})
        for filename,value in [('SOURCE_LEDGER.json',{'status':report['status'],'sourceRepository':REPO,'sourceCommit':COMMIT,'entries':ledger}),('original-wrapped-expr-name-map.json',{'status':'wrapped-Expr-pending-main-CI','nodes':mapping}),('static-identity-report.json',{'status':'passed-static-identity','checks':static}),('full-generated-readbacks.json',{'files':readbacks})]:
            (out/filename).write_text(json.dumps(value,ensure_ascii=False,indent=2)+'\n')
        md=['# Numeric source ledger','','These two nodes are conditional real-number inequalities. They do not implement arithmetic-geometric objects.','','| Producer | Original source | Original consumer |','|---|---|---|']
        md.extend('| `'+r['producer']+'` | [source]('+r['source']+') | `'+r['originalConsumer']+'` |'for r in ledger)
        md+=['','Original statement signatures and proofs are byte-identical. Platform compilation, actual Expr comparison, solution axiom audit, and existing canonical consumer integration remain pending.']
        (out/'SOURCE_LEDGER.md').write_text('\n'.join(md)+'\n')
    except (ValueError,KeyError,FileNotFoundError) as e:
        report['error']=str(e);report['status']='inputs-pending'if'missing:'in str(e)else'refused-unbound-or-unsupported-input'
    (out/'final-generation-report.json').write_text(json.dumps(report,ensure_ascii=False,indent=2)+'\n')
    print(json.dumps({'status':report['status'],'error':report.get('error'),'generatedFiles':report['generatedFiles']},ensure_ascii=False,indent=2))
    return 0 if report['status'].startswith('generated-final')else 2
if __name__=='__main__':raise SystemExit(main())
