#!/usr/bin/env python3
"""Parser-first numeric split. No compilation, regex, API, or Git operations."""
import argparse,json,hashlib
from pathlib import Path
from generate_numeric import ROOTS,IMPORTS,ALLOWED_AXIOMS,check,sha,hashed,load,lines,rng,span,walk,apply,accept_ci,TASK

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    for a in ['parser-acceptance','parser-ci-result','graph','source-facts-acceptance','source-facts-ci-result','original-exprs','out']:ap.add_argument('--'+a,required=True)
    args=ap.parse_args();out=Path(args.out).resolve()
    check(TASK in out.parents,'Output must be below assigned task /tmp directory')
    out.mkdir(parents=True,exist_ok=True)
    report={'status':'inputs-pending','mode':'parser-first-root-only-source','compilation':'not-run','nodes':[]}
    try:
        for k,v in vars(args).items():
            if k!='out':check(Path(v).is_file(),'Required compiler input missing: '+v)
        acceptance=load(args.parser_acceptance)
        check(acceptance['status']=='accepted' and acceptance['noPanicOrErrorDiagnostics'] is True,'Parser job not accepted')
        pci=accept_ci(args.parser_ci_result,acceptance['job_id'],acceptance['compilerReceiptSha256'])
        limit=16*1024**3
        check(pci['resources']['peak_rss_bytes']<=limit,'Parser job exceeds 16 GiB RSS')
        check(acceptance['graphSha256']==sha(args.graph),'Parser acceptance graph mismatch')
        rows={r['name']:r for r in lines(args.graph) if r.get('record')=='decl'}
        faccept=load(args.source_facts_acceptance)
        check(faccept['status']=='accepted' and faccept['noPanicOrErrorDiagnostics'] is True,'Original Expr export not accepted')
        fci=accept_ci(args.source_facts_ci_result,faccept['job_id'],faccept.get('compilerReceiptSha256',faccept.get('receipt_sha256')))
        check(fci['resources']['peak_rss_bytes']<=limit,'Original Expr job exceeds 16 GiB RSS')
        check(faccept['original_exprs_sha256']==sha(args.original_exprs),'Original Expr export hash mismatch')
        exprs={r['name']:r for r in load(args.original_exprs)['records']}
        entries={r['name']:r for r in acceptance['outputs']}
        check(set(entries)==set(ROOTS) and set(exprs)==set(ROOTS),'Unexpected parser/Expr root set')
        for name,module in ROOTS.items():
            row=rows[name];entry=entries[name]
            check(row['module']==module and row['typeDeps']==[] and row['valueDeps']==[] and not row['hasSorryAx'] and set(row['axioms'])<=ALLOWED_AXIOMS,'Root has nonnumeric project dependencies/axioms')
            check(entry['sha256']==sha(entry['path']),'Parser fact artifact changed')
            facts=lines(entry['path']);source,=[f for f in facts if f['kind']=='source'];d,=[f for f in facts if f['kind']=='decl']
            check(source['module']==module and source['name']==name and source['offsetCoordinate']=='lean-normalized-utf8','Parser source identity mismatch')
            data=Path(source['coordinateSource']).read_bytes()
            check(hashed(data)==source['normalizedSha256Expected']==entry['normalizedSha256']==exprs[name]['sourceSha256'],'Parser/original Expr source hash mismatch')
            check(data==Path(source['source']).read_bytes().replace(b'\r\n',b'\n') and len(data)==source['byteLength'],'Parser normalized bytes mismatch')
            check(facts[-1]['kind']=='summary' and facts[-1]['status']=='success' and facts[-1]['mode']=='parser-only-no-reelaboration','Missing parser terminal summary')
            check(d['name']==name and not d['generationIssue'] and d['privateTok'] is None and d['valKind']=='simple','Unsupported numeric target')
            p=(row.get('selectionRange') or row['range'])['start']
            check((d['nameRange']['start']['line'],d['nameRange']['start']['col'])==(p['line'],p['col']),'Compiler binding/parser identity mismatch')
            a,b=rng(d['nameRange']);x,y=rng(d['keywordRange']);start,end=span(d)
            check(start<=x<y<=a<b<=d['valStart']['offset']<end and data[x:y]==d['keyword'].encode(),'Parser keyword/proof bounds mismatch')
            commands=[f for f in facts if f['kind']=='command' and f['syntaxKind']!='Lean.Parser.Command.eoi']
            stack=[];target_stack=None;keep=[]
            for c in commands:
                check(c['range'] is not None,'Missing command range')
                k=c['syntaxKind']
                if c['isDeclaration']:
                    if rng(c['range'])==(start,end):target_stack=list(stack)
                elif k=='Lean.Parser.Command.namespace':
                    ids=[n['identifier'] for n in walk(c['contextSyntax']) if 'identifier'in n]
                    check(len(ids)==1,'Unsupported namespace form');stack.append((ids[0],c))
                elif k=='Lean.Parser.Command.end':
                    check(stack,'Unmatched context end');n,opening=stack.pop()
                    ids=[n['identifier'] for n in walk(c['contextSyntax']) if 'identifier'in n]
                    check(ids in [[],[n]],'Unsupported named end')
                    if target_stack and any(opening is op for _,op in target_stack):keep.extend([opening,c])
                elif k=='Lean.Parser.Command.section':raise ValueError('Unreviewed section context')
                elif k=='Lean.Parser.Command.universe':keep.append(c)
                elif k=='Lean.Parser.Command.set_option':
                    tokens=[n.get('identifier',n.get('atom')) for n in walk(c['contextSyntax']) if 'identifier'in n or 'atom'in n]
                    check(tokens in [['set_option','relaxedAutoImplicit','false'],['set_option','maxSynthPendingDepth','3']],'Unreviewed option AST')
                    keep.append(c)
            check(target_stack and [n for n,_ in target_stack]==['Iut'],'Target scope is not original Iut namespace')
            keep_ranges={rng(c['range']) for c in keep}
            removed=[c for c in commands if rng(c['range'])!=(start,end) and rng(c['range']) not in keep_ranges]
            ha,hb=rng(source['headerSyntax']['range'])
            import_text=''.join('import '+m+'\n' for m in IMPORTS).encode()
            changes=[(ha,hb,import_text)]+[(*rng(c['range']),b'') for c in removed]
            result=apply(data,changes)
            command=data[start:end];proof=data[d['valStart']['offset']:end]
            check(command in result and proof in result,'Root-only source altered target command/proof bytes')
            slug=name.replace('.','_');path=out/'RootOnly'/('Numeric_'+slug+'.lean');path.parent.mkdir(exist_ok=True);path.write_bytes(result)
            node={'name':name,'originalModule':module,'generatedModule':'RootOnly.Numeric_'+slug,
                  'source':str(path),'sourceSha256':sha(path),'originalSource':source['source'],
                  'originalSourceNormalizedSha256':hashed(data),'originalCommandRange':{'start':d['declStart'],'end':d['declEnd']},
                  'targetCommandSha256':hashed(command),'proofSha256':hashed(proof),'targetCommandBytesIdentical':True,
                  'removedCommands':[{'syntaxKind':c['syntaxKind'],'range':c['range'],'reason':'Other declaration or unused context; selected target has no project type/value dependency and retained original Expr will be kernel-compared'} for c in removed],
                  'retainedContext':[{'syntaxKind':c['syntaxKind'],'range':c['range']} for c in keep],
                  'originalExprExport':{'path':str(Path(args.original_exprs).resolve()),'sha256':sha(args.original_exprs),'recordName':name},'mathematicalScope':'Conditional inequality between real-number parameters',
                  'formalAcceptance':{'smallSourceInfoTree':False,'originalExprKernelComparison':False,'platformExactText':False}}
            report['nodes'].append(node)
        report.update(status='root-only-draft-generated-needs-small-source-CI',parserJobId=pci['job_id'],originalExprJobId=fci['job_id'],
                      parserAcceptanceSha256=sha(args.parser_acceptance),graphSha256=sha(args.graph),
                      nextStep='Main agent compiles each root-only source with Lean4.35 InfoTree oracle under 16GiB, then generates platform wrapper from those small-source facts and kernel-compares original Expr.')
    except (ValueError,KeyError,FileNotFoundError) as e:
        report['error']=str(e);report['status']='inputs-pending' if 'missing:' in str(e) else 'refused-unbound-or-unsupported-input'
    (out/'root-only-report.json').write_text(json.dumps(report,ensure_ascii=False,indent=2)+'\n')
    print(json.dumps({'status':report['status'],'error':report.get('error'),'nodes':[{k:n[k] for k in ['name','source','sourceSha256','targetCommandSha256','proofSha256','targetCommandBytesIdentical']} for n in report['nodes']]},ensure_ascii=False,indent=2));return 0 if report['status'].startswith('root-only-draft') else 2
if __name__=='__main__':raise SystemExit(main())
