#!/usr/bin/env python3
"""Generate a single-module PrimeSelection transplant from bound compiler facts.
No Lean compilation, API access, source mutation, or source regex parsing.
"""
import argparse
import hashlib
import json
from pathlib import Path

MODULE = 'Iut.Implication.PrimeSelection'
PREFIX = 'AbcAdaptation.Reference'
REVIEWED_NORMALIZED_SHA256 = 'c9d997817cd3e8d75405195ebec76c77692b4473036615c5a9f0d40f40171580'
ROOTS = {'Iut.ChebyshevBound.exists_prime_notMem',
         'Iut.LocalHeightData.exists_prime_selection', 'Iut.sum_log_primeFactors_le'}
MATHLIB = ['Mathlib.NumberTheory.Chebyshev',
           'Mathlib.Analysis.SpecialFunctions.Sqrt',
           'Mathlib.Analysis.Complex.ExponentialBounds']
DEF_MODULE = 'Definitions.Def_AbcAdaptation_Reference_Iut_Implication_PrimeSelection'
ALLOWED_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}


def check(cond, message):
    if not cond:
        raise ValueError(message)


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def load_lines(path):
    return [json.loads(line) for line in Path(path).read_text().splitlines() if line.strip()]


def walk(syntax):
    if isinstance(syntax, dict):
        yield syntax
        for child in syntax.get('children', []):
            yield from walk(child)


def span(fact):
    return fact['declStart']['offset'], fact['declEnd']['offset']


def rng(fact):
    return fact['start']['offset'], fact['end']['offset']


def edits(data, changes):
    ordered = sorted(changes)
    previous = 0
    for start, end, replacement in ordered:
        check(previous <= start <= end <= len(data), 'Overlapping or invalid compiler edits')
        previous = end
    for start, end, replacement in reversed(ordered):
        data = data[:start] + replacement + data[end:]
    return data


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--graph', required=True)
    ap.add_argument('--graph-receipt', required=True)
    ap.add_argument('--stage2-receipt', required=True)
    ap.add_argument('--stage2-ci-result', required=True)
    ap.add_argument('--keyword-facts', required=True)
    ap.add_argument('--out', required=True)
    args = ap.parse_args()
    out = Path(args.out).resolve()
    check(str(out).startswith('/tmp/p2m-prime-selection-mechanical-adapter-20261115/'),
          'This draft generator writes only beneath its assigned /tmp task directory')
    out.mkdir(parents=True, exist_ok=True)
    report = {'status': 'inputs-pending', 'compilation': 'not-run', 'api': 'not-used',
              'platform': {'lean': '4.33.1', 'mathlib': '0df444a'},
              'sourceCompiler': '4.35.0-rc3', 'generatedFiles': []}
    try:
        for p in [args.graph, args.graph_receipt, args.stage2_receipt, args.stage2_ci_result, args.keyword_facts]:
            check(Path(p).is_file(), 'Required bound compiler input missing: ' + p)
        graph = load_lines(args.graph)
        manifest, = [r for r in graph if r.get('record') == 'manifest']
        check(set(manifest['roots']) == ROOTS and manifest['participatingModules'] == [MODULE],
              'Unexpected graph roots/module set')
        rows = {r['name']: r for r in graph if r.get('record') == 'decl'}
        check(len(rows) == sum(r.get('record') == 'decl' for r in graph), 'Duplicate graph constants')
        gr = json.loads(Path(args.graph_receipt).read_text())
        check(gr.get('graphSha256') == sha(args.graph), 'Graph receipt hash mismatch')
        sr = json.loads(Path(args.stage2_receipt).read_text())
        check(sr.get('receiptValidation') == 'source-output-sha256-and-terminal-summaries-v1'
              and sr.get('complete') and sr.get('noPanicOrErrorDiagnostics') is True,
              'Stage2 requires a validated successful receipt')
        check(sr.get('compilerReceiptSha256') == sha(args.stage2_ci_result), 'Stage2 complete CI receipt hash mismatch')
        ci = json.loads(Path(args.stage2_ci_result).read_text())
        check(ci.get('status') == 'succeeded' and ci.get('job_id') == sr.get('compilerJobId'), 'Stage2 CI identity/terminal state mismatch')
        ci_result = ci['result']
        check(ci_result.get('exit_code') == 0 and ci_result.get('diagnostics') == [], 'Stage2 outer compiler diagnostics/exit failure')
        outer_logs = (ci_result.get('stdout','')+'\n'+ci_result.get('stderr','')).casefold()
        check('panic' not in outer_logs and 'error:' not in outer_logs, 'Stage2 outer compiler panic/error')
        check(ci_result['snapshot']['workspace_mode'] == 'exclusive_worktree' and ci_result['snapshot']['snapshot_id'] is None,
              'Stage2 CI mode differs from approved exclusive workflow')
        check(sr.get('configSha256') == sha(sr['configPath']) and
              json.loads(Path(sr['configPath']).read_text()) == sr['config'], 'Stage2 config changed')
        result, = sr['results']
        check(result['module'] == MODULE and result['status'] == 'success', 'Unexpected Stage2 result')
        for path_key, hash_key in [('output', 'outputSha256'), ('source', 'rawSha256'),
                                   ('coordinateSource', 'normalizedSha256'), ('diagnostics', 'diagnosticsSha256')]:
            check(sha(result[path_key]) == result[hash_key], 'Stage2 artifact changed: ' + path_key)
        diagnostics = json.loads(Path(result['diagnostics']).read_text())
        check(diagnostics.get('hasErrors') is False and diagnostics.get('messages') == [], 'Stage2 diagnostics must be empty for this reviewed source')
        check(result['normalizedSha256'] == REVIEWED_NORMALIZED_SHA256, 'Source version differs from reviewed single-module adapter')
        check(gr.get('sourceFiles', {}).get(MODULE) ==
              {k: result[k] for k in ['rawSha256', 'normalizedSha256']},
              'Graph and Stage2 source identities are not bound')
        facts = load_lines(result['output'])
        source, = [f for f in facts if f['kind'] == 'source']
        check(source['module'] == MODULE and source.get('namePrefixes') == [] and
              source['offsetCoordinate'] == 'lean-normalized-utf8' and source['coordinateSource'] == result['coordinateSource'] and source['source'] == result['source'], 'Unsupported Stage2 scope/coordinates/source')
        check(facts[-1]['kind'] == 'summary' and facts[-1]['status'] == 'success', 'Missing terminal summary')
        for key, kind in [('declarationCount','decl'), ('referenceCount','ref')]:
            check(sum(f['kind'] == kind for f in facts) == result[key] == facts[-1][key],
                  'Stage2 fact count mismatch')
        data = Path(result['coordinateSource']).read_bytes()
        check(len(data) == result['byteLength'] == source['byteLength'], 'Normalized byte length mismatch')
        declarations = [f for f in facts if f['kind'] == 'decl']
        commands = [f for f in facts if f['kind'] == 'command']
        refs = [f for f in facts if f['kind'] == 'ref']
        check(all(not f.get('generationIssue') for f in declarations + commands), 'Unsupported oracle command')
        # The full syntax tree, not source text, supplies import identities/ranges.
        imports = [n for n in walk(source['headerSyntax']) if n['syntaxKind'] == 'Lean.Parser.Module.import']
        import_names = [[n['identifier'] for n in walk(i) if 'identifier' in n] for i in imports]
        check(import_names == [[n] for n in MATHLIB], 'Mathlib import set/order differs from reviewed source')
        header_end = max(rng(i['range'])[1] for i in imports)
        # Admit only reviewed structural contexts. In particular no attributes,
        # notation, macros, scoped opens, exports, includes, sections or options.
        allowed = {'Lean.Parser.Command.namespace', 'Lean.Parser.Command.end',
                   'Lean.Parser.Command.open', 'Lean.Parser.Command.variable',
                   'Lean.Parser.Command.universe', 'Lean.Parser.Command.moduleDoc',
                   'Lean.Parser.Command.eoi'}
        contexts = {}
        contextual = []
        namespace_stack = []
        vars_stack = [[]]
        opens_stack = [[]]
        for c in commands:
            kind = c['syntaxKind']
            check(c['isDeclaration'] or kind in allowed, 'Unsupported context: ' + kind)
            if c['isDeclaration']:
                check(c['range'] is not None, 'Declaration command lacks range')
                contextual.append((rng(c['range'])[0], list(namespace_stack),
                                   [v for vs in vars_stack for v in vs],
                                   [o for os in opens_stack for o in os]))
                continue
            if kind == 'Lean.Parser.Command.eoi':
                continue
            check(c['range'] is not None and c.get('contextSyntax') is not None,
                  'Context has no AST/range: ' + kind)
            ids = [n['identifier'] for n in walk(c['contextSyntax']) if 'identifier' in n]
            atoms = [n['atom'] for n in walk(c['contextSyntax']) if 'atom' in n]
            if kind == 'Lean.Parser.Command.namespace':
                check(len(ids) == 1 and ids[0] in {'Iut', 'ChebyshevBound', 'LocalHeightData'},
                      'Unreviewed namespace form')
                namespace_stack.append(ids[0]); vars_stack.append([]); opens_stack.append([])
            elif kind == 'Lean.Parser.Command.end':
                check(namespace_stack and ids == [namespace_stack[-1]], 'Unsupported end/namespace mismatch')
                namespace_stack.pop(); vars_stack.pop(); opens_stack.pop()
            elif kind == 'Lean.Parser.Command.open':
                check(ids == ['Finset','Real'] and atoms == ['open'], 'Only original open Finset Real supported')
                opens_stack[-1].append(c)
            elif kind == 'Lean.Parser.Command.variable':
                vars_stack[-1].append(c)
            elif kind == 'Lean.Parser.Command.universe':
                check(ids == ['w'], 'Only original universe w supported')
        check(not namespace_stack, 'Unclosed namespace context')
        for d in declarations:
            candidates = [x for x in contextual if x[0] == d['declStart']['offset']]
            check(len(candidates) == 1, 'Declaration/command context join failed')
            contexts[span(d)] = candidates[0][1:]
        groups, members = {}, {span(d): set() for d in declarations}
        for name, row in rows.items():
            check(not row.get('hasSorryAx') and not (set(row['axioms'])-ALLOWED_AXIOMS),
                  'Unapproved source axioms: ' + name)
            if not row['startLine']:
                continue
            p = (row.get('selectionRange') or row['range'])['start']
            candidates = [d for d in declarations if
                          (d['declStart']['line'], d['declStart']['col']) <= (p['line'],p['col']) <
                          (d['declEnd']['line'], d['declEnd']['col'])]
            check(len(candidates) == 1, 'Ambiguous/missing compiler span join: ' + name)
            groups[name] = span(candidates[0]); members[groups[name]].add(name)
        decls = {span(d): d for d in declarations}
        primary = {}
        for key,d in decls.items():
            ns = '.'.join(contexts[key][0])
            name = ns + '.' + d['nameText']
            check(name in members[key], 'Compiler binding identity mismatch: ' + name)
            primary[key] = name
        def deps(n):
            return set(rows[n]['typeDeps'] + rows[n]['valueDeps'] + rows[n]['constructors'])
        def closure(seeds, stop=frozenset()):
            reached, work = set(), list(seeds)
            while work:
                n = work.pop()
                if n in reached:
                    continue
                check(n in rows, 'Graph missing dependency: ' + n)
                reached.add(n)
                if n not in stop:
                    work.extend(deps(n) - reached)
            return reached
        reached = closure(ROOTS | {n for n,r in rows.items() if r.get('isInstance')})
        while True:
            companions = set().union(*(members[groups[n]] for n in reached if n in groups))
            expanded = closure(reached | companions)
            if expanded == reached:
                break
            reached = expanded
        kept = {groups[n] for n in reached if n in groups}
        definition_groups = {key for key in kept if rows[primary[key]]['kind'] != 'theorem'}
        def_closure = closure(set().union(*(members[g] for g in definition_groups)))
        definition_groups |= {groups[n] for n in def_closure if n in groups}
        check(not ROOTS & def_closure, 'Definitions require a theorem node; split rejected')
        helper_groups = kept - definition_groups - {groups[n] for n in ROOTS}
        for key in helper_groups:
            d = decls[key]
            check(rows[primary[key]]['kind'] == 'theorem' and d['valStart'] and
                  d['declEnd']['line'] - d['valStart']['line'] <= 10,
                  'Unreviewed helper promotion/size: ' + primary[key])
        # AST namespace/open/variable contexts must not silently reference omitted
        # project constants. Require their graph closure to be provided by Defs.
        for c in commands:
            if c['isDeclaration'] or c['range'] is None:
                continue
            a,b = rng(c['range'])
            project_refs = {r['const'] for r in refs if a <= r['start']['offset'] and
                            r['end']['offset'] <= b and r['const'] in rows}
            check(all(n not in groups or groups[n] in definition_groups for n in closure(project_refs)),
                  'Preserved context needs missing theorem/material')
        # A parser-only compiler supplement supplies target keyword atom spans.
        # It must identify the exact normalized input, and no source token scan
        # is accepted as a substitute for these ranges.
        keyword_rows = load_lines(args.keyword_facts)
        keyword_sources = [r for r in keyword_rows if r.get('kind') == 'source']
        check(len(keyword_sources) == 1 and
              keyword_sources[0].get('normalizedSha256') == result['normalizedSha256'],
              'Keyword supplement is not bound to normalized source')
        keyword_by_name = {r['name']:r for r in keyword_rows if r.get('kind') == 'keyword'}
        check(set(keyword_by_name) == ROOTS and sum(r.get('kind') == 'keyword' for r in keyword_rows) == len(ROOTS), 'Keyword supplement target set mismatch/duplicates')
        def render_skeleton(selected, extra_imports):
            changes = [(a,b,b'') for a,b in decls if (a,b) not in selected]
            insertion = b'\n' + ''.join('import '+i+'\n' for i in extra_imports).encode() + \
                        ('\nnamespace '+PREFIX+'\n').encode()
            changes.append((header_end,header_end,insertion))
            return edits(data,changes) + ('\nend '+PREFIX+'\n').encode()
        def slug(name):
            full = PREFIX + '.' + name
            check(full.isascii() and all(p.isidentifier() for p in full.split('.')), 'Unsafe platform name')
            return full.replace('.','_')
        def save(module,text):
            p = out/(module.replace('.','/')+'.lean')
            p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(text)
            report['generatedFiles'].append({'module':module,'path':str(p),'sha256':sha(p),'bytes':len(text)})
            return p
        save(DEF_MODULE, render_skeleton(definition_groups, []))
        nodes=[]
        for name in sorted(ROOTS):
            key=groups[name]; d=decls[key]
            check(not d.get('privateTok') and d.get('valKind') == 'simple', 'Unsupported target wrapper/value')
            check(not ((closure(rows[name]['typeDeps']) & ROOTS)-{name}), 'Target statement needs a node import; explicit review required')
            check(rng(d['nameRange'])[1] <= d['valStart']['offset'], 'Binding overlaps proof')
            ns, variables, opens = contexts[key]
            check(ns and ns[0]=='Iut', 'Target original namespace missing')
            relocation_refs = [r for r in refs if r['const'] == 'Iut.log_natCast_nonneg'
                               and d['valStart']['offset'] <= r['start']['offset']
                               and r['end']['offset'] <= key[1]]
            expected_relocations = {'Iut.ChebyshevBound.exists_prime_notMem':1,
                                    'Iut.LocalHeightData.exists_prime_selection':4,
                                    'Iut.sum_log_primeFactors_le':0}
            check(len(relocation_refs) == expected_relocations[name], 'Unexpected exact ambiguity-fix reference count')
            relocation_edits = [(r['start']['offset'],r['end']['offset'],
                                 (PREFIX+'.'+r['const']).encode()) for r in relocation_refs]
            relocated_proof = edits(data[d['valStart']['offset']:key[1]],
                [(a-d['valStart']['offset'],b-d['valStart']['offset'],replacement)
                 for a,b,replacement in relocation_edits])
            def command_target(newname, stub):
                start,end=key; changes=[]
                a,b=rng(d['nameRange']);changes.append((a-start,b-start,newname.encode()))
                keyword_fact = keyword_by_name[name]
                x,y = rng(keyword_fact['keywordRange'])
                check(start <= x < y <= a and keyword_fact['keyword'] in {'lemma','theorem'},
                      'Invalid compiler keyword range')
                check(data[x:y] == keyword_fact['keyword'].encode(),
                      'Compiler keyword range/source mismatch')
                changes.append((x-start,y-start,b'theorem'))
                if d.get('docstring'):
                    x,y=rng(d['docstring']);changes.append((x-start,y-start,b''))
                if stub:
                    changes.append((d['valStart']['offset']-start,end-start,b':= by\n  sorry'))
                else:
                    changes.extend((a-start,b-start,replacement) for a,b,replacement in relocation_edits)
                return edits(data[start:end],changes)
            active = '\n'+''.join('open '+PREFIX+'.'+'.'.join(ns[:i])+'\n' for i in range(1,len(ns)+1))
            active += ''.join(data[slice(*rng(c['range']))].decode()+'\n' for c in opens)
            active += ''.join(data[slice(*rng(c['range']))].decode()+'\n' for c in variables)
            full=PREFIX+'.'+name
            formal=command_target(full,True)
            thm_preamble=render_skeleton(set(),[DEF_MODULE])+active.encode()
            theorem_module='Theorems.Thm_'+slug(name)
            save(theorem_module,thm_preamble+formal+b'\n')
            pc=closure(rows[name]['valueDeps'],ROOTS)
            child_nodes=sorted((pc & ROOTS)-{name})
            needed={groups[n] for n in pc if n in groups} & helper_groups
            solution_imports=[DEF_MODULE]+['Theorems.Thm_'+slug(n) for n in child_nodes]
            solution=render_skeleton(needed,solution_imports)+active.encode()+command_target('solution',False)+b'\n'
            sol_module='Solutions.Sol_'+slug(name)
            save(sol_module,solution)
            check(theorem_module not in solution_imports,'Solution imports own target')
            payload={'theorem_name':full,'preamble':thm_preamble.decode(),
                     'formal_statement':formal.decode(),'solution':solution.decode()}
            payload_path=out/'payloads'/(slug(name)+'.json');payload_path.parent.mkdir(exist_ok=True)
            payload_path.write_text(json.dumps(payload,ensure_ascii=False,indent=2)+'\n')
            nodes.append({'name':name,'theoremName':full,'proofLines':d['declEnd']['line']-d['valStart']['line'],
                          'children':child_nodes,'inlineHelpers':[primary[g] for g in sorted(needed)],
                          'targetCommandRange':list(key),
                          'originalProofSha256':hashlib.sha256(data[d['valStart']['offset']:key[1]]).hexdigest(),
                          'generatedProofSha256':hashlib.sha256(relocated_proof).hexdigest(),
                          'originalProofBytesIdentical':not relocation_refs,
                          'proofTransformation':'Original proof bytes with only the listed compiler-reference relocations',
                          'referenceRelocations':[{'const':r['const'],'sourceRange':{'start':r['start'],'end':r['end']},
                            'originalText':data[r['start']['offset']:r['end']['offset']].decode(),
                            'replacement':PREFIX+'.'+r['const']} for r in relocation_refs],
                          'payload':str(payload_path)})
        report.update(status='generated-draft-requires-main-agent-CI',nodes=nodes,
                      definitionCommands=[primary[g] for g in sorted(definition_groups)],
                      source={'graphSha256':sha(args.graph),'graphReceiptSha256':sha(args.graph_receipt),
                              'stage2ReceiptSha256':sha(args.stage2_receipt),
                              'stage2CiResultSha256':sha(args.stage2_ci_result),
                              'stage2CiJobId':ci['job_id'],
                              'keywordFactsSha256':sha(args.keyword_facts),
                              'normalizedSha256':result['normalizedSha256']},
                      subtraction={'retainedSourceCommands':len(kept),'allSourceCommands':len(declarations)},
                      acceptance={'exactTextCompilation':False,'typeComparison':False,'axiomAudit':False},
                      consumer={'actualOriginalConsumer':'Iut.Corollary22Inputs.c2 proof directly calls L.exists_prime_selection (original line 441), producing the P1-P3 witness',
                                'canonicalC22Connected':False})
    except (ValueError,KeyError,FileNotFoundError) as ex:
        report['error']=str(ex)
        report['status']='inputs-pending' if 'missing:' in str(ex) else 'refused-unsupported-or-unbound-input'
    (out/'dry-run-report.json').write_text(json.dumps(report,ensure_ascii=False,indent=2)+'\n')
    print(json.dumps(report,ensure_ascii=False,indent=2))
    return 0 if report['status'].startswith('generated-') else 2

if __name__=='__main__':
    raise SystemExit(main())
