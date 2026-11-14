"""Main-agent delivery tool. Generation does not compile or contact the API.

Install this file in the adaptation unit only after reviewing it. All evidence
files are produced by actual main-agent MCP-CI jobs or independent reviewers.
"""
from pathlib import Path
import ast
import hashlib
import importlib.util
import json
import sys
import time
import urllib.error
import urllib.request
import uuid

r = Path('/home/admin-wsl/Coq/abc')
w = r / 'prove2me_workspace'
u = '.local/adaptation/polar-presentation-height-sourceproof-20261114/'
b = w / u
pre = 'AbcAdaptation.Tripod.Fermat.Proper.'
short = 'polarPresentationHeightSum_of_principalRelation'
target = pre + short
source = 'Theorems/Thm_' + target.replace('.', '_') + '.lean'
helper_names = ['FermatPolarAbsoluteExtension', 'FermatPolarAbsoluteBasic',
                'FermatPolarPointAdapters', 'FermatPolarTupleHeight',
                'FermatPolarMinOrd', 'FermatPolarRootBound',
                'FermatPolarIntegrality', 'FermatPolarPresentationHeights']
helpers = ['Solutions/Source_' + n + '.lean' for n in helper_names]
checks = 'Solutions/Checks_FermatPolarPresentationHeights.lean'
consumer = 'Theorems/Thm_' + (pre + 'belyiHeightRelation').replace('.', '_') + '.lean'
sol = u + 'Solution_' + short + '.lean'
ENV = '0df444a360eaa60ab8c11dca51a86af692955474'
ROOT = 'e33ff731-60a7-43ef-87ae-c12aeba23cb5'
PARENT = '7cc0a201-c92c-4ff4-8377-f8ee6000a274'
STANDARD = {'propext', 'Classical.choice', 'Quot.sound'}
PACKETS = ['blind-readbacks-tuple.json', 'blind-readbacks-comparison.json',
           'blind-readback-rational-height.json']
ARGS = 'M hDVR hRF D E RD RE f r hr hrel'


def read(n):
    return json.loads((b / n).read_text())


def save(n, value):
    (b / n).write_text(json.dumps(value, ensure_ascii=False, indent=2) + '\n')


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def graph():
    return [json.loads(line) for line in (b / 'decl_graph.jsonl').read_text().splitlines() if line.strip()]


def module(path):
    return path[:-5].replace('/', '.')


def syntax(path, name):
    hits = [z for z in read('syntax-boundaries.json')
            if z['file'] == path and z['nameText'] == name.split('.')[-1]]
    assert len(hits) == 1, (path, name, len(hits))
    return hits[0]


def declaration_start(span):
    start = span['declStart']['offset']
    doc = span['docstring']
    if doc and doc['start']['offset'] == start:
        start = doc['end']['offset']
    return start


def header(path, name, replacement=None):
    """Copy parser bytes: retain original binder syntax and only change name."""
    span = syntax(path, name)
    raw = (w / path).read_bytes()
    ns, ne = span['nameRange']['start']['offset'], span['nameRange']['end']['offset']
    assert raw[ns:ne].decode() == name.split('.')[-1]
    namebytes = raw[ns:ne] if replacement is None else replacement.encode()
    return (raw[declaration_start(span):ns] + namebytes + raw[ne:span['valStart']['offset']]).decode().strip()


def packet_rows(packet):
    return packet['records'] if 'records' in packet else packet['declarations']


def bind():
    g = graph()
    out, historical = [], {}
    for packet_name in PACKETS:
        packet = read(packet_name)
        rows = packet_rows(packet)
        historical[packet_name] = {k: v for k, v in packet.items() if k not in ['records', 'declarations']}
        for row in rows:
            name = row.get('source_level_qualified_name') or row['qualified_logical_name']
            original = Path(row['source_file'])
            original_sha = row.get('file_sha256') or row['source_sha256']
            assert sha(original) == original_sha, original
            path = ('Solutions/Source_FermatPolarIntegrality.lean' if packet_name == PACKETS[2]
                    else 'Solutions/' + original.name)
            assert path in helpers, path
            hits = [z for z in g if z['module'] == module(path)
                    and z['userName'] == name and z['startLine'] > 0]
            assert len(hits) == 1, (name, len(hits))
            z = hits[0]
            actual = header(path, name)
            assert actual.endswith(row['raw_signature'].strip()), (name, actual, row['raw_signature'])
            languages = row['readback']
            out.append({'declaration': z['name'], 'userName': z['userName'],
                        'path': path, 'module': z['module'], 'source_sha256': sha(w / path),
                        'compiler_type': z['elaboratedType'],
                        'source_span': {'start_line': z['startLine'], 'end_line': z['endLine']},
                        'compiler_parser_span': syntax(path, name),
                        'blind_original_path': str(original), 'blind_original_sha256': original_sha,
                        'original_packet': packet_name, 'original_packet_sha256': sha(b / packet_name),
                        'raw_signature': row['raw_signature'], 'original_blind_row': row,
                        'original_blind_elaboration': row.get('elaboration') or row.get('parameter_status')
                            or row.get('inferred_parameters'),
                        'elaboration': {'status': 'compiler_bound', 'compiler_qualified_name': z['name'],
                                        'scope': 'Current graph/parser evidence only; source-only notes remain historical.'},
                        'en': languages['en'], 'zh_Hans': languages.get('zh_Hans') or languages['zh-Hans'],
                        'ja': languages['ja'], 'quotation': None,
                        'proof_notes': {'scope': 'Blind readback did not assess proof correctness.',
                                        'current_binding': 'Compiler graph type and parser source spans; independent retained-binder review is a separate required receipt.'}})
    assert len(out) == 121 and len({z['declaration'] for z in out}) == 121
    # Ensure each authored helper command, including unused commands, is bound.
    for path in helpers:
        parsed = [z for z in read('syntax-boundaries.json') if z['file'] == path]
        bound = [z for z in out if z['path'] == path]
        assert {z['nameText'] for z in parsed} == {z['userName'].split('.')[-1] for z in bound}, path
        assert len(parsed) == len(bound), path
    oldpath = w / '.local/adaptation/belyi-height-split-20261114/final-readbacks.json'
    old = next(z for z in json.loads(oldpath.read_text())['declarations'] if z['declaration'] == target)
    z = next(z for z in g if z['name'] == target)
    assert old['compiler_type'] == z['elaboratedType'], 'Reused target type changed'
    out.append(old | {'path': source, 'source_sha256': sha(w / source),
                      'compiler_type': z['elaboratedType'],
                      'source_span': {'start_line': z['startLine'], 'end_line': z['endLine']},
                      'reused_from': str(oldpath.relative_to(w)), 'reused_packet_sha256': sha(oldpath),
                      'reuse_basis': 'Unchanged exact compiler type; original independent target readback reused.',
                      'original_proof_notes': old.get('proof_notes'),
                      'proof_notes': {'scope': 'Historical target notes describe the previous placeholder.',
                                      'current_formal_body': 'Actual source tuple monotonicity supplied to the exact presentation composer.',
                                      'validation': 'Current closed source and consumer receipts required separately.'}})
    # Apply actual independent compiler-type readback corrections, preserving the blind originals.
    audit_path = b / 'compiler-readback-type-review.json'
    if audit_path.exists():
        audit = read('compiler-readback-type-review.json')
        assert audit['passed'] and audit['compiler_evidence']['graph_sha256'] == sha(b / 'decl_graph.jsonl')
        by_name = {z['declaration']: z for z in out}
        for row in audit['declarations']:
            correction = row.get('corrected_trilingual_statement')
            if correction:
                entry = by_name[row['compiler_name']]
                entry['superseded_blind_statements'] = {lang: entry[lang] for lang in ['en','zh_Hans','ja']}
                entry.update(correction)
                entry['compiler_readback_correction'] = 'compiler-readback-type-review.json'
    save('historical-blind-source-notes.json', historical)
    save('final-readbacks.json', {'declarations': out, 'blind_readback': True,
                                'compiler_bound': True, 'quotations_separate': True,
                                'retained_binder_review': 'Required separately; this file does not assert that it passed.'})


def closure():
    g = graph()
    index = {z['name']: z for z in g}
    mods = {module(path) for path in helpers}
    instances = {z['name'] for z in g if z['module'] in mods and z['isInstance']}
    reached, todo = set(), [target] + sorted(instances)
    while todo:
        name = todo.pop()
        if name in reached:
            continue
        reached.add(name)
        z = index.get(name)
        if z:
            todo += z['typeDeps'] + z['valueDeps']
    authored = [z for z in g if z['module'] in mods and z['startLine'] > 0]
    assert target in index and index[target]['module'] == module(source)
    # Prove graph evidence includes each source unit before using it for pruning.
    for path in helpers:
        assert any(z['module'] == module(path) for z in authored), path
    return authored, reached, instances


def generate():
    bind()
    authored, reached, instances = closure()
    imports, bodies, removals, retained = [], [], [], []
    for path in helpers + [source]:
        raw = (w / path).read_bytes()
        edits = []
        if path == source:
            span = syntax(path, target)
            edits.append((span['nameRange']['start']['offset'], span['nameRange']['end']['offset'], b'closedPolarHeightSource'))
        else:
            rows = [z for z in authored if z['module'] == module(path)]
            for z in rows:
                span = syntax(path, z['userName'])
                if z['name'] in reached:
                    retained.append(z['name'])
                    continue
                # The WHOLE outer command is removed. This includes scoped
                # `open ... in`, `omit ... in`, local attributes and docstrings.
                start = span['cmdStart']['start']['offset']
                end = span['cmdEnd']['offset']
                assert span['cmdStart']['end']['offset'] == end
                assert 0 <= start <= span['declStart']['offset'] < end <= len(raw)
                edits.append((start, end, b''))
                removals.append({'name': z['name'], 'path': path, 'cmd_start': start, 'cmd_end': end})
        ordered = sorted(edits)
        assert all(a[1] <= c[0] for a, c in zip(ordered, ordered[1:])), path
        for start, end, replacement in reversed(ordered):
            raw = raw[:start] + replacement + raw[end:]
        lines = []
        for line in raw.decode().splitlines(keepends=True):
            if line.startswith('import '):
                imp = line.strip()
                name = imp.removeprefix('import ')
                if name in {module(p) for p in helpers}:
                    continue
                assert name.startswith(('Definitions.', 'Mathlib.')), imp
                if imp not in imports:
                    imports.append(imp)
            else:
                lines.append(line)
        bodies.append(''.join(lines).strip())
    assert set(retained) == {z['name'] for z in authored if z['name'] in reached}
    assert instances <= reached
    # Raw binder style from the parser; the original platform forall type is
    # independently re-parsed below and checked by the compiler.
    exact = header(source, target, 'solution')
    assert exact.startswith('theorem solution {N : ℕ}')
    code = '\n'.join(imports) + '\n\nset_option autoImplicit false\n\n' + '\n\n'.join(bodies)
    code += '\n\nopen ' + pre.rstrip('.') + '\n\n' + exact
    code += ' := by\n  exact ' + pre + 'closedPolarHeightSource ' + ARGS + '\n'
    assert 'sorry' not in code and 'import Solutions.' not in code
    assert 'import ' + module(source) not in code
    (w / sol).write_text(code)
    formal = read('platform-before-parent.json')['formal_statement']
    assert formal.startswith('theorem ' + target + ' ') and formal.endswith(' := by sorry')
    original = formal.replace('theorem ' + target, 'theorem PlatformOriginalType', 1).removesuffix(' := by sorry')
    audit = 'import Lean\n' + code + '\n' + original + ' := solution\n'
    audit += '''
open Lean
run_meta do
  let a ← getConstInfo `solution
  let e ← getConstInfo `PlatformOriginalType
  unless ← Lean.Meta.isDefEq a.type e.type do throwError "Original platform type differs"
  let axs ← collectAxioms `solution
  for ax in axs do
    unless #[`propext, `Classical.choice, `Quot.sound].contains ax do throwError "Unexpected solution axiom {ax}"
  IO.FS.writeFile "OUTPUT" (Json.pretty (Json.mkObj [("type",Json.str (← Lean.Meta.ppExpr a.type).pretty),("axioms",toJson (axs.map toString)),("original_type_equal",Json.bool true)]))
'''.replace('OUTPUT', u + 'solution-type-axioms.json')
    (b / 'AuditSolution.lean').write_text(audit)
    save('solution-source-closure.json', {
        'source': sol, 'source_sha256': sha(w / sol), 'graph_sha256': sha(b / 'decl_graph.jsonl'),
        'parser_sha256': sha(b / 'syntax-boundaries.json'), 'root': target,
        'extra_instance_roots': sorted(instances), 'retained_helpers': sorted(retained),
        'removed_whole_commands': removals, 'retained_count': len(retained),
        'source_hashes': {p: sha(w / p) for p in helpers + [source]},
        'source_body_changes': 'Unused whole declarations removed; target wrapper name only renamed. Lexical contexts preserved.',
        'type_source': 'Compiler parser byte-range raw binder header; original platform forall type audited separately.',
        'imports': imports, 'no_own_target_import': True, 'no_upstream_import': True,
        'new_nodes': [], 'new_open_debt': 0})


def checked(tag, path, review=False, artifact=False):
    z = read(tag + '-result.json')
    q, rs = z['request'], z['result']
    assert z['status'] == 'succeeded' and rs['exit_code'] == 0, tag
    assert 'sorryAx' not in rs.get('stdout', '') + rs.get('stderr', ''), tag
    assert q['exclusive'] and q['workspace'] == str(w), tag
    params = {'args': [path, '-o', '.lake/build/lib/lean/' + path[:-5] + '.olean']} if artifact else {'source': path}
    assert q['parameters'] == params, tag
    assert q['task_type'] == ('full' if artifact else 'review' if review else 'leaf'), tag
    assert q['worktree_manifest']['source_sha256'] == sha(w / path), tag
    assert rs['actual_arguments'] == (['lean'] + params['args'] if artifact else ['lean', path]), tag
    assert rs['snapshot']['workspace_mode'] == 'exclusive_worktree' and rs['snapshot']['snapshot_id'] is None, tag
    if review:
        assert rs['review']['passed'], tag
    # Present resource values must retain physical-memory compliance; missing
    # measurements remain unknown and are not represented as zero.
    rss = z.get('resources', {}).get('peak_rss_bytes')
    assert rss is None or rss <= 16 * 1024**3, tag
    return z


def preflight():
    jobs = []
    for name, path in zip(helper_names, helpers):
        jobs += [checked(name + '-leaf', path), checked(name + '-artifact', path, artifact=True)]
    tag = 'Thm_' + target.replace('.', '_')
    jobs += [checked(tag + '-leaf', source), checked(tag + '-artifact', source, artifact=True)]
    required = [('closed-axioms-review', checks, True),
                ('source-graph-leaf', u + 'ExtractPolarHeightGraph.lean', False),
                ('syntax-leaf', u + 'ExtractPolarHeightSyntax.lean', False),
                ('all-constants-review', u + 'AuditAllConstants.lean', True),
                ('direct-solution-leaf', sol, False),
                ('solution-type-axioms-review', u + 'AuditSolution.lean', True),
                ('production-gates-review', u + 'ProductionGates.lean', True),
                ('consumer-parent-leaf', consumer, False),
                ('consumer-closed-review', u + 'ChecksBelyiHeightClosed.lean', True)]
    jobs += [checked(*row) for row in required]
    jobs.append(checked('consumer-parent-artifact', consumer, artifact=True))
    axs = read('all-module-axioms.json')
    expected = {z['name'] for z in graph() if z['module'] in {module(p) for p in helpers + [source]}}
    assert expected <= {z['name'] for z in axs}
    assert all(set(z['axioms']) <= STANDARD for z in axs)
    audit = read('solution-type-axioms.json')
    assert audit['original_type_equal'] and set(audit['axioms']) <= STANDARD
    own = helpers + [source, checks]
    inputs = read('production-gates-review-result.json')['request']['worktree_manifest']['input_hashes']
    assert all(inputs[p] == sha(w / p) for p in own)
    rb = read('final-readbacks.json')['declarations']
    assert len(rb) == 122 and all(z['source_sha256'] == sha(w / z['path']) for z in rb)
    bound = {z['declaration']: z for z in rb}
    binder = read('compiler-readback-type-review.json')
    assert binder['passed'] and binder['compiler_evidence']['graph_sha256'] == sha(b / 'decl_graph.jsonl')
    assert {z['path']: z['sha256'] for z in binder['original_packets']} == {p: sha(b / p) for p in PACKETS}
    rows = binder['declarations']
    assert len(rows) == 121 and {z['compiler_name'] for z in rows} == set(bound) - {target}
    for row in rows:
        z = bound[row['compiler_name']]
        assert row['passed'] and row['compiler_type'] == z['compiler_type']
        assert row['current_source']['sha256'] == z['source_sha256']
        if row.get('corrected_trilingual_statement'):
            assert all(z[lang] == row['corrected_trilingual_statement'][lang] for lang in ['en','zh_Hans','ja'])
    close = read('solution-source-closure.json')
    assert close['source_sha256'] == sha(w / sol) and 'sorry' not in (w / sol).read_text()
    assert close['graph_sha256'] == sha(b / 'decl_graph.jsonl') and close['parser_sha256'] == sha(b / 'syntax-boundaries.json')
    assert all(close['source_hashes'][p] == sha(w / p) for p in helpers + [source])
    review = read('independent-delivery-review.json')
    assert review['passed'] and review['solution_sha256'] == sha(w / sol)
    save('delivery-validation.json', {'passed': True, 'original_platform_type_equal': True,
                                     'new_platform_nodes': [], 'new_open_debt': 0, 'readbacks': 122,
                                     'closed_source_reuse': True, 'compiler_checks': [z['job_id'] for z in jobs],
                                     'owned_source_hashes': {p: sha(w / p) for p in own},
                                     'unchanged_consumer_source_hashes': {consumer: sha(w / consumer)},
                                     'independent_delivery_review_sha256': sha(b / 'independent-delivery-review.json')})


def prose(rows):
    return '\n\n'.join('**' + title + '**\n\n' + '\n\n'.join('`' + z['userName'] + '`\n\n' + z[lang] for z in rows)
                         for lang, title in [('en', 'English'), ('zh_Hans', '简体中文'), ('ja', '日本語')])


def publish():
    preflight()
    spec = importlib.util.spec_from_file_location('api', w / '.local/abc-item/api.py')
    api = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(api)
    assert api.base == 'https://prove2.me/api/v1'
    ident = read('target-id.json')['id']
    before = read('platform-before-parent.json')
    current = api.request('/theorems/' + ident)
    assert current['formal_statement'] == before['formal_statement']
    assert current['theorem_name'] == target and current['visibility'] == 'private' and current['mathlib_rev'] == ENV
    context = globals() | {'api': api}
    protocol = (w / '.local/adaptation/platform-tripod-20261113/executed-platform-publish.py').read_text()
    functions = [n for n in ast.parse(protocol).body if isinstance(n, ast.FunctionDef) and n.name == 'verify']
    assert len(functions) == 1
    exec(compile(ast.Module(body=functions, type_ignores=[]), '<established-protocol>', 'exec'), context)
    rb = read('final-readbacks.json')['declarations']
    selected_names = {target, pre + 'polarPresentationHeightSum_of_tupleMonotonicity',
                      pre + 'PolarTuple.tupleHeight_le_of_minOrd_le'}
    selected = [z for z in rb if z['userName'] in selected_names]
    assert len(selected) == 3
    quote = (b / 'quotation.md').read_text().strip()
    origin = ('Shinichi Mochizuki, Arithmetic Elliptic Curves in General Position (February 2009), '
              'Proposition 1.4(i),(iii), Theorem 2.1 and its proof, pp.6,11–13. '
              'Official PDF https://www.kurims.kyoto-u.ac.jp/~motizuki/Arithmetic%20Elliptic%20Curves%20in%20General%20Position.pdf ; '
              'SHA256 b9dc115af61dca7fe434332ebafddf6a376a9e2926dad4e1ea2dcc0d2441f768. '
              'The presentation-level auxiliary is formal-source mathematics, not a verbatim paper quotation. '
              'Exact Heights source bodies are pinned at 721496ca4c158e511d25d8ccf6bfe8503eda73c1: '
              'Heights/Absolute/Extension.lean, Basic.lean, RootBound.lean, Northcott.lean; '
              'Heights/Curve/TupleHeight.lean, Integrality.lean, LinearEquiv.lean. '
              'The min-order product/scaling lemmas and presentation composer adapt LinearEquiv.lean to the supplied local polar presentations. '
              'Original Apache-2.0 notices, source hashes and adaptation ledger are retained. '
              'The direct proof uses actual tuple-height monotonicity from integral dependence and local bounds, '
              'not a new source-law hypothesis. All 122 readbacks, their source contexts and independent retained-binder audit remain in local evidence.')
    notes = (r'For each supplied polar presentation, pair the two coordinates $(1,a)$ and $(1,b)$. '
             r'Their tuple heights equal the supplied function heights, including poles, and their minimum orders equal the negatives of their pole multiplicities. '
             r'The principal relation makes the positive presentation product and the negative presentation product together with $(1,f)$ have equal minimum order after the latter tuple is scaled by $r^{-1}$. '
             r'Integral dependence, local root bounds, and the number-field height sum prove the uniform tuple-height comparison in each direction. '
             r'Scaling invariance and additivity under tuple products give the desired uniform absolute bound. '
             r'The proof retains arbitrary supplied presentations, every proper place, all algebraic points, zero functions, and the original nonzero premise on $r$.')
    explanation = notes + '\n\n' + quote + '\n\n' + prose(selected) + '\n\n' + origin
    assert len(explanation) <= 50000, len(explanation)
    tag = 'prove-' + short
    request = {'theorem_id': ident, 'proof_type': 'prove', 'file': sol,
               'source_sha256': sha(w / sol), 'explanation': explanation}
    if (b / (tag + '-verify-submit.json')).exists():
        assert read(tag + '-verify-request.json') == request
    else:
        # An unresolved mutation sentinel is not permission to repeat the POST.
        assert not (b / (tag + '-verification-requested.json')).exists(), 'Reconcile prior POST before retry'
        save(tag + '-verification-requested.json', request)
    result = context['verify'](tag, ident, sol, explanation)
    assert result['status'] == 'ACCEPTED'
    patch = {'natural_language_statement': quote + '\n\n' + prose([z for z in rb if z['declaration'] == target]), 'source': origin}
    save('parent-metadata-patch-request.json', patch)
    current = api.request('/theorems/' + ident)
    if not all(current.get(k) == v for k, v in patch.items()):
        save('parent-metadata-patch-response.json', api.request('/theorems/' + ident, patch, 'PATCH'))
    current = api.request('/theorems/' + ident)
    assert current['status'] == 'Proved' and current['formal_statement'] == before['formal_statement']
    assert all(current[k] == v for k, v in patch.items())
    save('platform-after-parent.json', current)
    parent = api.request('/theorems/' + PARENT)
    assert parent['theorem_name'] == pre + 'belyiHeightRelation' and parent['status'] == 'Proved'
    old_sentence = 'Both child proofs remain Open.'
    if old_sentence in parent['source']:
        save('automatic-parent-metadata-before.json', parent)
        parent_patch = {'source': parent['source'].replace(old_sentence,
            'Both exact children are now Proved: canonicalCuspPolarLinearEquivalence and polarPresentationHeightSum_of_principalRelation. The existing two-child reduction therefore proves this parent.')}
        save('automatic-parent-metadata-patch-request.json', parent_patch)
        save('automatic-parent-metadata-patch-response.json', api.request('/theorems/' + PARENT, parent_patch, 'PATCH'))
        refreshed = api.request('/theorems/' + PARENT)
        assert refreshed['formal_statement'] == parent['formal_statement']
        assert refreshed['natural_language_statement'] == parent['natural_language_statement']
        assert refreshed['source'] == parent_patch['source'] and refreshed['status'] == 'Proved'
        parent = refreshed
    save('platform-after-belyiHeightRelation.json', parent)
    root = api.request('/theorems/' + ROOT)
    assert root['status'] == 'Open'
    save('platform-after-root.json', root)
    sys.path.insert(0, str(w / '.local/adaptation/northcott-sourceproof-20261114'))
    from graph_completion import fetch_complete_math_graph
    final_graph = fetch_complete_math_graph(api, ROOT, save, 'root-graph-after')
    assert final_graph['mathematical_closure_complete']
    save('root-graph-after.json', final_graph)
    assert {z['theorem_id'] for z in final_graph['nodes']
            if z['node_type'] == 'theorem' and z['status'] != 'Definition'} == {
        z['theorem_id'] for z in read('root-graph-before.json')['nodes']
        if z['node_type'] == 'theorem' and z['status'] != 'Definition'}
    leaves = []
    while True:
        page = api.request('/theorems/' + ROOT + '/open-leaves?limit=50&offset=' + str(len(leaves)))
        save('root-frontier-after-page-' + str(len(leaves)) + '.json', page)
        leaves += page['open_leaves']
        if len(leaves) >= page['total']:
            break
        assert page['open_leaves'], 'Incomplete frontier pagination'
    assert len(leaves) == page['total']
    save('root-frontier-after.json', {'open_leaves': leaves, 'total': page['total'], 'all_pages_fetched': True})
    old = read('root-frontier-before.json')
    assert old['total'] == 19 and page['total'] == 18
    assert {z['theorem_id'] for z in leaves} == {z['theorem_id'] for z in old['open_leaves']} - {ident}
    print('Exact polar-presentation source proof ACCEPTED; belyiHeightRelation Proved; root Open; complete frontier 19 -> 18.', flush=True)


if __name__ == '__main__':
    {'bind': bind, 'generate': generate, 'preflight': preflight, 'publish': publish}[sys.argv[1]]()
