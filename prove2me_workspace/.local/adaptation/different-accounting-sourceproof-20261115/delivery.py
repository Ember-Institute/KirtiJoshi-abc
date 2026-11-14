"""Root-only direct different-accounting delivery. No import-time effects.
No compiler, new node publication, Git mutation, registry or pending DB update.
"""
from pathlib import Path
import ast
import hashlib
import importlib.util
import json
import math
import subprocess
import sys
import time
import urllib.error
import urllib.request
import uuid

r = Path('/home/admin-wsl/Coq/abc')
w = r / 'prove2me_workspace'
u = '.local/adaptation/different-accounting-sourceproof-20261115/'
b = w / u
pre = 'AbcAdaptation.Tripod.Fermat.Proper.'
target = pre + 'belyiActualFieldDifferentAccounting'
parent = target
PARENT_ID = 'd7edb0f4-a7cb-4ab5-8cf1-46eea7d81aa3'
verify_tag = 'prove-belyiActualFieldDifferentAccounting'
source = 'Theorems/Thm_' + target.replace('.', '_') + '.lean'
helper = 'Solutions/Source_FermatBelyiDifferentAccounting.lean'
checks = 'Solutions/Checks_FermatBelyiDifferentAccounting.lean'
own = [helper, source, checks]
authored_paths = [helper, source]
fresh_paths = authored_paths
sol = u + 'Solution_belyiActualFieldDifferentAccounting.lean'
closed_source_name = 'closedDifferentAccountingSource'
ENV = '0df444a360eaa60ab8c11dca51a86af692955474'
ROOT = 'e33ff731-60a7-43ef-87ae-c12aeba23cb5'
STANDARD = {'propext', 'Classical.choice', 'Quot.sound'}
EXPECTED_BEFORE = {'accepted_reductions': 36, 'published_children': 83,
    'dependency_edges': 101, 'open_frontier': 18, 'direct_closed_children': 40}
EXPECTED_AFTER = {'accepted_reductions': 36, 'published_children': 83,
    'dependency_edges': 101, 'open_frontier': 17, 'direct_closed_children': 41}
PRIOR = w / '.local/adaptation/conductor-extension-split-20261114'


def read(name):
    return json.loads((b / name).read_text())


def save(name, value):
    (b / name).write_text(json.dumps(value, ensure_ascii=False, indent=2) + '\n')


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def module(path):
    return path[:-5].replace('/', '.')


def graph():
    return [json.loads(line) for line in (b / 'decl_graph.jsonl').read_text().splitlines()
            if line.strip()]


def syntax(path, name):
    rows = [z for z in read('syntax-boundaries.json') if z['file'] == path
            and z['nameText'] == name.split('.')[-1]]
    assert len(rows) == 1, (path, name, len(rows))
    return rows[0]


def declaration_start(span):
    start = span['declStart']['offset']
    doc = span.get('docstring')
    if doc and doc['start']['offset'] == start:
        start = doc['end']['offset']
    return start


def header(path, name, replacement=None):
    """Only compiler-parser bytes provide theorem headers, never pretty printing."""
    raw = (w / path).read_bytes()
    span = syntax(path, name)
    ns, ne = span['nameRange']['start']['offset'], span['nameRange']['end']['offset']
    assert raw[ns:ne].decode() == name.split('.')[-1]
    replacement = raw[ns:ne] if replacement is None else replacement.encode()
    return (raw[declaration_start(span):ns] + replacement +
            raw[ne:span['valStart']['offset']]).decode().strip()


def one_decl(path, name):
    hits = [z for z in graph() if z['module'] == module(path)
            and z['userName'] == name and z['startLine'] > 0]
    assert len(hits) == 1, (path, name, len(hits))
    return hits[0]


def binding(row, path):
    return {'declaration': row['name'], 'userName': row['userName'], 'path': path,
        'module': row['module'], 'source_sha256': sha(w / path),
        'compiler_type': row['elaboratedType'],
        'source_span': {'start_line': row['startLine'], 'end_line': row['endLine']},
        'compiler_parser_span': syntax(path, row['userName'])}


def reached_from(roots):
    index = {z['name']: z for z in graph()}
    reached, todo = set(), list(roots)
    while todo:
        name = todo.pop()
        if name in reached:
            continue
        reached.add(name)
        row = index.get(name)
        if row:
            todo += row['typeDeps'] + row['valueDeps']
    return reached


def split_imports(code):
    imports, rest = [], []
    for line in code.splitlines(keepends=True):
        if line.startswith('import '):
            imports.append(line.strip())
        else:
            rest.append(line)
    return imports, ''.join(rest).strip()


def pruned_module(path, retained):
    """Remove complete unused declaration commands; retain namespace/variables."""
    raw = (w / path).read_bytes()
    removed = []
    for row in graph():
        if row['module'] != module(path) or row['startLine'] <= 0 or row['name'] in retained:
            continue
        span = syntax(path, row['userName'])
        command = span.get('cmdStart')
        start = command['start']['offset'] if command else span['declStart']['offset']
        doc = span.get('docstring')
        if doc:
            start = min(start, doc['start']['offset'])
        end = span.get('cmdEnd', span['declEnd'])['offset']
        assert 0 <= start < end <= len(raw)
        removed.append((start, end, row['name']))
    ordered = sorted(removed)
    assert all(a[1] <= c[0] for a, c in zip(ordered, ordered[1:]))
    for start, end, _ in reversed(ordered):
        raw = raw[:start] + raw[end:]
    return raw.decode(), [{'start': a, 'end': c, 'name': n} for a, c, n in ordered]


def write_source(path, text):
    (w / path).write_text(text.rstrip() + '\n')


def checked(tag, path, review=False, artifact=False):
    z = read(tag + '-result.json')
    q, rs = z['request'], z['result']
    assert z['status'] == 'succeeded' and rs['exit_code'] == 0, tag
    assert q['language'] == 'lean' and q['workspace'] == str(w) and q['exclusive'] is True, tag
    parameters = {'args': [path, '-o', '.lake/build/lib/lean/' + path[:-5] + '.olean']} if artifact else {'source': path}
    assert q['parameters'] == parameters, tag
    assert q['target'] == ('module' if artifact else 'file'), tag
    assert q['task_type'] == ('full' if artifact else 'review' if review else 'leaf'), tag
    assert q['worktree_manifest']['source_sha256'] == sha(w / path), tag
    assert rs['actual_arguments'] == (['lean'] + parameters['args'] if artifact else ['lean', path]), tag
    assert rs['snapshot']['workspace_mode'] == 'exclusive_worktree' and rs['snapshot']['snapshot_id'] is None, tag
    if review:
        assert rs['review']['passed'], tag
    resources = z.get('resources', {})
    rss = resources.get('peak_rss_bytes')
    assert rss is None or rss <= 16 * 1024**3, tag
    cpu, user, system = [resources.get(k) for k in ['cpu_time_seconds', 'cpu_user_seconds', 'cpu_system_seconds']]
    if None not in [cpu, user, system]:
        assert math.isclose(cpu, user + system, abs_tol=0.1), tag
    return z


def prose(rows):
    return '\n\n'.join('**' + title + '**\n\n' + '\n\n'.join(
        '`' + z['userName'] + '`\n\n' + z[key] for z in rows)
        for key, title in [('en', 'English'), ('zh_Hans', '简体中文'), ('ja', '日本語')])


def verification(protocol, tag, ident, path, explanation):
    intent, receipt = b / (tag + '-verification-requested.json'), b / (tag + '-verify-submit.json')
    request = {'theorem_id': ident, 'proof_type': 'prove', 'file': path,
        'source_sha256': sha(w / path), 'explanation': explanation}
    if intent.exists():
        assert read(intent.name) == request
        assert receipt.exists(), 'Verification outcome unknown: reconcile original submission before retry'
    else:
        assert not receipt.exists()
        save(intent.name, request)
    if receipt.exists():
        assert read(tag + '-verify-request.json') == request
    result = protocol['verify'](tag, ident, path, explanation)
    assert result.get('id') == read(tag + '-verify-submit.json')['submission_id']
    return result


def summary_without_direct_proof_nodes(graph_input, direct_ids):
    """The established summary counts reductions with mathematical dependencies."""
    sys.path.insert(0, str(w / '.local/adaptation/northcott-sourceproof-20261114'))
    from delivery_common import graph_summary
    math_ids = {z['theorem_id'] for z in graph_input['nodes']
                if z['node_type'] == 'theorem' and z['status'] != 'Definition'}
    omitted = set()
    for node in graph_input['nodes']:
        if node['node_type'] != 'sketch' or node['submission_id'] not in direct_ids:
            continue
        assert node['status'] == 'ACCEPTED'
        actual = {e['source'] for e in graph_input['edges'] if e['kind'] == 'sketch'
                  and e['target'] == node['node_id'] and e['source'] in math_ids}
        assert actual == set(), ('Direct proof unexpectedly has mathematical imports', node['submission_id'])
        omitted.add(node['node_id'])
    filtered = graph_input | {
        'nodes': [z for z in graph_input['nodes'] if z.get('node_id') not in omitted],
        'edges': [z for z in graph_input['edges'] if z['source'] not in omitted and z['target'] not in omitted]}
    return graph_summary(filtered)


def authored_rows():
    rows = [z for z in graph() if z['module'] in {module(p) for p in authored_paths}
            and z['startLine'] > 0]
    assert len(rows) == len({z['name'] for z in rows}) == 9
    for path in authored_paths:
        parsed = [z for z in read('syntax-boundaries.json') if z['file'] == path]
        compiled = [z for z in rows if z['module'] == module(path)]
        assert len(parsed) == len(compiled)
        assert {z['nameText'] for z in parsed} == {z['userName'].split('.')[-1] for z in compiled}
    return rows


def bind():
    packet = read('blind-readbacks-source.json')
    assert packet.get('terminology_revision'), 'Confirmed terminology provenance missing'
    compiled = authored_rows()
    rows = packet['declarations']
    assert len(rows) == 9
    out = []
    for row in rows:
        path, name = row['source_relative_path'], row['logical_qualified_name']
        assert path in authored_paths
        original = Path(row['source_path'])
        assert sha(original) == row['source_sha256']
        data = original.read_bytes()[row['source_span']['start_byte']:row['source_span']['end_byte_exclusive']]
        assert data.decode() == row['raw_declaration']
        assert hashlib.sha256(data).hexdigest() == row['raw_declaration_sha256']
        z = one_decl(path, name)
        assert '【译名待定：DIFFERENT-IDEAL】' not in row['readback']['zh-Hans']
        out.append(binding(z, path) | {
            'raw_signature': header(path, name), 'original_raw_signature': row['raw_signature'],
            'original_blind_row': row, 'original_packet': 'blind-readbacks-source.json',
            'original_packet_sha256': sha(b / 'blind-readbacks-source.json'),
            'blind_original_path': str(original), 'blind_original_sha256': row['source_sha256'],
            'en': row['readback']['en'], 'zh_Hans': row['readback']['zh-Hans'], 'ja': row['readback']['ja'],
            'proof_notes': row.get('proof_notes'), 'quotation': None})
    assert {z['declaration'] for z in out} == {z['name'] for z in compiled}
    old = next(z for z in json.loads((PRIOR / 'final-readbacks.json').read_text())['declarations']
               if z['userName'] == target)
    row = next(z for z in out if z['userName'] == target)
    baseline = next(z for z in read('root-graph-before.json')['nodes'] if z.get('theorem_name') == target)
    before = read('platform-before-parent.json')
    assert baseline['theorem_id'] == before['theorem_id'] == PARENT_ID
    assert baseline['formal_statement'] == before['formal_statement']
    row.update(reused_parent_meaning={k: old[k] for k in ['en', 'zh_Hans', 'ja']},
        reused_from=str((PRIOR / 'final-readbacks.json').relative_to(w)),
        reused_packet_sha256=sha(PRIOR / 'final-readbacks.json'),
        historical_platform_formal_statement=before['formal_statement'])
    audit_path = b / 'compiler-readback-type-review.json'
    if audit_path.exists():
        audit = read(audit_path.name)
        assert audit['passed'] and audit['compiler_evidence']['graph_sha256'] == sha(b / 'decl_graph.jsonl')
        by_name = {z['declaration']: z for z in out}
        for review in audit['declarations']:
            if review.get('corrected_trilingual_statement'):
                entry = by_name[review['compiler_name']]
                entry['superseded_blind_statements'] = {k: entry[k] for k in ['en', 'zh_Hans', 'ja']}
                entry.update(review['corrected_trilingual_statement'])
                entry['compiler_readback_correction'] = audit_path.name
    save('final-readbacks.json', {'declarations': out, 'blind_readback': True,
        'compiler_bound': True, 'quotations_separate': True, 'fresh_binder_review_count': 9,
        'terminology_revision': packet['terminology_revision']})


def generate():
    bind()
    rows = authored_rows()
    reached = reached_from([target])
    assert {z['name'] for z in rows} <= reached
    retained = {z['name'] for z in rows if z['module'] == module(helper) and z['name'] in reached}
    code, removals = pruned_module(helper, retained)
    imports, body = split_imports(code)
    assert all(x.startswith('import Definitions.') for x in imports)
    wrapper = (w / source).read_bytes()
    span = syntax(source, target)
    ns, ne = span['nameRange']['start']['offset'], span['nameRange']['end']['offset']
    assert wrapper[ns:ne].decode() == target.removeprefix(pre)
    wrapper = (wrapper[:ns] + closed_source_name.encode() + wrapper[ne:]).decode()
    wrapper_imports, wrapper_body = split_imports(wrapper)
    for line in wrapper_imports:
        if line == 'import ' + module(helper):
            continue
        assert line.startswith('import Definitions.'), line
        if line not in imports:
            imports.append(line)
    formal = read('platform-before-parent.json')['formal_statement']
    assert formal.startswith('theorem ' + target + ' : ') and formal.endswith(' := by sorry')
    exact = formal.replace('theorem ' + target, 'theorem solution', 1).removesuffix(' := by sorry')
    standalone = '\n'.join(imports) + '\n\n' + body + '\n\n' + wrapper_body
    standalone += '\n\nopen AbcAdaptation\nopen ' + pre.rstrip('.') + '\n\n'
    standalone += exact + ' := ' + closed_source_name + '\n'
    assert 'sorry' not in standalone and 'import Solutions.' not in standalone and 'import Theorems.' not in standalone
    assert standalone.count('theorem solution ') == 1
    write_source(sol, standalone)
    audit = 'import Lean\n' + standalone
    original = formal.replace('theorem ' + target, 'theorem PlatformOriginalTargetType', 1).removesuffix(' := by sorry')
    audit += '\n' + original + ' := solution\n'
    audit += '\n' + header(source, target, 'PlatformSourceTargetType') + ' := solution\n'
    audit += '''
open Lean
run_meta do
  let original ← getConstInfo `PlatformOriginalTargetType
  let current ← getConstInfo `PlatformSourceTargetType
  let proof ← getConstInfo `solution
  unless ← Meta.isDefEq original.type proof.type do throwError "Original platform type differs"
  unless ← Meta.isDefEq current.type proof.type do throwError "Current wrapper type differs"
  let axs ← collectAxioms `solution
  for ax in axs do
    unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
      throwError "Unexpected direct-proof axiom {ax}"
  IO.FS.writeFile "OUTPUT" (Json.pretty (Json.mkObj [
    ("original_type_equal",Json.bool true),("source_type_equal",Json.bool true),
    ("type",Json.str (← Meta.ppExpr proof.type).pretty),("axioms",toJson (axs.map toString))]))
'''.replace('OUTPUT', u + 'solution-type-axioms.json')
    write_source(u + 'AuditSolution.lean', audit)
    save('solution-source-closure.json', {'source': sol, 'source_sha256': sha(w / sol),
        'graph_sha256': sha(b / 'decl_graph.jsonl'), 'parser_sha256': sha(b / 'syntax-boundaries.json'),
        'source_hashes': {p: sha(w / p) for p in authored_paths},
        'retained_helpers': sorted(retained), 'removed_whole_commands': removals,
        'imports': imports, 'mathematical_imports': [], 'new_definitions': [], 'new_children': [],
        'source_name': closed_source_name, 'type_source': 'Exact platform statement and compiler-parser wrapper bytes.'})
    save('consumer-closure.json', {'root': target, 'declarations': sorted(z['name'] for z in rows),
                                  'all_authored_declarations_consumed': True})
    save('generated-source-hashes.json', generated_hashes())


def generated_hashes():
    return {p: sha(w / p) for p in [sol, u + 'AuditSolution.lean']}


def receipt_plan():
    plan = []
    for path in authored_paths:
        stem = Path(path).stem.removeprefix('Source_')
        for suffix in ['leaf', 'artifact']:
            plan.append((stem + '-' + suffix, path, False, suffix == 'artifact'))
    plan += [('closed-axioms-review', checks, True, False),
        ('source-graph-leaf', u + 'ExtractDifferentAccountingGraph.lean', False, False),
        ('syntax-leaf', u + 'ExtractDifferentAccountingSyntax.lean', False, False),
        ('all-constants-review', u + 'AuditAllConstants.lean', True, False),
        ('solution-leaf', sol, False, False),
        ('types-leaf', u + 'AuditSolution.lean', False, False),
        ('production-gates-review', u + 'ProductionGates.lean', True, False),
        ('consumer-review', u + 'ChecksDifferentAccountingConsumer.lean', True, False)]
    return plan


def preflight():
    jobs = [checked(*entry) for entry in receipt_plan()]
    for receipt in jobs:
        rs = receipt['result']
        assert 'sorryAx' not in rs.get('stdout', '') + rs.get('stderr', '')
    for tag in ['source-graph-leaf', 'syntax-leaf', 'all-constants-review', 'production-gates-review']:
        hashes = read(tag + '-result.json')['request']['worktree_manifest']['input_hashes']
        assert all(hashes[p] == sha(w / p) for p in authored_paths)
    hashes = read('production-gates-review-result.json')['request']['worktree_manifest']['input_hashes']
    assert all(hashes[p] == sha(w / p) for p in own)
    imports = {line.removeprefix('import ') for line in (b / 'ProductionGates.lean').read_text().splitlines()
               if line.startswith('import ')}
    assert imports == {'ArithmeticTeichmullerSpaces.Prologue.Audit.ImportAudit',
        'ArithmeticTeichmullerSpaces.Act1Scene1', 'ArithmeticTeichmullerSpaces.Prologue.Audit.AxiomAudit'}
    rows = authored_rows()
    axs = {z['name']: z for z in read('all-module-axioms.json')}
    expected = {z['name'] for z in graph() if z['module'] in {module(p) for p in authored_paths}}
    assert expected <= set(axs) and all(set(axs[n]['axioms']) <= STANDARD for n in expected)
    audit = read('solution-type-axioms.json')
    assert audit['original_type_equal'] and audit['source_type_equal'] and set(audit['axioms']) <= STANDARD
    rb = read('final-readbacks.json')['declarations']
    assert len(rb) == 9 and {z['declaration'] for z in rb} == {z['name'] for z in rows}
    assert all(z['source_sha256'] == sha(w / z['path']) for z in rb)
    review = read('compiler-readback-type-review.json')
    assert review['passed'] and review['compiler_evidence']['graph_sha256'] == sha(b / 'decl_graph.jsonl')
    assert len(review['declarations']) == 9
    assert {z['compiler_name'] for z in review['declarations']} == {z['name'] for z in rows}
    assert {z['path']: z['sha256'] for z in review['original_packets']} == {
        'blind-readbacks-source.json': sha(b / 'blind-readbacks-source.json')}
    by_name = {z['declaration']: z for z in rb}
    for z in review['declarations']:
        original = by_name[z['compiler_name']]
        assert z['passed'] and z['compiler_type'] == original['compiler_type']
        assert z['current_source']['sha256'] == original['source_sha256']
        if z.get('corrected_trilingual_statement'):
            assert all(original[k] == z['corrected_trilingual_statement'][k] for k in ['en', 'zh_Hans', 'ja'])
    closure = read('solution-source-closure.json')
    assert closure['source_sha256'] == sha(w / sol) and closure['graph_sha256'] == sha(b / 'decl_graph.jsonl')
    assert closure['parser_sha256'] == sha(b / 'syntax-boundaries.json')
    assert all(closure['source_hashes'][p] == sha(w / p) for p in authored_paths)
    assert closure['mathematical_imports'] == [] and closure['new_definitions'] == closure['new_children'] == []
    assert read('consumer-closure.json')['all_authored_declarations_consumed']
    assert {z['name'] for z in rows} <= reached_from([target])
    solution = (w / sol).read_text()
    assert 'sorry' not in solution and 'import Theorems.' not in solution and 'import Solutions.' not in solution
    assert generated_hashes() == read('generated-source-hashes.json')
    consumer = read('consumer-config.json')
    assert consumer['source'] == u + 'ChecksDifferentAccountingConsumer.lean'
    assert consumer['ci_tag'] == 'consumer-review' and consumer['review'] is True and consumer['expected_sorryAx'] is False
    assert consumer['parent_still_open_expected'] is True
    assert consumer['actual_consumer'] == pre + 'belyiActualFieldConductorExtension_of_local_and_accounting'
    assert consumer['root_consumer'] == pre + 'canonicalEstimate_of_belyi_children'
    assert consumer['explicit_remaining_child'] == 'BelyiActualFieldLocalConductorComparison'
    assert consumer['actual_closed_child'] == target
    assert consumer['source_path'] == 'Definitions/Def_FermatCanonicalBelyiComposition.lean'
    assert consumer['source_sha256'] == sha(w / consumer['source_path'])
    consumer_text = (w / consumer['source']).read_text()
    assert 'import ' + module(source) in consumer_text
    assert 'BelyiActualFieldLocalConductorComparison' in consumer_text
    assert 'belyiActualFieldConductorExtension_of_local_and_accounting' in consumer_text
    assert 'belyiDifferentConductorComparison_of_exact_children' in consumer_text
    assert 'canonicalEstimate_of_belyi_children' in consumer_text
    assert '(belyiActualFieldConductorExtension_of_local_and_accounting hLocal belyiActualFieldDifferentAccounting)' in consumer_text
    for name in ['belyiActualFieldLocalConductorComparison', 'belyiActualFieldConductorExtension', 'belyiDifferentConductorComparison']:
        assert 'import Theorems.Thm_' + (pre + name).replace('.', '_') not in consumer_text
    consumer_hashes = read('consumer-review-result.json')['request']['worktree_manifest']['input_hashes']
    assert all(consumer_hashes[p] == sha(w / p) for p in authored_paths + [consumer['source_path']])
    sc = read('source-consumer.json')['declarations']
    assert {z['declaration'] for z in sc} == {z['name'] for z in rows}
    independent = read('independent-delivery-review.json')
    assert independent['passed'] and independent['blockers'] == []
    assert independent['source_ledger_passed'] and independent['all_new_outputs_have_actual_consumers']
    assert independent['source_ledger_sha256'] == sha(r / 'ArithmeticTeichmullerSpaces/SOURCE_LEDGER.md')
    assert independent['generated_source_hashes'] == generated_hashes()
    assert {z['job_id'] for z in jobs} <= set(independent['compiler_checks'])
    subprocess.run(['git', 'diff', '--check'], cwd=r, check=True)
    validation = {'passed': True, 'original_platform_type_equal': True, 'source_type_equal': True,
        'readbacks': 9, 'fresh_compiler_binder_reviews': 9,
        'owned_source_hashes': {p: sha(w / p) for p in own},
        'generated_source_hashes': generated_hashes(), 'compiler_checks': [z['job_id'] for z in jobs],
        'new_definitions': [], 'new_children': [], 'new_open_debt': 0,
        'independent_delivery_review_sha256': sha(b / 'independent-delivery-review.json')}
    save('delivery-validation.json', validation)
    evidence = [tag + '-result.json' for tag, _, _, _ in receipt_plan()] + [
        'decl_graph.jsonl', 'syntax-boundaries.json', 'all-module-axioms.json', 'solution-type-axioms.json',
        'blind-readbacks-source.json', 'blind-readbacks-original.json', 'final-readbacks.json',
        'compiler-readback-type-review.json', 'independent-delivery-review.json',
        'consumer-closure.json', 'consumer-config.json', 'source-consumer.json',
        'solution-source-closure.json', 'generated-source-hashes.json', 'delivery-validation.json']
    return {'validation': validation, 'owned_sources': own, 'required_jobs': jobs, 'required_evidence': evidence}


def load_verify_protocol():
    spec = importlib.util.spec_from_file_location('api', w / '.local/abc-item/api.py')
    api = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(api)
    assert api.base == 'https://prove2.me/api/v1'
    context = {key: value for key, value in globals().items() if key != 'publish'} | {'api': api}
    path = w / '.local/adaptation/platform-tripod-20261113/executed-platform-publish.py'
    nodes = [n for n in ast.parse(path.read_text()).body if isinstance(n, ast.FunctionDef) and n.name == 'verify']
    assert len(nodes) == 1
    exec(compile(ast.Module(body=nodes, type_ignores=[]), '<established-verify-only>', 'exec'), context)
    assert 'publish' not in context
    return api, context


def publish():
    preflight()
    api, protocol = load_verify_protocol()
    before = read('platform-before-parent.json')
    assert before['theorem_id'] == PARENT_ID and before['theorem_name'] == target
    assert before['visibility'] == 'private' and before['mathlib_rev'] == ENV and before['status'] == 'Open'
    current = api.request('/theorems/' + PARENT_ID)
    assert current['formal_statement'] == before['formal_statement'] and current['preamble'] == before['preamble']
    baseline = read('root-graph-before.json')
    assert baseline['mathematical_closure_complete'] and read('registry-before.json')['graph_counts'] == EXPECTED_BEFORE
    quote = (b / 'quotation.md').read_text().strip()
    description = (b / 'source-description.txt').read_text().strip()
    selected = [z for z in read('final-readbacks.json')['declarations'] if z['userName'] == target]
    assert quote and description and len(selected) == 1
    explanation = quote + '\n\n' + prose(selected) + '\n\n' + description
    explanation += '\n\nThe source proof factors the actual nonzero relative different ideal into its prime-power factors and takes logarithms of absolute norms. It groups the normalized terms by the actual prime below each prime of the full point field. The support lies in the finite image of the different ideal prime support. This proves both finite support and the exact grouped identity, with the full point-field degree in the denominator and the original actual image-field inclusion. The standalone proof imports only existing Definitions and has no mathematical theorem imports. This closes the unchanged accounting child; the separate local conductor child and its parent estimates remain Open.'
    assert len(explanation) <= 50000
    result = verification(protocol, verify_tag, PARENT_ID, sol, explanation)
    assert result['status'] == 'ACCEPTED'
    patch = {'natural_language_statement': quote + '\n\n' + prose(selected), 'source': description}
    save('parent-metadata-patch-request.json', patch)
    current = api.request('/theorems/' + PARENT_ID)
    assert current['formal_statement'] == before['formal_statement'] and current['preamble'] == before['preamble']
    if not all(current.get(k) == v for k, v in patch.items()):
        save('parent-metadata-patch-response.json', api.request('/theorems/' + PARENT_ID, patch, 'PATCH'))
    state = api.request('/theorems/' + PARENT_ID)
    assert state['status'] == 'Proved' and state['visibility'] == 'private' and state['mathlib_rev'] == ENV
    assert state['formal_statement'] == before['formal_statement'] and state['preamble'] == before['preamble']
    assert all(state.get(k) == v for k, v in patch.items())
    save('platform-after-parent.json', state)
    sys.path.insert(0, str(w / '.local/adaptation/northcott-sourceproof-20261114'))
    from graph_completion import fetch_complete_math_graph
    after = fetch_complete_math_graph(api, ROOT, save, 'root-graph-after')
    save('root-graph-after.json', after)
    leaves = []
    while True:
        page = api.request('/theorems/' + ROOT + '/open-leaves?limit=50&offset=' + str(len(leaves)))
        save('root-frontier-after-page-' + str(len(leaves)) + '.json', page)
        leaves += page['open_leaves']
        if len(leaves) >= page['total']:
            break
    assert len(leaves) == page['total']
    save('root-frontier-after.json', {'open_leaves': leaves, 'total': page['total'], 'all_pages_fetched': True})
    old = {z['theorem_id'] for z in baseline['nodes'] if z.get('status') == 'Definition'}
    new = {z['theorem_id'] for z in after['nodes'] if z.get('status') == 'Definition'}
    save('definition-retention-readbacks.json', {'definitions': [api.request('/theorems/' + ident)
         for ident in sorted(old ^ new)]})
    verify_graph(baseline, after, result)
    print('Exact different-accounting source proof ACCEPTED; frontier 18 -> 17; local conductor child remains Open.', flush=True)


def retained_definitions(before, after):
    old = {z['theorem_id']: z for z in before['nodes'] if z.get('status') == 'Definition'}
    current = {z['theorem_id']: z for z in after['nodes'] if z.get('status') == 'Definition'}
    baseline = {z['theorem_id']: z for z in read('definition-baseline-readbacks.json')['definitions']}
    changes = set(old) ^ set(current)
    rows = read('definition-retention-readbacks.json')['definitions']
    actual = {z['theorem_id']: z for z in rows}
    assert len(actual) == len(rows) and set(actual) == changes
    for ident in set(old) | set(current):
        previous = old[ident] if ident in old else baseline[ident]
        row = current[ident] if ident in current else actual[ident]
        assert previous['theorem_id'] == row['theorem_id'] == ident
        assert previous['theorem_name'] == row['theorem_name']
        assert previous['status'] == row['status'] == 'Definition'
        assert previous['formal_statement'] == row['formal_statement']
        assert definition_code(previous) == definition_code(row)
        assert not row.get('deprecated_at')
        if ident in changes:
            get_row = actual[ident]
            assert get_row['theorem_name'] == previous['theorem_name'] and get_row['status'] == 'Definition'
            assert get_row['visibility'] == 'private' and get_row['mathlib_rev'] == ENV
            assert get_row['formal_statement'] == previous['formal_statement']
            assert definition_code(get_row) == definition_code(previous)
        if ident not in old:
            assert previous['visibility'] == 'private' and previous['mathlib_rev'] == ENV
            # A pre-submission GET proves that a newly visible graph Definition
            # already existed. Its presence is not a new publication by this unit.
            assert previous['created_at'] == row['created_at']
    return {'new_published_definitions': [], 'hidden_old_ids': sorted(set(old) - set(current)),
        'reappeared_preexisting_ids': sorted(set(current) - set(old)),
        'baseline_readbacks_sha256': sha(b / 'definition-baseline-readbacks.json'),
        'retention_readbacks_sha256': sha(b / 'definition-retention-readbacks.json')}


def verify_graph(before, after, result):
    assert result['status'] == 'ACCEPTED' and result['theorem_id'] == PARENT_ID
    old = summary_without_direct_proof_nodes(before, set())
    new = summary_without_direct_proof_nodes(after, {result['id']})
    old_nodes = {z['theorem_name']: z for z in before['nodes'] if z['node_type'] == 'theorem' and z['status'] != 'Definition'}
    current = {z['theorem_name']: z for z in after['nodes'] if z['node_type'] == 'theorem' and z['status'] != 'Definition'}
    assert set(old_nodes) == set(current)
    for name, previous in old_nodes.items():
        row = current[name]
        assert row['theorem_id'] == previous['theorem_id'] and row['formal_statement'] == previous['formal_statement']
        assert row['status'] == ('Proved' if name == target else previous['status'])
        assert not row.get('deprecated_at')
    assert old_nodes[target]['status'] == 'Open' and current[target]['theorem_id'] == PARENT_ID
    for name in ['belyiActualFieldLocalConductorComparison', 'belyiActualFieldConductorExtension', 'belyiDifferentConductorComparison']:
        assert current[pre + name]['status'] == 'Open'
    assert current['AbcAdaptation.Tripod.Fermat.canonicalEstimate']['status'] == 'Open'
    assert current['abc.goal.lt_constant_mul_fix']['status'] == 'Open'
    old_reductions = {z['submission_id']: z for z in old['reductions']}
    new_reductions = {z['submission_id']: z for z in new['reductions']}
    assert old_reductions == new_reductions
    assert old['dependency_pairs'] == new['dependency_pairs']
    for summary, expected in [(old, EXPECTED_BEFORE), (new, EXPECTED_AFTER)]:
        assert summary['counts'] == {k: expected[k] for k in ['accepted_reductions', 'published_children', 'dependency_edges']}
    bf, af = read('root-frontier-before.json'), read('root-frontier-after.json')
    for frontier, expected in [(bf, EXPECTED_BEFORE), (af, EXPECTED_AFTER)]:
        assert frontier['all_pages_fetched'] and frontier['total'] == expected['open_frontier']
        assert len(frontier['open_leaves']) == len({z['theorem_id'] for z in frontier['open_leaves']}) == frontier['total']
    assert {z['theorem_id'] for z in af['open_leaves']} == {z['theorem_id'] for z in bf['open_leaves']} - {PARENT_ID}
    direct = {z['name'] for z in read('registry-before.json')['direct_closed_proofs']}
    assert len(direct) == 40 and target not in direct
    assert all(current[name]['status'] == 'Proved' for name in direct | {target})
    retention = retained_definitions(before, after)
    proof = {'name': target, 'submission_id': result['id'], 'status': 'ACCEPTED', 'mathematical_dependencies': []}
    save('direct-graph-evidence.json', {'target_id': PARENT_ID, 'submission_id': result['id'],
        'actual_child_ids': [], 'new_reductions': [], 'target': 'Proved', 'root': 'Open'})
    save('graph-count-evidence.json', {'before': EXPECTED_BEFORE, 'after': EXPECTED_AFTER,
        'direct_closed_proof': proof, 'new_nodes': [], 'new_reductions': [], 'new_dependencies': [],
        'definition_retention': retention, 'existing_nodes_preserved': True,
        'existing_reductions_preserved': True, 'changed_statuses': [target],
        'deprecations': [], 'Fermat_route_preserved': True, 'target': 'Proved',
        'local_conductor_child': 'Open', 'extension': 'Open', 'comparison': 'Open',
        'canonicalEstimate': 'Open', 'root': 'Open'})


def definition_code(row):
    values = [row[key] for key in ['definition', 'definitions'] if row.get(key)]
    assert values, ('Definition record has no nonempty source code', row.get('theorem_id'))
    assert all(value == values[0] for value in values)
    return values[0]


if __name__ == '__main__':
    {'bind': bind, 'generate': generate, 'preflight': preflight, 'publish': publish}[sys.argv[1]]()
