"""Main-agent-only divisor-degree delivery tool. No import-time side effects.

Generate local evidence with generate, compile only through MCP-CI,
then run preflight/publish after reviewing the independent receipts.
"""
from pathlib import Path
import ast
import hashlib
import importlib.util
import json
import subprocess
import sys
import time
import urllib.error
import urllib.request
import uuid

r = Path('/home/admin-wsl/Coq/abc')
w = r / 'prove2me_workspace'
u = '.local/adaptation/divisor-degree-height-sourceproof-20261114/'
b = w / u
prior = w / '.local/adaptation/polar-presentation-height-sourceproof-20261114'
pre = 'AbcAdaptation.Tripod.Fermat.Proper.'
short = 'divisorDegreeHeightComparison'
target = pre + short
source = 'Theorems/Thm_' + target.replace('.', '_') + '.lean'
old_names = ['FermatPolarAbsoluteExtension', 'FermatPolarAbsoluteBasic',
             'FermatPolarPointAdapters', 'FermatPolarTupleHeight',
             'FermatPolarMinOrd', 'FermatPolarRootBound',
             'FermatPolarIntegrality', 'FermatPolarPresentationHeights']
new_names = ['FermatDivisorTupleEquivalence', 'FermatPositiveDegreePolar',
             'FermatDivisorHeightMachine', 'FermatDivisorDegreeHeightComparison']
helper_names = old_names + new_names
helpers = ['Solutions/Source_' + n + '.lean' for n in helper_names]
old_helpers, new_helpers = helpers[:8], helpers[8:]
checks = 'Solutions/Checks_FermatDivisorDegreeHeightComparison.lean'
sol = u + 'Solution_' + short + '.lean'
ENV = '0df444a360eaa60ab8c11dca51a86af692955474'
ROOT = 'e33ff731-60a7-43ef-87ae-c12aeba23cb5'
STANDARD = {'propext', 'Classical.choice', 'Quot.sound'}
PACKETS = ['blind-readbacks-source.json']
TARGET_PACKET = w / '.local/adaptation/readbacks/fermat-proper-canonical-v1/result.json'

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

def prose(rows):
    return '\n\n'.join('**' + title + '**\n\n' + '\n\n'.join('`' + z['userName'] + '`\n\n' + z[lang] for z in rows)
                         for lang, title in [('en', 'English'), ('zh_Hans', '简体中文'), ('ja', '日本語')])

def one_decl(path, user_name):
    hits = [z for z in graph() if z['module'] == module(path)
            and z['userName'] == user_name and z['startLine'] > 0]
    assert len(hits) == 1, (path, user_name, len(hits))
    return hits[0]


def binding(z, path):
    return {'declaration': z['name'], 'userName': z['userName'], 'path': path,
            'module': z['module'], 'source_sha256': sha(w / path),
            'compiler_type': z['elaboratedType'],
            'source_span': {'start_line': z['startLine'], 'end_line': z['endLine']},
            'compiler_parser_span': syntax(path, z['userName'])}


def bind():
    old_packet = prior / 'final-readbacks.json'
    old_audit_path = prior / 'compiler-readback-type-review.json'
    old_audit = json.loads(old_audit_path.read_text())
    assert old_audit['passed']
    old_rows = [z for z in json.loads(old_packet.read_text())['declarations'] if z['path'] in old_helpers]
    audits = {z['compiler_name']: z for z in old_audit['declarations']}
    assert len(old_rows) == len(audits) == 121
    out, reused_audits = [], []
    for old in old_rows:
        path = old['path']
        z = one_decl(path, old['userName'])
        assert old['source_sha256'] == sha(w / path), ('Changed old source', path)
        assert old['compiler_type'] == z['elaboratedType'], ('Changed old type', z['name'])
        audit = audits[old['declaration']]
        assert audit['passed'] and audit['compiler_type'] == z['elaboratedType']
        assert audit['current_source']['sha256'] == sha(w / path)
        assert audit.get('userName', old['userName']) == z['userName']
        assert audit.get('module', module(path)) == z['module']
        # Compiler names of private declarations are rebound by original userName;
        # the exact current module, source bytes and elaborated type must match.
        out.append(old | binding(z, path) | {
            'reused_from': str(old_packet.relative_to(w)), 'reused_packet_sha256': sha(old_packet),
            'reused_compiler_name': old['declaration'],
            'reuse_basis': 'Same module + original userName; identical current source hash and compiler type.',
            'retained_binder_review': 'Reused exact type/source audit; recorded in reused-compiler-readback-type-review.json'})
        reused_audits.append(audit | {'compiler_name': z['name'], 'reused_compiler_name': old['declaration']})
    packet_name = 'blind-readbacks-source.json'
    packet = read(packet_name)
    rows = packet['readbacks']
    assert len(rows) == 23
    for row in rows:
        original = Path(row['source_path'])
        assert sha(original) == row['source_sha256'], original
        path = 'Solutions/' + original.name
        assert path in new_helpers
        name = row['logical_qualified_name']
        z = one_decl(path, name)
        actual_header = header(path, name)
        adaptation = None
        if not actual_header.endswith(row['raw_signature'].strip()):
            # This one helper needed its Model-derived instance in the conclusion
            # before elaboration. Preserve the blind signature and require the
            # new compiler-type audit; do not represent it as byte-identical.
            assert name == pre + 'suppliedPresentationHeight_approx_chosen', name
            insertion = '\n    letI : IsCurveField M.K := M.isCurveField'
            assert actual_header.count(insertion) == 1
            assert actual_header.replace(insertion, '', 1).endswith(row['raw_signature'].strip())
            repair = read('supplied-height-instance-repair.json')
            assert repair['new_hypothesis'] is False and repair['original_target_changed'] is False
            adaptation = {'kind': 'derived_instance_in_conclusion',
                          'exact_inserted_bytes': insertion,
                          'repair_receipt': 'supplied-height-instance-repair.json',
                          'repair_receipt_sha256': sha(b / 'supplied-height-instance-repair.json'),
                          'audit_required': 'Current compiler type and retained-binder readback, among all 23 new declarations.'}
        langs = row['readback']
        out.append(binding(z, path) | {
            'raw_signature': actual_header, 'original_raw_signature': row['raw_signature'],
            'signature_adaptation': adaptation, 'original_blind_row': row,
            'original_packet': packet_name, 'original_packet_sha256': sha(b / packet_name),
            'blind_original_path': str(original), 'blind_original_sha256': row['source_sha256'],
            'original_blind_elaboration': row['inferred_compiler_parameters'],
            'elaboration': {'status': 'compiler_bound', 'compiler_qualified_name': z['name']},
            'en': langs['en'], 'zh_Hans': langs['zh-Hans'], 'ja': langs['ja'], 'quotation': None,
            'proof_notes': {'scope': 'Blind source readback is not a proof or retained-binder audit.'}})
    # The existing independent target readback is unchanged. Bind it to the new
    # compiler type; its old packet contains source meanings, not compiler types.
    old_target = json.loads(TARGET_PACKET.read_text())[target]
    before = read('platform-before-parent.json')
    old_graph = read('root-graph-before.json')
    node = next(z for z in old_graph['nodes'] if z.get('theorem_name') == target)
    assert before['formal_statement'] == node['formal_statement']
    z = one_decl(source, target)
    out.append(binding(z, source) | {
        'en': old_target['en'], 'zh_Hans': old_target['zh'], 'ja': old_target['ja'],
        'reused_from': str(TARGET_PACKET.relative_to(w)), 'reused_packet_sha256': sha(TARGET_PACKET),
        'reuse_basis': 'Independent target readback; unchanged exact platform formal statement; current compiler binding.',
        'historical_platform_formal_statement': node['formal_statement'],
        'proof_notes': {'scope': 'Original target readback retained; current body audited separately.'}, 'quotation': None})
    assert len(out) == 145 and len({z['declaration'] for z in out}) == 145
    for path in helpers:
        parsed = [z for z in read('syntax-boundaries.json') if z['file'] == path]
        bound = [z for z in out if z['path'] == path]
        assert len(parsed) == len(bound), path
        assert {z['nameText'] for z in parsed} == {z['userName'].split('.')[-1] for z in bound}, path
    audit_path = b / 'compiler-readback-type-review.json'
    if audit_path.exists():
        audit = read('compiler-readback-type-review.json')
        assert audit['passed'] and audit['compiler_evidence']['graph_sha256'] == sha(b / 'decl_graph.jsonl')
        by_name = {z['declaration']: z for z in out}
        for row in audit['declarations']:
            correction = row.get('corrected_trilingual_statement')
            if correction:
                entry = by_name[row['compiler_name']]
                entry['superseded_blind_statements'] = {lang: entry[lang] for lang in ['en', 'zh_Hans', 'ja']}
                entry.update(correction)
                entry['compiler_readback_correction'] = 'compiler-readback-type-review.json'
    save('reused-compiler-readback-type-review.json', {
        'passed': True, 'source_audit': str(old_audit_path.relative_to(w)),
        'source_audit_sha256': sha(old_audit_path), 'original_packet_sha256': sha(old_packet),
        'current_graph_sha256': sha(b / 'decl_graph.jsonl'), 'declarations': reused_audits})
    save('final-readbacks.json', {'declarations': out, 'blind_readback': True,
                                'compiler_bound': True, 'quotations_separate': True,
                                'retained_binder_review': '121 exact-source/type audits reused; fresh 23-row audit required separately.'})




def generate():
    bind()
    authored, reached, instances = closure()
    imports, bodies, removals, retained = [], [], [], []
    for path in helpers + [source]:
        raw = (w / path).read_bytes()
        edits = []
        if path == source:
            span = syntax(path, target)
            edits.append((span['nameRange']['start']['offset'], span['nameRange']['end']['offset'], b'closedDivisorHeightSource'))
        else:
            for z in [z for z in authored if z['module'] == module(path)]:
                span = syntax(path, z['userName'])
                if z['name'] in reached:
                    retained.append(z['name'])
                    continue
                start, end = span['cmdStart']['start']['offset'], span['cmdEnd']['offset']
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
                assert name.startswith(('Definitions.', 'Mathlib.', 'Theorems.')), imp
                assert name != module(source), imp
                if imp not in imports:
                    imports.append(imp)
            else:
                lines.append(line)
        bodies.append(''.join(lines).strip())
    # Platform theorem imports expose their statement, so source-used theorem constants need direct imports.
    by_name = {z['name']: z for z in graph()}
    used_theorem_modules = set()
    for declaration in graph():
        if declaration['name'] not in set(retained) | {target}:
            continue
        for dependency in declaration['typeDeps'] + declaration['valueDeps']:
            info = by_name.get(dependency)
            if info and info['module'].startswith('Theorems.') and info['module'] != module(source):
                used_theorem_modules.add(info['module'])
    for name in sorted(used_theorem_modules):
        line = 'import ' + name
        if line not in imports:
            imports.append(line)
    assert set(retained) == {z['name'] for z in authored if z['name'] in reached}
    assert instances <= reached
    exact = header(source, target, 'solution')
    assert exact == 'theorem solution : DivisorDegreeHeightComparison', exact
    code = '\n'.join(imports) + '\n\nset_option autoImplicit false\n\n' + '\n\n'.join(bodies)
    # All source namespaces have ended before the single public solution name.
    code += '\n\nopen ' + pre.rstrip('.') + '\n\n' + exact
    code += ' := by\n  exact ' + pre + 'closedDivisorHeightSource\n'
    assert 'sorry' not in code and 'import Solutions.' not in code
    assert 'import ' + module(source) not in code
    (w / sol).write_text(code)
    formal = read('platform-before-parent.json')['formal_statement']
    assert formal.startswith('theorem ' + target + ' : ') and formal.endswith(' := by sorry')
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
        'source_body_changes': 'Unused complete outer declaration commands removed; target name only renamed; lexical contexts retained.',
        'type_source': 'Compiler parser bytes; original platform statement separately audited with Meta.isDefEq.',
        'imports': imports, 'platform_theorem_imports': [p for p in imports if p.startswith('import Theorems.')],
        'no_own_target_import': True, 'no_solutions_import': True,
        'new_nodes': [], 'new_open_debt': 0})
def imported_platform_theorems():
    """Import closure for revalidation, not a claim about platform graph edges."""
    by_module = {module('Theorems/Thm_' + z['theorem_name'].replace('.', '_') + '.lean'): z
                 for z in read('root-graph-before.json')['nodes'] if z['node_type'] == 'theorem'}
    todo = [p.removeprefix('import ') for p in read('solution-source-closure.json')['imports']]
    seen, found = set(), {}
    while todo:
        name = todo.pop()
        if name in seen or name.startswith('Mathlib.'):
            continue
        seen.add(name)
        assert name.startswith(('Definitions.', 'Theorems.', 'Solutions.')), name
        path = w / (name.replace('.', '/') + '.lean')
        assert path.exists(), path
        if name.startswith('Theorems.'):
            assert name in by_module, ('Imported platform theorem absent from complete baseline graph', name)
            row = by_module[name]
            assert row['theorem_name'] != target
            found[row['theorem_id']] = {'id': row['theorem_id'], 'name': row['theorem_name'],
                                       'module': name, 'source_sha256': sha(path)}
        todo.extend(line.split()[1] for line in path.read_text().splitlines() if line.startswith('import '))
    return sorted(found.values(), key=lambda z: z['name'])


def preflight():
    jobs = []
    for name, path in zip(helper_names, helpers):
        unit = prior if path in old_helpers else b
        for suffix, artifact in [('leaf', False), ('artifact', True)]:
            # Prior successful receipts are reusable only for these unchanged bytes.
            tag = name + '-' + suffix
            if unit == prior:
                receipt = json.loads((prior / (tag + '-result.json')).read_text())
                assert receipt['request']['worktree_manifest']['source_sha256'] == sha(w / path), tag
                # checked uses current unit; validate prior evidence without copying it.
                q, rs = receipt['request'], receipt['result']
                expected = {'args': [path, '-o', '.lake/build/lib/lean/' + path[:-5] + '.olean']} if artifact else {'source': path}
                assert receipt['status'] == 'succeeded' and rs['exit_code'] == 0
                assert q['workspace'] == str(w) and q['exclusive'] and q['parameters'] == expected
                assert q['task_type'] == ('full' if artifact else 'leaf')
                assert rs['actual_arguments'] == (['lean'] + expected['args'] if artifact else ['lean', path])
                assert rs['snapshot']['workspace_mode'] == 'exclusive_worktree' and rs['snapshot']['snapshot_id'] is None
                assert 'sorryAx' not in rs.get('stdout', '') + rs.get('stderr', '')
                rss = receipt.get('resources', {}).get('peak_rss_bytes')
                assert rss is None or rss <= 16 * 1024**3
                jobs.append(receipt)
            else:
                jobs.append(checked(tag, path, artifact=artifact))
    tag = 'Thm_' + target.replace('.', '_')
    jobs += [checked(tag + '-leaf', source), checked(tag + '-artifact', source, artifact=True)]
    for row in [('closed-axioms-review', checks, True),
                ('source-graph-leaf', u + 'ExtractDegreeHeightGraph.lean', False),
                ('syntax-leaf', u + 'ExtractDegreeHeightSyntax.lean', False),
                ('all-constants-review', u + 'AuditAllConstants.lean', True),
                ('direct-solution-leaf', sol, False),
                ('solution-type-axioms-review', u + 'AuditSolution.lean', True),
                ('production-gates-review', u + 'ProductionGates.lean', True),
                (read('consumer-config.json')['ci_tag'], read('consumer-config.json')['source'], True)]:
        jobs.append(checked(*row))
    axs = read('all-module-axioms.json')
    expected = {z['name'] for z in graph() if z['module'] in {module(p) for p in helpers + [source]}}
    assert expected <= {z['name'] for z in axs}
    assert all(set(z['axioms']) <= STANDARD for z in axs)
    audit = read('solution-type-axioms.json')
    assert audit['original_type_equal'] and set(audit['axioms']) <= STANDARD
    own = new_helpers + [source, checks]
    inputs = read('production-gates-review-result.json')['request']['worktree_manifest']['input_hashes']
    assert all(inputs[p] == sha(w / p) for p in helpers + [source, checks])
    for tag in ['source-graph-leaf', 'syntax-leaf']:
        inputs = read(tag + '-result.json')['request']['worktree_manifest']['input_hashes']
        assert all(inputs[p] == sha(w / p) for p in helpers + [source]), tag
    rb = read('final-readbacks.json')['declarations']
    assert len(rb) == 145 and all(z['source_sha256'] == sha(w / z['path']) for z in rb)
    bound = {z['declaration']: z for z in rb}
    binder = read('compiler-readback-type-review.json')
    assert binder['passed'] and binder['compiler_evidence']['graph_sha256'] == sha(b / 'decl_graph.jsonl')
    # Review is explicitly about all 23 new declarations, not just retained ones.
    rows = binder['declarations']
    new_bound = {z['declaration']: z for z in rb if z['path'] in new_helpers}
    assert len(rows) == 23 and {z['compiler_name'] for z in rows} == set(new_bound)
    assert {z['path']: z['sha256'] for z in binder['original_packets']} == {
        'blind-readbacks-source.json': sha(b / 'blind-readbacks-source.json')}
    for row in rows:
        z = bound[row['compiler_name']]
        assert row['passed'] and row['compiler_type'] == z['compiler_type']
        assert row['current_source']['sha256'] == z['source_sha256']
        if row.get('corrected_trilingual_statement'):
            assert all(z[lang] == row['corrected_trilingual_statement'][lang] for lang in ['en', 'zh_Hans', 'ja'])
    reused = read('reused-compiler-readback-type-review.json')
    assert reused['passed'] and len(reused['declarations']) == 121
    assert reused['current_graph_sha256'] == sha(b / 'decl_graph.jsonl')
    assert reused['source_audit_sha256'] == sha(prior / 'compiler-readback-type-review.json')
    for row in reused['declarations']:
        z = bound[row['compiler_name']]
        assert row['passed'] and row['compiler_type'] == z['compiler_type']
        assert row['current_source']['sha256'] == z['source_sha256']
    close = read('solution-source-closure.json')
    assert close['source_sha256'] == sha(w / sol) and 'sorry' not in (w / sol).read_text()
    assert close['graph_sha256'] == sha(b / 'decl_graph.jsonl') and close['parser_sha256'] == sha(b / 'syntax-boundaries.json')
    assert all(close['source_hashes'][p] == sha(w / p) for p in helpers + [source])
    review = read('independent-delivery-review.json')
    assert review['passed'] and review['solution_sha256'] == sha(w / sol)
    # The source/consumer ledger is also reviewed independently. Its receipt can
    # preserve any additional source-fidelity findings without a schema rewrite.
    assert review.get('source_ledger_passed') is True
    assert review.get('all_new_outputs_have_actual_consumers') is True
    assert review.get('source_ledger_sha256') == sha(r / 'ArithmeticTeichmullerSpaces/SOURCE_LEDGER.md')
    consumer = read('consumer-config.json')
    assert consumer['review'] and consumer['parent_still_open_expected']
    assert consumer['source_sha256'] == sha(w / consumer['source_path'])
    subprocess.run(['git', 'diff', '--check'], cwd=r, check=True)
    deps = imported_platform_theorems()
    save('imported-platform-theorems.json', {'scope': 'Import closure for private Proved revalidation; actual graph children derived after ACCEPTED.',
                                            'theorems': deps})
    save('delivery-validation.json', {'passed': True, 'original_platform_type_equal': True,
        'new_platform_nodes': [], 'new_open_debt': 0, 'readbacks': 145,
        'reused_exact_source_type_binder_audits': 121, 'fresh_binder_audits': 23,
        'compiler_checks': [z['job_id'] for z in jobs],
        'owned_source_hashes': {p: sha(w / p) for p in own},
        'reused_source_hashes': {p: sha(w / p) for p in old_helpers},
        'consumer_source_sha256': sha(w / read('consumer-config.json')['source']),
        'independent_delivery_review_sha256': sha(b / 'independent-delivery-review.json')})


def load_api():
    # The only credential store is the existing ignored file. Do not read or
    # duplicate its contents in evidence or diagnostic output.
    tracked = subprocess.run(['git', 'ls-files', '--error-unmatch', 'credentials.json'], cwd=w,
                             stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    ignored = subprocess.run(['git', 'check-ignore', '-q', 'credentials.json'], cwd=w)
    assert tracked.returncode != 0 and ignored.returncode == 0
    spec = importlib.util.spec_from_file_location('api', w / '.local/abc-item/api.py')
    api = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(api)
    assert api.base == 'https://prove2.me/api/v1'
    # Preserve the established direct opener and refuse redirects.
    text = (w / '.local/abc-item/api.py').read_text()
    assert 'ProxyHandler({})' in text and 'NoRedirect()' in text
    return api


def publish():
    preflight()
    api = load_api()
    ident = read('target-id.json')['id']
    before = read('platform-before-parent.json')
    current = api.request('/theorems/' + ident)
    assert current['formal_statement'] == before['formal_statement']
    assert current['theorem_name'] == target and current['visibility'] == 'private' and current['mathlib_rev'] == ENV
    validated = []
    for dep in read('imported-platform-theorems.json')['theorems']:
        z = api.request('/theorems/' + dep['id'])
        assert z['theorem_name'] == dep['name'] and z['status'] == 'Proved'
        assert z['visibility'] == 'private' and z['mathlib_rev'] == ENV
        validated.append({'id': dep['id'], 'name': dep['name'], 'status': z['status'],
                          'visibility': z['visibility'], 'mathlib_rev': z['mathlib_rev']})
    save('platform-imports-revalidated.json', {'passed': True, 'theorems': validated})
    context = globals() | {'api': api}
    protocol = (w / '.local/adaptation/platform-tripod-20261113/executed-platform-publish.py').read_text()
    functions = [n for n in ast.parse(protocol).body if isinstance(n, ast.FunctionDef) and n.name == 'verify']
    assert len(functions) == 1
    exec(compile(ast.Module(body=functions, type_ignores=[]), '<established-protocol>', 'exec'), context)
    rb = read('final-readbacks.json')['declarations']
    selected_names = {target, pre + 'DegreeHeightMachine.chosenHeight_le_mul', pre + 'positiveDegreePolarRealization'}
    selected = [z for z in rb if z['userName'] in selected_names]
    assert len(selected) == 3
    quote = (b / 'quotation.md').read_text().strip()
    origin = ('Shinichi Mochizuki, Arithmetic Elliptic Curves in General Position (February 2009), '
              'Proposition 1.4 and Theorem 2.1 with its proof. '
              'Official PDF https://www.kurims.kyoto-u.ac.jp/~motizuki/Arithmetic%20Elliptic%20Curves%20in%20General%20Position.pdf ; '
              'SHA256 b9dc115af61dca7fe434332ebafddf6a376a9e2926dad4e1ea2dcc0d2441f768. '
              'Paper quotations supply context; the exact strict divisor-degree comparison is a formal-source auxiliary, not a verbatim paper quotation. '
              'Source proofs: Heights 721496ca4c158e511d25d8ccf6bfe8503eda73c1, '
              'Heights/Curve/LinearEquiv.lean:61–108 and Heights/Curve/DivisorHeight.lean:112–309, '
              'with Belyi 9ce4d3f793d3bc831f2fc7214b7dbad90ea012d8, Belyi/CurveField/Riemann.lean:393–412. '
              'Existing tuple-height, integral-dependence, and local-root-bound proofs are reused with original source notices and pinned source ledger. '
              'The standalone proof retains existing private Proved Riemann/polar theorem imports; actual platform dependency edges are recorded from the complete final API graph. '
              'All 145 source/target readbacks and the retained-binder audits remain in local evidence.')
    notes = (r'For each divisor, choose a polar presentation using the already proved Riemann construction. '
             r'Tuple-height comparison for equal local minimum orders proves invariance under principal divisors and addition. '
             r'A divisor of positive degree has a positive multiple linearly equivalent to an actual polar divisor, so its chosen height is bounded below. '
             r'Given $\deg E<q\deg D$ with $\deg D>0$, choose a rational number $a/b$ strictly between $\deg E/\deg D$ and $q$, with $b>0$. '
             r'The divisor $aD-bE$ has positive degree. Its lower height bound, additivity and the multiple laws give an upper comparison for $h_E$ at coefficient $a/b$. '
             r'The lower bound for $h_D$ raises that coefficient to $q$. '
             r'Finally, compare both internally chosen heights with the two arbitrary supplied presentations. '
             r'The error from multiplying by $q$ is bounded using $|q|$, so every real $q$ remains allowed. '
             r'The result holds at every proper algebraic point, including poles, with the constant chosen independently of the point. '
             r'This closes the exact divisor comparison leaf; the canonical-estimate parent retains its other open children.')
    explanation = notes + '\n\n' + quote + '\n\n' + prose(selected) + '\n\n' + origin
    assert len(explanation) <= 50000
    tag = 'prove-' + short
    request = {'theorem_id': ident, 'proof_type': 'prove', 'file': sol,
               'source_sha256': sha(w / sol), 'explanation': explanation}
    if (b / (tag + '-verify-submit.json')).exists():
        assert read(tag + '-verify-request.json') == request
        assert sha(b / (tag + '-solution.lean')) == request['source_sha256']
    else:
        assert not (b / (tag + '-verification-requested.json')).exists(), 'Reconcile prior uncertain POST before retry'
        save(tag + '-verification-requested.json', request)
    result = context['verify'](tag, ident, sol, explanation)
    assert result['status'] == 'ACCEPTED'
    assert sha(w / sol) == request['source_sha256']
    patch = {'natural_language_statement': quote + '\n\n' + prose([z for z in rb if z['declaration'] == target]), 'source': origin}
    save('parent-metadata-patch-request.json', patch)
    current = api.request('/theorems/' + ident)
    if not all(current.get(k) == v for k, v in patch.items()):
        save('parent-metadata-patch-response.json', api.request('/theorems/' + ident, patch, 'PATCH'))
    current = api.request('/theorems/' + ident)
    assert current['status'] == 'Proved' and current['formal_statement'] == before['formal_statement']
    assert all(current[k] == v for k, v in patch.items())
    save('platform-after-parent.json', current)
    root = api.request('/theorems/' + ROOT)
    assert root['status'] == 'Open'
    save('platform-after-root.json', root)
    sys.path.insert(0, str(w / '.local/adaptation/northcott-sourceproof-20261114'))
    from graph_completion import fetch_complete_math_graph
    final_graph = fetch_complete_math_graph(api, ROOT, save, 'root-graph-after')
    assert final_graph['mathematical_closure_complete']
    save('root-graph-after.json', final_graph)
    before_graph = read('root-graph-before.json')
    mathematical = lambda g: {z['theorem_id'] for z in g['nodes'] if z['node_type'] == 'theorem' and z['status'] != 'Definition'}
    assert mathematical(final_graph) == mathematical(before_graph)
    before_sketches = {z['node_id'] for z in before_graph['nodes'] if z['node_type'] == 'sketch'}
    new_reductions = [z for z in final_graph['nodes'] if z['node_type'] == 'sketch' and z['node_id'] not in before_sketches]
    assert len(new_reductions) == 1 and new_reductions[0]['parent_theorem_id'] == ident
    assert new_reductions[0]['status'] == 'ACCEPTED'
    reduction_id = new_reductions[0]['node_id']
    names = {z['theorem_id']: z for z in final_graph['nodes'] if z['node_type'] == 'theorem' and z['status'] != 'Definition'}
    incoming = {e['source'] for e in final_graph['edges'] if e['target'] == reduction_id and e['kind'] == 'sketch'}
    actual_children = sorted(incoming & set(names))
    save('platform-definition-imports.json', {'scope': 'Existing Definition imports excluded from mathematical child counts', 'ids': sorted(incoming - set(names))})
    actual = []
    for child in actual_children:
        assert child in names and names[child]['status'] == 'Proved'
        z = api.request('/theorems/' + child)
        assert z['status'] == 'Proved' and z['visibility'] == 'private' and z['mathlib_rev'] == ENV
        actual.append({'id': child, 'name': z['theorem_name'], 'status': z['status']})
    save('actual-platform-reduction.json', {'submission_id': result.get('id'), 'reduction_id': reduction_id,
        'status': 'ACCEPTED', 'children': actual, 'source': 'Complete final API graph; no inferred child count.'})
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
    assert old['total'] == 18 and page['total'] == 17
    assert {z['theorem_id'] for z in leaves} == {z['theorem_id'] for z in old['open_leaves']} - {ident}
    print('Exact divisor comparison ACCEPTED; root Open; complete frontier 18 -> 17.', flush=True)


if __name__ == '__main__':
    {'bind': bind, 'generate': generate, 'preflight': preflight, 'publish': publish}[sys.argv[1]]()
