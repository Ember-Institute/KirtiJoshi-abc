"""Main-agent-only conductor-extension split delivery; no import-time effects.

Generate raw upload and audit sources, obtain MCP-CI receipts, then preflight/publish.
This script never compiles, changes Git, or updates the registry/pending database.
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
u = '.local/adaptation/conductor-extension-split-20261114/'
b = w / u
pre = 'AbcAdaptation.Tripod.Fermat.Proper.'
parent = pre + 'belyiActualFieldConductorExtension'
PARENT_ID = '2383cd37-cc7e-49bd-afc6-838a919d2ce3'
children = [pre + n for n in ['belyiActualFieldLocalConductorComparison',
                             'belyiActualFieldDifferentAccounting']]
children_payload_tag = 'conductor-extension-children'
parent_verify_tag = 'reduce-parent'
definitions = [{
    'name': 'FermatBelyiConductorExtension' + suffix,
    'source': 'Definitions/Def_FermatBelyiConductorExtension' + suffix + '.lean',
    'publish_tag': 'def-FermatBelyiConductorExtension' + suffix,
    'readback': 'platform-after-definition-FermatBelyiConductorExtension' + suffix + '.json'}
    for suffix in ['FinitePlaces', 'Children']]
adapter = 'Solutions/Source_FermatBelyiConductorExtensionAdapters.lean'
checks = 'Solutions/Checks_FermatBelyiConductorExtensionReduction.lean'
reduction_checks = checks
closed_checks = 'Solutions/Checks_FermatBelyiConductorExtensionClosed.lean'
composer = pre + 'belyiActualFieldConductorExtension_of_local_and_accounting'
ENV = '0df444a360eaa60ab8c11dca51a86af692955474'
ROOT = 'e33ff731-60a7-43ef-87ae-c12aeba23cb5'
STANDARD = {'propext', 'Classical.choice', 'Quot.sound'}
PRIOR = w / '.local/adaptation/belyi-different-conductor-split-20261114'
TARGET_PACKET = PRIOR / 'final-readbacks.json'
EXPECTED_BEFORE = {'accepted_reductions': 35, 'published_children': 81,
    'dependency_edges': 99, 'open_frontier': 17, 'direct_closed_children': 40}
EXPECTED_AFTER = {'accepted_reductions': 36, 'published_children': 83,
    'dependency_edges': 101, 'open_frontier': 18, 'direct_closed_children': 40}


def child_path(name):
    return 'Theorems/Thm_' + name.replace('.', '_') + '.lean'


source = child_path(parent)
sol = u + 'Solution_belyiActualFieldConductorExtension.lean'
fresh_paths = [d['source'] for d in definitions] + [adapter] + [child_path(n) for n in children]
authored_paths = fresh_paths + [source]
own = authored_paths + [checks, closed_checks]


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


def load_protocol():
    spec = importlib.util.spec_from_file_location('api', w / '.local/abc-item/api.py')
    api = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(api)
    assert api.base == 'https://prove2.me/api/v1'
    context = globals() | {'api': api}
    protocol = w / '.local/adaptation/platform-tripod-20261113/executed-platform-publish.py'
    picked = set()
    for node in ast.parse(protocol.read_text()).body:
        if isinstance(node, ast.FunctionDef) and node.name in {'publish', 'verify'}:
            exec(compile(ast.Module(body=[node], type_ignores=[]), '<established-protocol>', 'exec'), context)
            picked.add(node.name)
    assert picked == {'publish', 'verify'}
    return api, context


def publication(protocol, tag, endpoint, payload):
    """An uncertain mutation is reconciled by submission ID, never blind POST."""
    intent, receipt = b / (tag + '-publication-requested.json'), b / (tag + '-submit.json')
    request = {'endpoint': endpoint, 'payload': payload}
    if intent.exists():
        assert read(intent.name) == request
        assert receipt.exists(), 'Publication outcome unknown: reconcile original request/job before retry'
    else:
        assert not receipt.exists()
        save(intent.name, request)
    if receipt.exists():
        assert read(tag + '-payload.json') == payload
    return protocol['publish'](tag, endpoint, payload)


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


def definition_code(row):
    values = [row[key] for key in ['definition', 'definitions'] if row.get(key)]
    assert values, ('Definition record has no nonempty source code', row.get('theorem_id'))
    assert all(value == values[0] for value in values)
    return values[0]


def authored_rows():
    rows = [z for z in graph() if z['module'] in {module(p) for p in authored_paths}
            and z['startLine'] > 0]
    assert len({z['name'] for z in rows}) == len(rows)
    for path in authored_paths:
        parsed = [z for z in read('syntax-boundaries.json') if z['file'] == path]
        compiled = [z for z in rows if z['module'] == module(path)]
        assert parsed and len(parsed) == len(compiled), path
        assert {z['nameText'] for z in parsed} == {z['userName'].split('.')[-1] for z in compiled}, path
    return rows


def bind():
    """Bind every authored declaration, including the unchanged-type parent."""
    packet = read('blind-readbacks-source.json')
    rows = packet['declarations']
    compiled = authored_rows()
    expected = {z['name'] for z in compiled}
    out = []
    for row in rows:
        path, name = row['source_relative_path'], row['logical_qualified_name']
        assert path in authored_paths
        original = Path(row['source_path'])
        assert sha(original) == row['source_sha256']
        old = original.read_bytes()[row['source_span']['start_byte']:
                                    row['source_span']['end_byte_exclusive']]
        assert old.decode() == row['raw_declaration']
        assert hashlib.sha256(old).hexdigest() == row['raw_declaration_sha256']
        z = one_decl(path, name)
        out.append(binding(z, path) | {'raw_signature': header(path, name),
            'original_raw_signature': row['raw_signature'], 'original_blind_row': row,
            'original_packet': 'blind-readbacks-source.json',
            'original_packet_sha256': sha(b / 'blind-readbacks-source.json'),
            'blind_original_path': str(original), 'blind_original_sha256': row['source_sha256'],
            'en': row['readback']['en'], 'zh_Hans': row['readback']['zh-Hans'],
            'ja': row['readback']['ja'], 'proof_notes': row.get('proof_notes'),
            'quotation': None, 'fresh_compiler_binder_review_required': True})
    assert len(out) == len(expected) and {z['declaration'] for z in out} == expected
    old_parent = next(z for z in json.loads(TARGET_PACKET.read_text())['declarations']
                      if z['userName'] == parent)
    baseline = next(z for z in read('root-graph-before.json')['nodes']
                    if z.get('theorem_name') == parent)
    before = read('platform-before-parent.json')
    assert baseline['theorem_id'] == before['theorem_id'] == PARENT_ID
    assert before['formal_statement'] == baseline['formal_statement']
    parent_row = next(z for z in out if z['userName'] == parent)
    parent_row.update(reused_parent_meaning={k: old_parent[k] for k in ['en', 'zh_Hans', 'ja']},
        reused_from=str(TARGET_PACKET.relative_to(w)), reused_packet_sha256=sha(TARGET_PACKET),
        historical_platform_formal_statement=before['formal_statement'],
        reuse_basis='Exact original parent platform statement; fresh source readback and compiler binder audit retained separately.')
    audit_path = b / 'compiler-readback-type-review.json'
    if audit_path.exists():
        audit = read(audit_path.name)
        assert audit['passed'] and audit['compiler_evidence']['graph_sha256'] == sha(b / 'decl_graph.jsonl')
        by_name = {z['declaration']: z for z in out}
        for z in audit['declarations']:
            correction = z.get('corrected_trilingual_statement')
            if correction:
                entry = by_name[z['compiler_name']]
                entry['superseded_blind_statements'] = {k: entry[k] for k in ['en', 'zh_Hans', 'ja']}
                entry.update(correction)
                entry['compiler_readback_correction'] = audit_path.name
    from term_resolver import resolve_rows
    out = resolve_rows(out, b)
    save('final-readbacks.json', {'declarations': out, 'blind_readback': True,
        'compiler_bound': True, 'quotations_separate': True,
        'fresh_binder_review_count': len(out), 'reused_parent_meaning': 1,
        'count_basis': 'Exact equality of blind packet, compiler authored set, and parser declaration set.'})


def generated_paths():
    return [sol, u + 'AuditSolution.lean', u + 'AuditDefinition.lean'] + [
        u + 'UploadDefinition' + str(i) + '.lean' for i in range(len(definitions))] + [
        u + 'UploadType' + str(i) + '.lean' for i in range(len(children))]


def generated_hashes():
    return {p: sha(w / p) for p in generated_paths()}


def generate():
    bind()
    rows = authored_rows()
    reached = reached_from([parent])
    authored = {z['name'] for z in rows}
    assert authored <= reached, sorted(authored - reached)
    assert all(z['module'] != module(adapter) or z['name'] in reached for z in rows)
    save('consumer-closure.json', {'root': parent, 'declarations': sorted(authored),
        'all_authored_declarations_consumed': True,
        'new_mathematical_children': children, 'remaining_open_children': children})
    alias_bodies, alias_imports, def_pairs = [], ['import Lean'], []
    for i, item in enumerate(definitions):
        path = item['source']
        code = (w / path).read_text()
        imports, _ = split_imports(code)
        assert imports and all(x.startswith(('import Definitions.', 'import Mathlib.')) for x in imports)
        assert 'sorry' not in code and 'import Solutions.' not in code and 'import Theorems.' not in code
        write_source(u + 'UploadDefinition' + str(i) + '.lean', code)
        old_namespace = pre.rstrip('.') + ('.ConductorExtensionSource' if i == 0 else '')
        new_namespace = 'PlatformDefinitionAudit' + ('.ConductorExtensionSource' if i == 0 else '')
        assert code.count('namespace ' + old_namespace) == 1
        assert code.count('end ' + old_namespace) == 1
        alias = code.replace('namespace ' + old_namespace, 'namespace ' + new_namespace, 1)
        alias = alias.replace('end ' + old_namespace, 'end ' + new_namespace, 1)
        if i == 1:
            alias = alias.replace('open ConductorExtensionSource\n', 'open PlatformDefinitionAudit.ConductorExtensionSource\n', 1)
        imports, body = split_imports(alias)
        for line in ['import ' + module(path)] + imports:
            if line not in alias_imports:
                alias_imports.append(line)
        alias_bodies.append(body)
        for z in rows:
            if z['module'] != module(path):
                continue
            assert z['userName'].startswith(pre)
            alias_name = 'PlatformDefinitionAudit.' + z['userName'].removeprefix(pre)
            def_pairs.append((z['name'], alias_name, z['kind'] in ['def', 'abbrev']))
    # The alias modules stay in their original lexical order. Parent namespace
    # openings retain the meaning of relative Tripod and actual model names.
    def_audit = '\n'.join(alias_imports) + '\n\nopen AbcAdaptation\nopen ' + pre.rstrip('.')
    def_audit += '\n\n' + '\n\n'.join(alias_bodies)
    pairs = '#[' + ','.join('(`' + a + ', `' + c + ', ' + str(is_def).lower() + ')'
                            for a, c, is_def in def_pairs) + ']'
    def_audit += '''

open Lean
run_meta do
  let pairs : Array (Name × Name × Bool) := PAIRS
  let mut rows : Array Json := #[]
  for (original, uploaded, compareBody) in pairs do
    let a ← getConstInfo original
    let c ← getConstInfo uploaded
    unless ← Meta.isDefEq a.type c.type do throwError "Definition-module type differs: {original}"
    let aExpr ← Meta.mkConstWithFreshMVarLevels original
    let cExpr ← Meta.mkConstWithFreshMVarLevels uploaded
    unless ← Meta.withTransparency .all (Meta.isDefEq aExpr cExpr) do
      throwError "Definition-module term differs: {original}"
    let axs ← collectAxioms uploaded
    for ax in axs do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Unexpected Definition-module axiom {ax}"
    rows := rows.push (Json.mkObj [("name",toJson original.toString),
      ("uploaded",toJson uploaded.toString),("type_equal",Json.bool true),
      ("body_equal",Json.bool true),("computational_declaration",Json.bool compareBody),
      ("axioms",toJson (axs.map toString))])
  IO.FS.writeFile "OUTPUT" (Json.pretty (Json.arr rows))
'''.replace('PAIRS', pairs).replace('OUTPUT', u + 'definition-type-audit.json')
    write_source(u + 'AuditDefinition.lean', def_audit)
    items = []
    for i, name in enumerate(children):
        path = child_path(name)
        imports, _ = split_imports((w / path).read_text())
        assert imports and all(x.startswith('import Definitions.') for x in imports)
        preamble = '\n'.join(imports) + '\n\nset_option autoImplicit false\n\nopen AbcAdaptation\nopen ' + pre.rstrip('.')
        preamble += '\nopen NumberField IsDedekindDomain Module\nopen scoped Classical IntermediateField'
        statement = header(path, name, name) + ' := by sorry'
        assert statement.startswith('theorem ' + name + ' : ')
        item = {'theorem_name': name, 'preamble': preamble, 'formal_statement': statement}
        items.append(item)
        write_source(u + 'UploadType' + str(i) + '.lean', preamble + '\n\n' + statement)
    save('upload-problem-items.json', items)
    retained = {z['name'] for z in rows if z['module'] == module(adapter) and z['name'] in reached}
    raw, removals = pruned_module(adapter, retained)
    imports, body = split_imports(raw)
    assert all(x.startswith(('import Definitions.', 'import Mathlib.')) for x in imports)
    imports += ['import ' + module(child_path(n)) for n in children]
    formal = read('platform-before-parent.json')['formal_statement']
    assert formal.startswith('theorem ' + parent + ' : ') and formal.endswith(' := by sorry')
    exact = formal.replace('theorem ' + parent, 'theorem solution', 1).removesuffix(' := by sorry')
    solution = '\n'.join(imports) + '\n\n' + body + '\n\nopen AbcAdaptation\nopen ' + pre.rstrip('.')
    solution += '\n\n' + exact + ' :=\n  ' + composer + '\n    ' + '\n    '.join(children) + '\n'
    assert 'sorry' not in solution and 'import Solutions.' not in solution
    assert 'import ' + module(source) not in solution
    assert {x for x in imports if x.startswith('import Theorems.')} == {
        'import ' + module(child_path(n)) for n in children}
    write_source(sol, solution)
    type_audit = 'import Lean\n' + solution.replace('theorem solution ', 'theorem PlatformReduction ', 1)
    for i, item in enumerate(items):
        annotation = item['formal_statement'].replace('theorem ' + item['theorem_name'],
            'theorem PlatformUploadType' + str(i), 1).removesuffix(' := by sorry')
        type_audit += '\n' + annotation + ' := ' + item['theorem_name'] + '\n'
    type_audit += '\n' + formal.replace('theorem ' + parent, 'theorem PlatformOriginalParentType', 1).removesuffix(' := by sorry')
    type_audit += ' := PlatformReduction\n'
    type_audit += '\n' + header(source, parent, 'PlatformSourceParentType') + ' := PlatformReduction\n'
    pairs = [(n, 'PlatformUploadType' + str(i)) for i, n in enumerate(children)] + [
        ('PlatformOriginalParentType', 'PlatformReduction'), ('PlatformSourceParentType', 'PlatformReduction')]
    pairs_lean = '#[' + ','.join('(`' + a + ', `' + c + ')' for a, c in pairs) + ']'
    type_audit += '''
open Lean
run_meta do
  let pairs : Array (Name × Name) := PAIRS
  let mut rows : Array Json := #[]
  for (original, uploaded) in pairs do
    let a ← getConstInfo original
    let c ← getConstInfo uploaded
    unless ← Meta.isDefEq a.type c.type do throwError "Exact uploaded/source type differs: {original}"
    let axs ← collectAxioms uploaded
    unless axs.contains `sorryAx do throwError "Expected explicit Open child debt missing: {uploaded}"
    for ax in axs do
      unless #[`propext, `Classical.choice, `Quot.sound, `sorryAx].contains ax do
        throwError "Unexpected reduction axiom {ax}"
    rows := rows.push (Json.mkObj [("original",toJson original.toString),
      ("checked",toJson uploaded.toString),("type_equal",Json.bool true),
      ("expected_sorry",Json.bool true),("axioms",toJson (axs.map toString))])
  IO.FS.writeFile "OUTPUT" (Json.pretty (Json.arr rows))
'''.replace('PAIRS', pairs_lean).replace('OUTPUT', u + 'type-audit.json')
    write_source(u + 'AuditSolution.lean', type_audit)
    save('solution-source-closure.json', {'source': sol, 'source_sha256': sha(w / sol),
        'graph_sha256': sha(b / 'decl_graph.jsonl'), 'parser_sha256': sha(b / 'syntax-boundaries.json'),
        'source_hashes': {p: sha(w / p) for p in authored_paths},
        'retained_helpers': sorted(retained), 'removed_whole_commands': removals,
        'parent_imports': imports, 'only_parent_mathematical_imports': children,
        'no_solutions_import': True, 'new_definitions': [d['name'] for d in definitions],
        'new_children': children, 'new_direct_proofs': [], 'parent_type_unchanged': True})
    save('generated-source-hashes.json', generated_hashes())


def receipt_plan():
    plan = []
    for path in authored_paths:
        stem = Path(path).stem.removeprefix('Def_').removeprefix('Source_')
        for suffix in ['leaf', 'artifact']:
            plan.append((stem + '-' + suffix, path, False, suffix == 'artifact'))
    plan += [('closed-axioms-review', closed_checks, True, False),
        ('reduction-axioms-leaf', checks, False, False),
        ('source-graph-leaf', u + 'ExtractConductorExtensionGraph.lean', False, False),
        ('syntax-leaf', u + 'ExtractConductorExtensionSyntax.lean', False, False),
        ('all-constants-leaf', u + 'AuditAllConstants.lean', False, False),
        ('solution-leaf', sol, False, False),
        ('types-leaf', u + 'AuditSolution.lean', False, False),
        ('definition-types-leaf', u + 'AuditDefinition.lean', False, False),
        ('production-gates-review', u + 'ProductionGates.lean', True, False),
        ('consumer-review', u + 'ChecksConductorExtensionConsumer.lean', True, False)]
    plan += [('upload-definition-' + str(i) + '-leaf', u + 'UploadDefinition' + str(i) + '.lean', False, False)
             for i in range(len(definitions))]
    plan += [('upload-type-' + str(i) + '-leaf', u + 'UploadType' + str(i) + '.lean', False, False)
             for i in range(len(children))]
    return plan


def preflight_definitions():
    jobs = []
    for i, item in enumerate(definitions):
        path, name = item['source'], item['name']
        jobs += [checked(name + '-leaf', path), checked(name + '-artifact', path, artifact=True),
                 checked('upload-definition-' + str(i) + '-leaf', u + 'UploadDefinition' + str(i) + '.lean')]
        assert (b / ('UploadDefinition' + str(i) + '.lean')).read_bytes() == (w / path).read_bytes()
    jobs += [checked('definition-types-leaf', u + 'AuditDefinition.lean'),
             checked('closed-axioms-review', closed_checks, review=True)]
    expected = {z['name'] for z in authored_rows() if z['module'] in {module(d['source']) for d in definitions}}
    audit = read('definition-type-audit.json')
    assert len(audit) == len(expected) and {z['name'] for z in audit} == expected
    assert all(z['type_equal'] and z['body_equal'] and set(z['axioms']) <= STANDARD for z in audit)
    return jobs


def preflight():
    jobs = [checked(*entry) for entry in receipt_plan()]
    preflight_definitions()
    rows = authored_rows()
    by_compiler_name = {z['name']: z for z in graph()}
    for tag in ['source-graph-leaf', 'syntax-leaf', 'all-constants-leaf', 'production-gates-review']:
        hashes = read(tag + '-result.json')['request']['worktree_manifest']['input_hashes']
        assert all(hashes[p] == sha(w / p) for p in authored_paths), tag
    hashes = read('production-gates-review-result.json')['request']['worktree_manifest']['input_hashes']
    assert all(hashes[p] == sha(w / p) for p in own)
    gate_imports = {line.removeprefix('import ') for line in (b / 'ProductionGates.lean').read_text().splitlines()
                    if line.startswith('import ')}
    assert gate_imports == {'ArithmeticTeichmullerSpaces.Prologue.Audit.ImportAudit',
        'ArithmeticTeichmullerSpaces.Act1Scene1', 'ArithmeticTeichmullerSpaces.Prologue.Audit.AxiomAudit'}
    axioms = read('all-module-axioms.json')
    axs = {z['name']: z for z in axioms}
    modules = {module(p) for p in authored_paths}
    expected = {z['name'] for z in graph() if z['module'] in modules}
    assert expected <= set(axs)
    for name in expected:
        z = axs[name]
        permitted = by_compiler_name[name]['module'] in {module(child_path(n)) for n in children + [parent]}
        assert set(z['axioms']) <= STANDARD | ({'sorryAx'} if permitted else set()), name
    assert all('sorryAx' in axs[n]['axioms'] for n in children + [parent])
    assert all('sorryAx' not in axs[z['name']]['axioms'] for z in rows
               if z['module'] in {module(d['source']) for d in definitions} | {module(adapter)})
    parent_refs = {n for n in by_compiler_name[parent]['valueDeps'] if n in by_compiler_name
                   and by_compiler_name[n]['module'].startswith('Theorems.')
                   and by_compiler_name[n]['startLine'] > 0}
    assert parent_refs == set(children)
    span = syntax(source, parent)
    raw_body = (w / source).read_bytes()[span['valStart']['offset']:span['declEnd']['offset']].decode()
    expected_body = ':= belyiActualFieldConductorExtension_of_local_and_accounting ' + ' '.join(n.removeprefix(pre) for n in children)
    assert ' '.join(raw_body.split()) in [expected_body, expected_body.replace(':= ', ':= by exact ', 1)]
    audit = read('type-audit.json')
    expected_pairs = {(n, 'PlatformUploadType' + str(i)) for i, n in enumerate(children)} | {
        ('PlatformOriginalParentType', 'PlatformReduction'), ('PlatformSourceParentType', 'PlatformReduction')}
    assert len(audit) == len(expected_pairs)
    assert {(z['original'], z['checked']) for z in audit} == expected_pairs
    assert all(z['type_equal'] and z['expected_sorry'] and 'sorryAx' in z['axioms']
               and set(z['axioms']) <= STANDARD | {'sorryAx'} for z in audit)
    items = read('upload-problem-items.json')
    assert len(items) == len(children)
    for i, item in enumerate(items):
        assert item['theorem_name'] == children[i]
        assert item['formal_statement'] == header(child_path(children[i]), children[i], children[i]) + ' := by sorry'
        assert (b / ('UploadType' + str(i) + '.lean')).read_text() == item['preamble'] + '\n\n' + item['formal_statement'] + '\n'
    rb = read('final-readbacks.json')['declarations']
    assert len(rb) == len(rows) and {z['declaration'] for z in rb} == {z['name'] for z in rows}
    assert all(z['source_sha256'] == sha(w / z['path']) for z in rb)
    review = read('compiler-readback-type-review.json')
    assert review['passed'] and review['compiler_evidence']['graph_sha256'] == sha(b / 'decl_graph.jsonl')
    assert len(review['declarations']) == len(rows)
    assert {z['compiler_name'] for z in review['declarations']} == {z['name'] for z in rows}
    assert {z['path']: z['sha256'] for z in review['original_packets']} == {
        'blind-readbacks-source.json': sha(b / 'blind-readbacks-source.json')}
    bound = {z['declaration']: z for z in rb}
    for z in review['declarations']:
        original = bound[z['compiler_name']]
        assert z['passed'] and z['compiler_type'] == original['compiler_type']
        assert z['current_source']['sha256'] == original['source_sha256']
        if z.get('corrected_trilingual_statement'):
            from term_resolver import approved_text
            assert all(original[k] == (approved_text(z['corrected_trilingual_statement'][k]) if k == 'zh_Hans' else z['corrected_trilingual_statement'][k]) for k in ['en', 'zh_Hans', 'ja'])
    closure = read('solution-source-closure.json')
    assert closure['source_sha256'] == sha(w / sol)
    assert closure['graph_sha256'] == sha(b / 'decl_graph.jsonl')
    assert closure['parser_sha256'] == sha(b / 'syntax-boundaries.json')
    assert all(closure['source_hashes'][p] == sha(w / p) for p in authored_paths)
    assert read('consumer-closure.json')['all_authored_declarations_consumed']
    assert {z['name'] for z in rows} <= reached_from([parent])
    assert 'sorry' not in (w / sol).read_text() and 'import Solutions.' not in (w / sol).read_text()
    assert generated_hashes() == read('generated-source-hashes.json')
    consumer = read('consumer-config.json')
    assert consumer['ci_tag'] == 'consumer-review' and consumer['review'] is True
    assert consumer['source'] == u + 'ChecksConductorExtensionConsumer.lean'
    assert consumer['expected_sorryAx'] is False and consumer['parent_still_open_expected']
    assert consumer['actual_consumer'] == pre + 'belyiDifferentConductorComparison_of_exact_children'
    assert consumer['root_consumer'] == pre + 'canonicalEstimate_of_belyi_children'
    assert consumer['explicit_remaining_children'] == ['BelyiActualFieldLocalConductorComparison',
                                                      'BelyiActualFieldDifferentAccounting']
    assert consumer['source_path'] == 'Definitions/Def_FermatCanonicalBelyiComposition.lean'
    assert consumer['source_sha256'] == sha(w / consumer['source_path'])
    consumer_hashes = read('consumer-review-result.json')['request']['worktree_manifest']['input_hashes']
    assert all(consumer_hashes[p] == sha(w / p) for p in [consumer['source_path'], adapter] + [d['source'] for d in definitions])
    consumer_text = (w / consumer['source']).read_text()
    assert all('import ' + module(child_path(n)) not in consumer_text for n in children + [parent])
    assert 'BelyiActualFieldLocalConductorComparison' in consumer_text and 'BelyiActualFieldDifferentAccounting' in consumer_text
    assert 'belyiActualFieldConductorExtension_of_local_and_accounting' in consumer_text
    assert 'belyiDifferentConductorComparison_of_exact_children' in consumer_text
    assert 'canonicalEstimate_of_belyi_children' in consumer_text
    assert '(belyiActualFieldConductorExtension_of_local_and_accounting hLocal hAccounting)' in consumer_text
    consumer_result = read('consumer-review-result.json')['result']
    assert 'sorryAx' not in consumer_result.get('stdout', '') + consumer_result.get('stderr', '')
    source_consumer = read('source-consumer.json')['declarations']
    assert {z['declaration'] for z in source_consumer} == {z['name'] for z in rows}
    delivery_review = read('independent-delivery-review.json')
    assert delivery_review['passed'] and delivery_review['blockers'] == []
    assert delivery_review['source_ledger_passed'] and delivery_review['all_new_outputs_have_actual_consumers']
    assert delivery_review['source_ledger_sha256'] == sha(r / 'ArithmeticTeichmullerSpaces/SOURCE_LEDGER.md')
    assert delivery_review['generated_source_hashes'] == generated_hashes()
    assert {z['job_id'] for z in jobs} <= set(delivery_review['compiler_checks'])
    subprocess.run(['git', 'diff', '--check'], cwd=r, check=True)
    validation = {'passed': True, 'original_parent_type_equal': True,
        'all_child_types_equal': True, 'definition_types_and_bodies_equal': True,
        'readbacks': len(rb), 'fresh_compiler_binder_reviews': len(rows),
        'owned_source_hashes': {p: sha(w / p) for p in own},
        'generated_source_hashes': generated_hashes(), 'compiler_checks': [z['job_id'] for z in jobs],
        'new_definitions': [d['name'] for d in definitions], 'new_children': children,
        'closed_direct_children': [], 'remaining_open_children': children,
        'independent_delivery_review_sha256': sha(b / 'independent-delivery-review.json')}
    save('delivery-validation.json', validation)
    required_evidence = [tag + '-result.json' for tag, _, _, _ in receipt_plan()] + [
        'decl_graph.jsonl', 'syntax-boundaries.json', 'all-module-axioms.json',
        'type-audit.json', 'definition-type-audit.json', 'blind-readbacks-source.json',
        'final-readbacks.json', 'compiler-readback-type-review.json',
        'independent-delivery-review.json', 'consumer-closure.json', 'consumer-config.json',
        'source-consumer.json', 'solution-source-closure.json',
        'generated-source-hashes.json', 'delivery-validation.json']
    return {'validation': validation, 'owned_sources': own,
            'required_jobs': jobs, 'required_evidence': required_evidence}


def metadata_inputs():
    quote = (b / 'quotation.md').read_text().strip()
    description = (b / 'source-description.txt').read_text().strip()
    assert quote and description
    return quote, description, read('final-readbacks.json')['declarations']


def publish():
    preflight()
    api, protocol = load_protocol()
    quote, description, rb = metadata_inputs()
    before = read('platform-before-parent.json')
    assert before['theorem_id'] == PARENT_ID and before['theorem_name'] == parent
    assert before['status'] == 'Open' and before['visibility'] == 'private' and before['mathlib_rev'] == ENV
    baseline = read('root-graph-before.json')
    assert baseline['mathematical_closure_complete']
    assert not set(children).intersection(z.get('theorem_name') for z in baseline['nodes'])
    assert read('root-frontier-before.json')['total'] == EXPECTED_BEFORE['open_frontier']
    assert read('registry-before.json')['graph_counts'] == EXPECTED_BEFORE
    current = api.request('/theorems/' + PARENT_ID)
    assert current['formal_statement'] == before['formal_statement'] and current['preamble'] == before['preamble']
    preflight_definitions()
    definition_ids = {}
    for i, item in enumerate(definitions):
        selected = [z for z in rb if z['path'] == item['source']]
        assert selected
        payload = {'definition_name': item['name'], 'definition_title': {
            0: 'Actual finite-place arithmetic for the Belyi point-field inclusion',
            1: 'Local conductor comparison and exact different accounting for actual Belyi fields'}[i],
            'definition': (b / ('UploadDefinition' + str(i) + '.lean')).read_text(),
            'natural_language_statement': quote + '\n\n' + prose(selected),
            'source': description, 'env': ENV, 'private': True,
            'tags': ['abc-conjecture', 'arithmetic-geometry']}
        results = publication(protocol, item['publish_tag'], '/submit-definition', payload)
        assert len(results) == 1
        ident = results[0]['theorem_id']
        state = api.request('/theorems/' + ident)
        assert state['theorem_id'] == ident and state['theorem_name'] == item['name']
        assert state['status'] == 'Definition' and state['visibility'] == 'private' and state['mathlib_rev'] == ENV
        assert definition_code(state) == payload['definition']
        save(item['readback'], state)
        definition_ids[item['name']] = ident
        save('published-definition-ids.json', definition_ids)
    assert len(set(definition_ids.values())) == len(definitions)
    items = read('upload-problem-items.json')
    titles = ['Local conductor inequality over each actual finite place',
              'Finite support and exact accounting of the actual relative different']
    for item, title in zip(items, titles):
        selected = [z for z in rb if z['userName'] == item['theorem_name']]
        assert len(selected) == 1
        item.update(theorem_title=title, natural_language_statement=quote + '\n\n' + prose(selected),
                    source=description, tags=['abc-conjecture', 'arithmetic-geometry'])
    results = publication(protocol, children_payload_tag, '/submit-problem',
                          {'problems': items, 'env': ENV, 'private': True})
    assert len(results) == len(children)
    ids = {z['theorem_name']: z['theorem_id'] for z in results}
    assert set(ids) == set(children) and len(set(ids.values())) == len(children)
    save('published-child-ids.json', ids)
    for item in items:
        name = item['theorem_name']
        state = api.request('/theorems/' + ids[name])
        assert state['theorem_name'] == name and state['status'] == 'Open'
        assert state['visibility'] == 'private' and state['mathlib_rev'] == ENV
        assert state['formal_statement'] == item['formal_statement'] and state['preamble'] == item['preamble']
        assert state['natural_language_statement'] == item['natural_language_statement']
        save('platform-after-' + name.removeprefix(pre) + '.json', state)
    selected = [z for z in rb if z['userName'] == parent]
    assert len(selected) == 1
    explanation = quote + '\n\n' + prose(selected) + '\n\n' + description
    explanation += '\n\nThe unchanged conductor-extension statement is reduced to exactly two explicit arithmetic children. The local child bounds the normalized logarithmic norm at every actual finite place by the sum over its actual extensions and the actual different contribution. The accounting child supplies both finite support and the exact grouped different identity. The closed source adapters identify the existing finite-set conductor with its finite support sum, use disjoint actual places-over fibers and the algebra-map containment of the actual finite element sets, and bound a finite subtotal of nonnegative different contributions by the complete sum. No upper bound for the different, Serre bound, extra field equality, new model law or smaller-field substitution is assumed. Both children remain Open; this is a decomposition, and the original parent, canonicalEstimate and root remain Open.'
    assert len(explanation) <= 50000
    result = verification(protocol, parent_verify_tag, PARENT_ID, sol, explanation)
    assert result['status'] == 'SKETCH_ACCEPTED'
    patch = {'natural_language_statement': quote + '\n\n' + prose(selected), 'source': description}
    save('parent-metadata-patch-request.json', patch)
    current = api.request('/theorems/' + PARENT_ID)
    assert current['formal_statement'] == before['formal_statement'] and current['preamble'] == before['preamble']
    if not all(current.get(key) == value for key, value in patch.items()):
        save('parent-metadata-patch-response.json', api.request('/theorems/' + PARENT_ID, patch, 'PATCH'))
    for name, ident in [(parent, PARENT_ID)] + list(ids.items()):
        state = api.request('/theorems/' + ident)
        assert state['theorem_id'] == ident and state['theorem_name'] == name and state['status'] == 'Open'
        assert state['visibility'] == 'private' and state['mathlib_rev'] == ENV
        assert not state.get('deprecated_at') and not state.get('deprecated') and not state.get('is_deprecated')
        if name == parent:
            assert state['formal_statement'] == before['formal_statement'] and state['preamble'] == before['preamble']
            assert all(state[key] == value for key, value in patch.items())
            save('platform-after-parent.json', state)
        else:
            save('platform-after-' + name.removeprefix(pre) + '.json', state)
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
    # Definition visibility varies with graph depth. Each omitted old Definition
    # gets an actual read-only GET before retention checks, never another POST.
    old_defs = {z['theorem_id'] for z in baseline['nodes'] if z.get('status') == 'Definition'}
    visible_defs = {z['theorem_id'] for z in after['nodes'] if z.get('status') == 'Definition'}
    retention = [api.request('/theorems/' + ident) for ident in sorted(old_defs - visible_defs)]
    save('definition-retention-readbacks.json', {'definitions': retention})
    verify_graph(baseline, after, ids, definition_ids, result)
    print('Exact two-child conductor-extension reduction SKETCH_ACCEPTED; both children remain Open.', flush=True)


def summary_without_direct_proof_nodes(graph_input, direct_ids):
    """Retain the shared summary API; this unit submits no direct proofs."""
    assert not direct_ids
    sys.path.insert(0, str(w / '.local/adaptation/northcott-sourceproof-20261114'))
    from delivery_common import graph_summary
    return graph_summary(graph_input)


def retained_definitions(before, after, definition_ids):
    old = {z['theorem_id']: z for z in before['nodes'] if z.get('status') == 'Definition'}
    current = {z['theorem_id']: z for z in after['nodes'] if z.get('status') == 'Definition'}
    expected_new = set(definition_ids.values()) if isinstance(definition_ids, dict) else set(definition_ids)
    assert set(current) - set(old) == expected_new
    missing = set(old) - set(current)
    retention = read('definition-retention-readbacks.json') if missing or (b / 'definition-retention-readbacks.json').exists() else {'definitions': []}
    saved = {z['theorem_id']: z for z in retention['definitions']}
    assert len(saved) == len(retention['definitions']) and set(saved) == missing
    evidence = []
    for ident, previous in old.items():
        visible = ident in current
        row = current[ident] if visible else saved[ident]
        assert row['theorem_id'] == ident and row['theorem_name'] == previous['theorem_name']
        assert row['status'] == 'Definition' and row['formal_statement'] == previous['formal_statement']
        assert definition_code(row) == definition_code(previous)
        assert not row.get('deprecated_at')
        for key in ['deprecated', 'is_deprecated']:
            assert bool(row.get(key)) == bool(previous.get(key))
        if visible:
            for key in ['visibility', 'mathlib_rev']:
                if key in previous or key in row:
                    assert row.get(key) == previous.get(key)
        else:
            assert row['visibility'] == 'private' and row['mathlib_rev'] == ENV
        evidence.append({'id': ident, 'name': previous['theorem_name'],
                         'visible_in_after_graph': visible,
                         'exact_original_formal_statement': True,
                         'exact_original_definition_code': True})
    for item in definitions:
        ident = definition_ids[item['name']]
        row = current[ident]
        assert row['theorem_name'] == item['name']
        assert definition_code(row) == (w / item['source']).read_text()
    return {'existing_definitions': evidence, 'missing_from_graph_ids': sorted(missing),
            'retention_readbacks_sha256': sha(b / 'definition-retention-readbacks.json')
                if (b / 'definition-retention-readbacks.json').exists() else None,
            'new_definition_ids': definition_ids}


def verify_graph(before, after, ids, definition_ids, reduction):
    old = summary_without_direct_proof_nodes(before, set())
    new = summary_without_direct_proof_nodes(after, set())
    assert before['mathematical_closure_complete'] and after['mathematical_closure_complete']
    assert not after.get('has_hidden_deprecated') and not after.get('has_hidden_deprecated_sketches')
    old_nodes = {z['theorem_name']: z for z in before['nodes'] if z['node_type'] == 'theorem' and z['status'] != 'Definition'}
    new_nodes = {z['theorem_name']: z for z in after['nodes'] if z['node_type'] == 'theorem' and z['status'] != 'Definition'}
    assert set(new_nodes) - set(old_nodes) == set(children) and set(old_nodes) <= set(new_nodes)
    assert {new_nodes[n]['theorem_id'] for n in children} == set(ids.values())
    for name, previous in old_nodes.items():
        row = new_nodes[name]
        assert row['theorem_id'] == previous['theorem_id'] and row['status'] == previous['status']
        assert row['formal_statement'] == previous['formal_statement']
        assert not row.get('deprecated_at')
        for key in ['deprecated', 'is_deprecated']:
            assert bool(row.get(key)) == bool(previous.get(key))
    for name in children + [parent, 'AbcAdaptation.Tripod.Fermat.canonicalEstimate', 'abc.goal.lt_constant_mul_fix']:
        assert new_nodes[name]['status'] == 'Open'
    assert set(definition_ids) == {d['name'] for d in definitions}
    retention = retained_definitions(before, after, definition_ids)
    sketches = [z for z in after['nodes'] if z['node_type'] == 'sketch' and z['submission_id'] == reduction['id']]
    assert len(sketches) == 1 and sketches[0]['status'] == reduction['status'] == 'SKETCH_ACCEPTED'
    assert sketches[0]['parent_theorem_id'] == PARENT_ID
    all_math_ids = {z['theorem_id'] for z in new_nodes.values()}
    actual = {e['source'] for e in after['edges'] if e['kind'] == 'sketch'
              and e['target'] == sketches[0]['node_id'] and e['source'] in all_math_ids}
    assert actual == set(ids.values())
    old_reductions = {z['submission_id']: z for z in old['reductions']}
    current_reductions = {z['submission_id']: z for z in new['reductions']}
    assert set(current_reductions) - set(old_reductions) == {reduction['id']}
    assert all(current_reductions[k] == v for k, v in old_reductions.items())
    assert new['dependency_pairs'] - old['dependency_pairs'] == {(parent, name) for name in children}
    assert old['dependency_pairs'] <= new['dependency_pairs']
    for result, expected in [(old, EXPECTED_BEFORE), (new, EXPECTED_AFTER)]:
        assert result['counts'] == {k: expected[k] for k in ['accepted_reductions', 'published_children', 'dependency_edges']}
    bf, af = read('root-frontier-before.json'), read('root-frontier-after.json')
    for frontier, expected in [(bf, EXPECTED_BEFORE), (af, EXPECTED_AFTER)]:
        assert frontier['all_pages_fetched'] and frontier['total'] == expected['open_frontier']
        assert len(frontier['open_leaves']) == len({z['theorem_id'] for z in frontier['open_leaves']}) == frontier['total']
    assert {z['theorem_id'] for z in af['open_leaves']} == ({z['theorem_id'] for z in bf['open_leaves']}
        - {PARENT_ID}) | set(ids.values())
    registry = read('registry-before.json')
    direct = {z['name'] for z in registry['direct_closed_proofs']}
    assert len(direct) == EXPECTED_BEFORE['direct_closed_children'] == EXPECTED_AFTER['direct_closed_children']
    assert not direct.intersection(children) and all(new_nodes[n]['status'] == 'Proved' for n in direct)
    save('graph-count-evidence.json', {'before': EXPECTED_BEFORE, 'after': EXPECTED_AFTER,
        'new_definition_ids': definition_ids, 'published_child_ids': ids,
        'new_reductions': [current_reductions[reduction['id']]],
        'new_dependencies': [[parent, name] for name in children], 'direct_closed_proofs': [],
        'definition_retention': retention, 'remaining_open_children': children,
        'existing_nodes_preserved': True, 'existing_reductions_preserved': True,
        'deprecations': [], 'Fermat_route_preserved': True,
        'parent': 'Open', 'canonicalEstimate': 'Open', 'root': 'Open'})
    save('direct-graph-evidence.json', {'parent_id': PARENT_ID, 'submission_id': reduction['id'],
        'actual_child_ids': sorted(actual), 'expected_child_ids': sorted(ids.values()),
        'both_children_open': True, 'new_direct_proofs': [], 'parent_and_root_open': True})


if __name__ == '__main__':
    {'bind': bind, 'generate': generate, 'preflight': preflight, 'publish': publish}[sys.argv[1]]()
