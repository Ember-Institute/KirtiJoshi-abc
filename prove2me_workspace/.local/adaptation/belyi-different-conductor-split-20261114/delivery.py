"""Main-agent delivery tool for the exact Belyi different/conductor split.

No import-time effects. This script never starts a compiler or changes Git/registry.
The main agent generates evidence, obtains MCP-CI receipts, then publishes privately.
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
u = '.local/adaptation/belyi-different-conductor-split-20261114/'
b = w / u
pre = 'AbcAdaptation.Tripod.Fermat.Proper.'
parent = pre + 'belyiDifferentConductorComparison'
children = [pre + x for x in ['belyiActualFieldConductorExtension',
                             'belyiActualFieldDifferentTower',
                             'tripodGeneratorConductorIdentity']]
open_child, closed_children = children[0], children[1:]
definition_name = 'FermatBelyiDifferentConductorChildren'
definition = 'Definitions/Def_' + definition_name + '.lean'
adapter = 'Solutions/Source_FermatBelyiDifferentConductorAdapters.lean'
coord = 'Solutions/Source_FermatCoordRingSource.lean'
coord_helper = pre + 'CuspCoordRingSource.cuspDivisor_apply'
composer = pre + 'belyiDifferentConductorComparison_of_exact_children'
def_names = [pre + n for n in ['finiteSetLogCond', 'tripodConductorGenerators',
    'evaluatedCuspGenerators', 'belyiRelativeLogDifferent',
    'BelyiActualFieldConductorExtension', 'BelyiActualFieldDifferentTower',
    'TripodGeneratorConductorIdentity']]
closed_checks = 'Solutions/Checks_FermatBelyiDifferentConductorClosed.lean'
reduction_checks = 'Solutions/Checks_FermatBelyiDifferentConductorReduction.lean'
ENV = '0df444a360eaa60ab8c11dca51a86af692955474'
ROOT = 'e33ff731-60a7-43ef-87ae-c12aeba23cb5'
STANDARD = {'propext', 'Classical.choice', 'Quot.sound'}
TARGET_PACKET = w / '.local/adaptation/readbacks/fermat-proper-canonical-v1/result.json'
HELPER_PACKET = w / '.local/adaptation/cusp-generators-sourceproof-20261114/final-readbacks.json'
PRIOR = w / '.local/adaptation/divisor-degree-height-sourceproof-20261114'
EXPECTED_BEFORE = {'accepted_reductions': 34, 'published_children': 78,
    'dependency_edges': 96, 'open_frontier': 17, 'direct_closed_children': 38}
EXPECTED_AFTER = {'accepted_reductions': 35, 'published_children': 81,
    'dependency_edges': 99, 'open_frontier': 17, 'direct_closed_children': 40}


def child_path(name):
    return 'Theorems/Thm_' + name.replace('.', '_') + '.lean'


source = child_path(parent)
sol = u + 'Solution_belyiDifferentConductorComparison.lean'
direct_solutions = {name: u + 'Solution_' + name.removeprefix(pre) + '.lean'
                    for name in closed_children}
direct_source_names = {children[1]: 'closedBelyiActualFieldDifferentTowerSource',
                       children[2]: 'closedTripodGeneratorConductorIdentitySource'}
fresh_paths = [definition, adapter] + [child_path(n) for n in children]
own = fresh_paths + [source, closed_checks, reduction_checks]


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


def bind():
    packet = read('blind-readbacks-source.json')
    fresh = packet['declarations']
    assert len(fresh) == 18
    assert {z['source_relative_path'] for z in fresh} == set(fresh_paths)
    out = []
    for row in fresh:
        path, name = row['source_relative_path'], row['logical_qualified_name']
        original = Path(row['source_path'])
        assert sha(original) == row['source_sha256']
        old = original.read_bytes()[row['source_span']['start_byte']:
                                    row['source_span']['end_byte_exclusive']]
        assert old.decode() == row['raw_declaration']
        assert hashlib.sha256(old).hexdigest() == row['raw_declaration_sha256']
        z = one_decl(path, name)
        # Proof elaboration repairs are reviewed against the full retained raw
        # declaration; no equality of draft/final file hashes is fabricated.
        out.append(binding(z, path) | {'raw_signature': header(path, name),
            'original_raw_signature': row['raw_signature'], 'original_blind_row': row,
            'original_packet': 'blind-readbacks-source.json',
            'original_packet_sha256': sha(b / 'blind-readbacks-source.json'),
            'blind_original_path': str(original), 'blind_original_sha256': row['source_sha256'],
            'en': row['readback']['en'], 'zh_Hans': row['readback']['zh-Hans'],
            'ja': row['readback']['ja'], 'proof_notes': row.get('proof_notes'),
            'quotation': None, 'fresh_compiler_binder_review_required': True})
    for path in fresh_paths:
        parsed = [z for z in read('syntax-boundaries.json') if z['file'] == path]
        bound = [z for z in out if z['path'] == path]
        assert {z['nameText'] for z in parsed} == {z['userName'].split('.')[-1] for z in bound}
        assert len(parsed) == len(bound), path
    old = json.loads(HELPER_PACKET.read_text())['declarations']
    reused = next(z for z in old if z['userName'] == coord_helper)
    current = one_decl(coord, coord_helper)
    assert reused['source_sha256'] == sha(w / coord)
    assert reused['compiler_type'] == current['elaboratedType']
    out.append(reused | binding(current, coord) | {
        'reused_from': str(HELPER_PACKET.relative_to(w)),
        'reused_packet_sha256': sha(HELPER_PACKET),
        'reuse_basis': 'Same module, original userName, exact source hash and compiler type.'})
    old_parent = json.loads(TARGET_PACKET.read_text())[parent]
    old_graph = read('root-graph-before.json')
    node = next(z for z in old_graph['nodes'] if z.get('theorem_name') == parent)
    assert node['formal_statement'] == read('platform-before-parent.json')['formal_statement']
    out.append(binding(one_decl(source, parent), source) | {
        'en': old_parent['en'], 'zh_Hans': old_parent['zh'], 'ja': old_parent['ja'],
        'reused_from': str(TARGET_PACKET.relative_to(w)),
        'reused_packet_sha256': sha(TARGET_PACKET),
        'historical_platform_formal_statement': node['formal_statement'],
        'reuse_basis': 'Original blind parent meaning; exact platform statement retained.',
        'quotation': None})
    audit_path = b / 'compiler-readback-type-review.json'
    if audit_path.exists():
        audit = read(audit_path.name)
        assert audit['passed'] and audit['compiler_evidence']['graph_sha256'] == sha(b / 'decl_graph.jsonl')
        by_name = {z['declaration']: z for z in out}
        for row in audit['declarations']:
            correction = row.get('corrected_trilingual_statement')
            if correction:
                entry = by_name[row['compiler_name']]
                entry['superseded_blind_statements'] = {k: entry[k] for k in ['en', 'zh_Hans', 'ja']}
                entry.update(correction)
                entry['compiler_readback_correction'] = audit_path.name
    assert len(out) == len({z['declaration'] for z in out}) == 20
    save('final-readbacks.json', {'declarations': out, 'blind_readback': True,
        'compiler_bound': True, 'quotations_separate': True,
        'fresh_binder_review_count': 18, 'reused_rows': 2})


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


def rename_raw(path, name, replacement):
    span = syntax(path, name)
    raw = (w / path).read_bytes()
    ns, ne = span['nameRange']['start']['offset'], span['nameRange']['end']['offset']
    assert raw[ns:ne].decode() == name.split('.')[-1]
    return (raw[:ns] + replacement.encode() + raw[ne:]).decode()


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


def generate():
    bind()
    g = graph()
    assert len([z for z in g if z['module'] == module(definition) and z['startLine'] > 0]) == 7
    adapters = [z for z in g if z['module'] == module(adapter) and z['startLine'] > 0]
    assert len(adapters) == 6 and composer in {z['name'] for z in adapters}
    reached = reached_from([parent])
    authored = {z['name'] for z in g if z['module'] in {module(p) for p in fresh_paths}
                and z['startLine'] > 0}
    assert len(authored) == 18 and authored <= reached
    assert coord_helper in reached
    save('consumer-closure.json', {'root': parent, 'all_authored_declarations_consumed': True,
        'declarations': sorted(authored), 'reused_helper': coord_helper,
        'new_mathematical_children': children, 'only_remaining_open_child': open_child})
    code = (w / definition).read_text()
    imports, _ = split_imports(code)
    assert imports and all(x.startswith(('import Definitions.', 'import Mathlib.')) for x in imports)
    assert 'sorry' not in code and 'import Solutions.' not in code and 'import Theorems.' not in code
    write_source(u + 'UploadDefinition.lean', code)
    # Namespace rebinding retains every raw binder, actual body and local scope.
    # Original source is imported only into this local audit, never publication.
    assert code.count('namespace ' + pre.rstrip('.')) == 1
    assert code.count('end ' + pre.rstrip('.')) == 1
    alias = code.replace('namespace ' + pre.rstrip('.'), 'namespace PlatformDefinitionAudit', 1)
    alias = alias.replace('end ' + pre.rstrip('.'), 'end PlatformDefinitionAudit', 1)
    imports, body = split_imports(alias)
    def_pairs = ','.join('(`' + n + ', `PlatformDefinitionAudit.' + n.removeprefix(pre) + ')'
                         for n in def_names)
    audit = 'import Lean\nimport ' + module(definition) + '\n' + '\n'.join(imports)
    audit += '\n\nopen AbcAdaptation\nopen ' + pre.rstrip('.') + '\n\n' + body + '''

open Lean
run_meta do
  let pairs : Array (Name × Name) := PAIRS
  let mut rows : Array Json := #[]
  for (original, uploaded) in pairs do
    let a ← getConstInfo original
    let c ← getConstInfo uploaded
    unless ← Meta.isDefEq a.type c.type do throwError "Definition type differs: {original}"
    let aExpr ← Meta.mkConstWithFreshMVarLevels original
    let cExpr ← Meta.mkConstWithFreshMVarLevels uploaded
    unless ← Meta.withTransparency .all (Meta.isDefEq aExpr cExpr) do
      throwError "Definition body differs: {original}"
    let axs ← collectAxioms uploaded
    for ax in axs do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Unexpected definition axiom {ax}"
    rows := rows.push (Json.mkObj [("name",toJson original.toString),
      ("type_equal",Json.bool true),("body_equal",Json.bool true),
      ("axioms",toJson (axs.map toString))])
  IO.FS.writeFile "OUTPUT" (Json.pretty (Json.arr rows))
'''.replace('PAIRS', '#[' + def_pairs + ']').replace('OUTPUT', u + 'definition-type-audit.json')
    write_source(u + 'AuditDefinition.lean', audit)
    items = []
    for i, name in enumerate(children):
        path = child_path(name)
        imports, _ = split_imports((w / path).read_text())
        assert imports and all(x.startswith('import Definitions.') for x in imports)
        preamble = '\n'.join(imports) + '\n\nset_option autoImplicit false\n\nopen NumberField Module\nopen scoped Classical IntermediateField\nopen ' + pre.rstrip('.')
        statement = header(path, name, name) + ' := by sorry'
        assert statement.startswith('theorem ' + name + ' : ')
        item = {'theorem_name': name, 'preamble': preamble, 'formal_statement': statement}
        items.append(item)
        write_source(u + 'UploadType' + str(i) + '.lean', preamble + '\n\n' + statement)
    save('upload-problem-items.json', items)
    for name in closed_children:
        source_name = direct_source_names[name]
        direct = rename_raw(child_path(name), name, source_name)
        direct += '\n\nopen ' + pre.rstrip('.') + '\n\n'
        direct += header(child_path(name), name, 'solution') + ' := ' + source_name + '\n'
        imports, _ = split_imports(direct)
        assert all(x.startswith('import Definitions.') for x in imports)
        assert 'sorry' not in direct and 'import Theorems.' not in direct
        assert 'import Solutions.' not in direct
        write_source(direct_solutions[name], direct)
    retained = {z['name'] for z in g if z['name'] in reached
                and z['module'] in {module(adapter), module(coord)} and z['startLine'] > 0}
    retained_coord = {z['name'] for z in g if z['module'] == module(coord) and z['name'] in retained}
    assert retained_coord == {coord_helper}
    assert {z['name'] for z in adapters} <= retained
    all_imports, bodies, removals = [], [], []
    for path in [coord, adapter]:
        raw, dropped = pruned_module(path, retained)
        removals += [z | {'path': path} for z in dropped]
        imports, body = split_imports(raw)
        for imp in imports:
            if imp in {'import ' + module(coord), 'import ' + module(adapter)}:
                continue
            assert imp.startswith(('import Definitions.', 'import Mathlib.')), imp
            if imp not in all_imports:
                all_imports.append(imp)
        bodies.append(body)
    all_imports += ['import ' + module(child_path(n)) for n in children]
    before = read('platform-before-parent.json')
    formal = before['formal_statement']
    assert formal.startswith('theorem ' + parent + ' : ') and formal.endswith(' := by sorry')
    exact = formal.replace('theorem ' + parent, 'theorem solution', 1).removesuffix(' := by sorry')
    reduction = '\n'.join(all_imports) + '\n\n' + '\n\n'.join(bodies)
    reduction += '\n\nopen ' + pre.rstrip('.') + '\n\n' + exact + ' := by\n'
    reduction += '  exact ' + composer + '\n    ' + '\n    '.join(children) + '\n'
    assert 'sorry' not in reduction and 'import Solutions.' not in reduction
    assert 'import ' + module(source) not in reduction
    write_source(sol, reduction)
    # One local audit reparses the exact upload headers and all three standalone
    # proofs. Direct proofs retain private helpers and have distinct root aliases.
    audit_imports = ['import Lean']
    audit_bodies = []
    for name, path in [(n, direct_solutions[n]) for n in closed_children] + [(parent, sol)]:
        imports, body = split_imports((w / path).read_text())
        for imp in imports:
            if imp not in audit_imports:
                audit_imports.append(imp)
        rename = 'PlatformReduction' if name == parent else 'PlatformDirect' + str(closed_children.index(name))
        assert body.count('theorem solution ') == 1
        body = body.replace('theorem solution ', 'theorem ' + rename + ' ', 1)
        audit_bodies.append(body)
    type_audit = '\n'.join(audit_imports) + '\n\n' + '\n\n'.join(audit_bodies)
    type_audit += '\n\nopen ' + pre.rstrip('.') + '\n'
    for i, item in enumerate(items):
        name = item['theorem_name']
        annotation = item['formal_statement'].replace('theorem ' + name,
            'theorem PlatformUploadType' + str(i), 1).removesuffix(' := by sorry')
        type_audit += '\n' + annotation + ' := ' + name + '\n'
    parent_annotation = formal.replace('theorem ' + parent, 'theorem PlatformOriginalParentType', 1).removesuffix(' := by sorry')
    type_audit += '\n' + parent_annotation + ' := PlatformReduction\n'
    type_audit += '\n' + header(source, parent, 'PlatformSourceParentType') + ' := PlatformReduction\n'
    pairs = [(n, 'PlatformUploadType' + str(i), n == open_child) for i, n in enumerate(children)]
    pairs += [(n, 'PlatformDirect' + str(i), False) for i, n in enumerate(closed_children)]
    pairs += [('PlatformOriginalParentType', 'PlatformReduction', True),
              ('PlatformSourceParentType', 'PlatformReduction', True)]
    pairs_lean = '#[' + ','.join('(`' + a + ', `' + c + ', ' + str(s).lower() + ')'
                                for a, c, s in pairs) + ']'
    type_audit += '''
open Lean
run_meta do
  let pairs : Array (Name × Name × Bool) := PAIRS
  let mut rows : Array Json := #[]
  for (original, uploaded, expectedSorry) in pairs do
    let a ← getConstInfo original
    let c ← getConstInfo uploaded
    unless ← Meta.isDefEq a.type c.type do throwError "Exact uploaded/source type differs: {original}"
    let axs ← collectAxioms uploaded
    unless axs.contains `sorryAx == expectedSorry do throwError "Unexpected proof debt: {uploaded}"
    for ax in axs do
      unless (#[`propext, `Classical.choice, `Quot.sound].contains ax ||
          (expectedSorry && ax == `sorryAx)) do throwError "Unexpected axiom {ax}"
    rows := rows.push (Json.mkObj [("original",toJson original.toString),
      ("checked",toJson uploaded.toString),("type_equal",Json.bool true),
      ("expected_sorry",Json.bool expectedSorry),("axioms",toJson (axs.map toString))])
  IO.FS.writeFile "OUTPUT" (Json.pretty (Json.arr rows))
'''.replace('PAIRS', pairs_lean).replace('OUTPUT', u + 'type-audit.json')
    write_source(u + 'AuditSolution.lean', type_audit)
    save('solution-source-closure.json', {'source': sol, 'source_sha256': sha(w / sol),
        'graph_sha256': sha(b / 'decl_graph.jsonl'), 'parser_sha256': sha(b / 'syntax-boundaries.json'),
        'source_hashes': {p: sha(w / p) for p in fresh_paths + [source, coord]},
        'retained_helpers': sorted(retained), 'removed_whole_commands': removals,
        'parent_imports': all_imports, 'only_parent_mathematical_imports': children,
        'direct_source_hashes': {n: sha(w / p) for n, p in direct_solutions.items()},
        'direct_proofs_have_no_theorem_imports': True, 'no_solutions_import': True,
        'new_definition': definition_name, 'new_children': children,
        'remaining_open_frontier_replacement': {parent: open_child}})
    save('generated-source-hashes.json', generated_hashes())


def generated_hashes():
    paths = [sol, *direct_solutions.values(), u + 'UploadDefinition.lean',
             u + 'AuditDefinition.lean', u + 'AuditSolution.lean']
    paths += [u + 'UploadType' + str(i) + '.lean' for i in range(3)]
    return {p: sha(w / p) for p in paths}


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


def receipt_plan():
    plan = []
    for path in fresh_paths + [source]:
        stem = Path(path).stem.removeprefix('Def_').removeprefix('Source_')
        for suffix in ['leaf', 'artifact']:
            plan.append((stem + '-' + suffix, path, False, suffix == 'artifact'))
    plan += [
        ('closed-axioms-review', closed_checks, True, False),
        ('reduction-axioms-leaf', reduction_checks, False, False),
        ('source-graph-leaf', u + 'ExtractConductorGraph.lean', False, False),
        ('syntax-leaf', u + 'ExtractConductorSyntax.lean', False, False),
        ('all-constants-leaf', u + 'AuditAllConstants.lean', False, False),
        ('solution-leaf', sol, False, False),
        ('types-leaf', u + 'AuditSolution.lean', False, False),
        ('upload-definition-leaf', u + 'UploadDefinition.lean', False, False),
        ('definition-types-leaf', u + 'AuditDefinition.lean', False, False),
        ('production-gates-review', u + 'ProductionGates.lean', True, False),
        ('consumer-review', u + 'ChecksConductorConsumer.lean', True, False)]
    plan += [('direct-' + n.removeprefix(pre) + '-leaf', p, False, False)
             for n, p in direct_solutions.items()]
    plan += [('upload-type-' + str(i) + '-leaf', u + 'UploadType' + str(i) + '.lean', False, False)
             for i in range(3)]
    return plan


def preflight_definition():
    """Definition publication requires its own closed audit before any API write."""
    jobs = [checked(definition_name + '-leaf', definition),
            checked(definition_name + '-artifact', definition, artifact=True),
            checked('closed-axioms-review', closed_checks, review=True),
            checked('upload-definition-leaf', u + 'UploadDefinition.lean'),
            checked('definition-types-leaf', u + 'AuditDefinition.lean')]
    assert (b / 'UploadDefinition.lean').read_bytes() == (w / definition).read_bytes()
    audit = read('definition-type-audit.json')
    assert len(audit) == 7 and {z['name'] for z in audit} == set(def_names)
    assert all(z['type_equal'] and z['body_equal'] and set(z['axioms']) <= STANDARD for z in audit)
    return jobs


def preflight():
    jobs = [checked(*item) for item in receipt_plan()]
    preflight_definition()
    for tag in ['source-graph-leaf', 'syntax-leaf', 'all-constants-leaf', 'production-gates-review']:
        hashes = read(tag + '-result.json')['request']['worktree_manifest']['input_hashes']
        assert all(hashes[p] == sha(w / p) for p in fresh_paths + [source, coord]), tag
    hashes = read('production-gates-review-result.json')['request']['worktree_manifest']['input_hashes']
    assert all(hashes[p] == sha(w / p) for p in own)
    consumer = read('consumer-config.json')
    assert consumer['ci_tag'] == 'consumer-review' and consumer['review'] is True
    assert consumer['source'] == u + 'ChecksConductorConsumer.lean'
    assert consumer['expected_sorryAx'] is False and consumer['parent_still_open_expected']
    assert consumer['actual_consumer'] == pre + 'canonicalEstimate_of_belyi_children'
    assert consumer['explicit_remaining_child'] == 'BelyiActualFieldConductorExtension'
    assert consumer['source_path'] == 'Definitions/Def_FermatCanonicalBelyiComposition.lean'
    assert consumer['source_sha256'] == sha(w / consumer['source_path'])
    consumer_hashes = read('consumer-review-result.json')['request']['worktree_manifest']['input_hashes']
    assert all(consumer_hashes[p] == sha(w / p) for p in
               [consumer['source_path'], adapter, definition] + [child_path(n) for n in closed_children])
    consumer_code = (w / consumer['source']).read_text()
    assert 'import ' + module(source) not in consumer_code
    assert 'import ' + module(child_path(open_child)) not in consumer_code
    assert '(belyiDifferentConductorComparison_of_exact_children hExtension\n      belyiActualFieldDifferentTower tripodGeneratorConductorIdentity) hConductor' in consumer_code
    assert 'sorryAx' not in (read('consumer-review-result.json')['result'].get('stdout', '') +
                             read('consumer-review-result.json')['result'].get('stderr', ''))
    gate_imports = {line.removeprefix('import ') for line in (b / 'ProductionGates.lean').read_text().splitlines()
                    if line.startswith('import ')}
    assert gate_imports == {'ArithmeticTeichmullerSpaces.Prologue.Audit.ImportAudit',
        'ArithmeticTeichmullerSpaces.Act1Scene1', 'ArithmeticTeichmullerSpaces.Prologue.Audit.AxiomAudit'}
    rows = read('all-module-axioms.json')
    expected = {z['name'] for z in graph() if z['module'] in {module(p) for p in fresh_paths + [source]}}
    by_name = {z['name']: z for z in rows}
    assert expected <= set(by_name)
    # Every generated auxiliary is audited too. Only the actual open extension
    # and original parent module may contain the expected admitted child debt.
    for name in expected:
        z = by_name[name]
        mod = next(g['module'] for g in graph() if g['name'] == name)
        permitted = mod in {module(child_path(open_child)), module(source)}
        assert set(z['axioms']) <= STANDARD | ({'sorryAx'} if permitted else set()), name
    assert 'sorryAx' in by_name[open_child]['axioms']
    assert 'sorryAx' in by_name[parent]['axioms']
    assert all('sorryAx' not in by_name[n]['axioms'] for n in def_names + closed_children + [composer])
    compiled = {z['name']: z for z in graph()}
    actual_child_refs = {n for n in compiled[parent]['valueDeps'] if n in compiled
                        and compiled[n]['module'].startswith('Theorems.')
                        and compiled[n]['startLine'] > 0}
    assert actual_child_refs == set(children)
    span = syntax(source, parent)
    parent_body = (w / source).read_bytes()[span['valStart']['offset']:span['declEnd']['offset']].decode()
    assert ' '.join(parent_body.split()) == (
        ':= by exact belyiDifferentConductorComparison_of_exact_children '
        'belyiActualFieldConductorExtension belyiActualFieldDifferentTower tripodGeneratorConductorIdentity')
    audit = read('type-audit.json')
    assert len(audit) == 7 and all(z['type_equal'] for z in audit)
    expected_pairs = {(n, 'PlatformUploadType' + str(i), n == open_child) for i, n in enumerate(children)}
    expected_pairs |= {(n, 'PlatformDirect' + str(i), False) for i, n in enumerate(closed_children)}
    expected_pairs |= {('PlatformOriginalParentType', 'PlatformReduction', True),
                       ('PlatformSourceParentType', 'PlatformReduction', True)}
    assert {(z['original'], z['checked'], z['expected_sorry']) for z in audit} == expected_pairs
    for z in audit:
        assert ('sorryAx' in z['axioms']) == z['expected_sorry']
        assert set(z['axioms']) <= STANDARD | ({'sorryAx'} if z['expected_sorry'] else set())
    items = read('upload-problem-items.json')
    for i, item in enumerate(items):
        assert item['theorem_name'] == children[i]
        assert item['formal_statement'] == header(child_path(children[i]), children[i], children[i]) + ' := by sorry'
        assert (b / ('UploadType' + str(i) + '.lean')).read_text() == item['preamble'] + '\n\n' + item['formal_statement'] + '\n'
    assert len(items) == 3
    rb = read('final-readbacks.json')['declarations']
    assert len(rb) == 20 and all(z['source_sha256'] == sha(w / z['path']) for z in rb)
    fresh = {z['declaration']: z for z in rb if z['path'] in fresh_paths}
    review = read('compiler-readback-type-review.json')
    assert review['passed'] and review['compiler_evidence']['graph_sha256'] == sha(b / 'decl_graph.jsonl')
    assert len(review['declarations']) == 18
    assert {z['compiler_name'] for z in review['declarations']} == set(fresh)
    assert {z['path']: z['sha256'] for z in review['original_packets']} == {
        'blind-readbacks-source.json': sha(b / 'blind-readbacks-source.json')}
    for z in review['declarations']:
        row = fresh[z['compiler_name']]
        assert z['passed'] and z['compiler_type'] == row['compiler_type']
        assert z['current_source']['sha256'] == row['source_sha256']
        if z.get('corrected_trilingual_statement'):
            assert all(row[k] == z['corrected_trilingual_statement'][k] for k in ['en', 'zh_Hans', 'ja'])
    closure = read('solution-source-closure.json')
    assert closure['graph_sha256'] == sha(b / 'decl_graph.jsonl')
    assert closure['parser_sha256'] == sha(b / 'syntax-boundaries.json')
    assert closure['source_sha256'] == sha(w / sol)
    assert all(closure['source_hashes'][p] == sha(w / p) for p in fresh_paths + [source, coord])
    assert read('consumer-closure.json')['all_authored_declarations_consumed']
    assert all('sorry' not in (w / p).read_text() for p in [sol, *direct_solutions.values()])
    assert generated_hashes() == read('generated-source-hashes.json')
    delivery_review = read('independent-delivery-review.json')
    assert delivery_review['passed'] and delivery_review['blockers'] == []
    assert delivery_review['source_ledger_passed'] and delivery_review['all_new_outputs_have_actual_consumers']
    assert delivery_review['source_ledger_sha256'] == sha(r / 'ArithmeticTeichmullerSpaces/SOURCE_LEDGER.md')
    assert delivery_review['generated_source_hashes'] == generated_hashes()
    assert {z['job_id'] for z in jobs} <= set(delivery_review['compiler_checks'])
    subprocess.run(['git', 'diff', '--check'], cwd=r, check=True)
    validation = {'passed': True, 'original_parent_type_equal': True,
        'all_three_child_types_equal': True, 'seven_definition_types_and_bodies_equal': True,
        'readbacks': 20, 'fresh_compiler_binder_reviews': 18,
        'owned_source_hashes': {p: sha(w / p) for p in own},
        'generated_source_hashes': generated_hashes(), 'compiler_checks': [z['job_id'] for z in jobs],
        'new_definition': definition_name, 'new_children': children,
        'closed_direct_children': closed_children, 'only_remaining_open_child': open_child,
        'independent_delivery_review_sha256': sha(b / 'independent-delivery-review.json')}
    save('delivery-validation.json', validation)
    required_evidence = [tag + '-result.json' for tag, _, _, _ in receipt_plan()]
    required_evidence += ['decl_graph.jsonl', 'syntax-boundaries.json',
        'all-module-axioms.json', 'type-audit.json', 'definition-type-audit.json',
        'blind-readbacks-source.json', 'final-readbacks.json',
        'compiler-readback-type-review.json', 'independent-delivery-review.json',
        'consumer-closure.json', 'consumer-config.json', 'solution-source-closure.json',
        'generated-source-hashes.json', 'delivery-validation.json']
    return {'validation': validation, 'owned_sources': own,
            'required_jobs': jobs, 'required_evidence': required_evidence}


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


def metadata_inputs():
    quote = (b / 'quotation.md').read_text().strip()
    source_text = (b / 'source-description.txt').read_text().strip()
    assert quote and source_text
    return quote, source_text, read('final-readbacks.json')['declarations']


def publish():
    preflight()
    api, protocol = load_protocol()
    quote, source_text, rb = metadata_inputs()
    before = read('platform-before-parent.json')
    ident = before['theorem_id']
    assert before['theorem_name'] == parent and before['status'] == 'Open'
    assert before['visibility'] == 'private' and before['mathlib_rev'] == ENV
    baseline = read('root-graph-before.json')
    assert baseline['mathematical_closure_complete']
    assert not (set(children) & {z.get('theorem_name') for z in baseline['nodes']})
    assert read('root-frontier-before.json')['total'] == 17
    assert read('registry-before.json')['graph_counts'] == EXPECTED_BEFORE
    current = api.request('/theorems/' + ident)
    assert current['formal_statement'] == before['formal_statement']
    assert current['preamble'] == before['preamble']
    preflight_definition()
    selected = [z for z in rb if z['userName'] in def_names]
    assert len(selected) == 7
    payload = {'definition_name': definition_name,
        'definition_title': 'Actual finite-set conductors and the Belyi image-field different',
        'definition': (b / 'UploadDefinition.lean').read_text(),
        'natural_language_statement': quote + '\n\n' + prose(selected),
        'source': source_text, 'env': ENV, 'private': True,
        'tags': ['abc-conjecture', 'arithmetic-geometry']}
    published = publication(protocol, 'def-' + definition_name, '/submit-definition', payload)
    assert len(published) == 1
    definition_id = published[0]['theorem_id']
    save('published-definition-id.json', {'id': definition_id, 'name': definition_name})
    d = api.request('/theorems/' + definition_id)
    assert d['status'] == 'Definition' and d['visibility'] == 'private' and d['mathlib_rev'] == ENV
    definition_readbacks = [d[key] for key in ['definition', 'definitions'] if d.get(key)]
    assert definition_readbacks, 'Definition GET response contains no nonempty code field'
    assert all(code == payload['definition'] for code in definition_readbacks)
    save('platform-after-definition.json', d)
    titles = ['Conductor extension along the actual Belyi point-field inclusion',
              'Discriminant tower through the actual Belyi image field',
              'Conductor identity for the actual three tripod generators']
    items = read('upload-problem-items.json')
    for item, title in zip(items, titles):
        selected = [z for z in rb if z['userName'] == item['theorem_name']]
        assert len(selected) == 1
        item.update(theorem_title=title, natural_language_statement=quote + '\n\n' + prose(selected),
                    source=source_text, tags=['abc-conjecture', 'arithmetic-geometry'])
    published = publication(protocol, 'different-conductor-children', '/submit-problem',
                            {'problems': items, 'env': ENV, 'private': True})
    assert len(published) == 3
    ids = {z['theorem_name']: z['theorem_id'] for z in published}
    assert set(ids) == set(children)
    save('published-child-ids.json', ids)
    # All three records are published as Open before either closed proof is
    # verified. On a resumed run, only locally recorded ACCEPTED children may
    # already be Proved; this never creates a second publication.
    for item in items:
        name = item['theorem_name']
        z = api.request('/theorems/' + ids[name])
        assert z['theorem_name'] == name and z['visibility'] == 'private' and z['mathlib_rev'] == ENV
        expected = {'Open'}
        tag = 'prove-' + name.removeprefix(pre)
        if name in closed_children and (b / (tag + '-verify-result.json')).exists():
            if read(tag + '-verify-result.json')['status'] == 'ACCEPTED':
                expected.add('Proved')
        assert z['status'] in expected
        assert z['formal_statement'] == item['formal_statement'] and z['preamble'] == item['preamble']
        assert z['natural_language_statement'] == item['natural_language_statement']
        save('platform-before-proof-' + name.removeprefix(pre) + '.json', z)
    direct_results = {}
    for name in closed_children:
        selected = [z for z in rb if z['userName'] == name]
        explanation = quote + '\n\n' + prose(selected) + '\n\n' + source_text
        explanation += '\n\nThe submitted standalone file reuses the source proof and its private helper. It imports only existing Definitions and has no theorem import. The proof has only standard Lean axioms. This closes this exact child; the separate conductor-extension child remains Open.'
        result = verification(protocol, 'prove-' + name.removeprefix(pre), ids[name],
                              direct_solutions[name], explanation)
        assert result['status'] == 'ACCEPTED'
        direct_results[name] = result
        state = api.request('/theorems/' + ids[name])
        assert state['status'] == 'Proved'
        save('platform-after-' + name.removeprefix(pre) + '.json', state)
    selected = [z for z in rb if z['userName'] == parent]
    assert len(selected) == 1
    explanation = quote + '\n\n' + prose(selected) + '\n\n' + source_text
    explanation += '\n\nThe exact original comparison is composed from the three explicit child statements. The closed adapters establish regularity for every member of the actual coordinate-ring generator set, identify its actual finite-set conductor, and map all three actual tripod generators through the image-field inclusion. The tower child uses the full point field and the actual image field with their distinct degrees. The conductor child gives the remaining numerical inequality; the composer chooses additive constant zero. The tower and tripod identity children are ACCEPTED direct source proofs. Exactly the conductor-extension child remains Open. The parent, canonicalEstimate and root remain Open.'
    assert len(explanation) <= 50000
    result = verification(protocol, 'reduce-parent', ident, sol, explanation)
    assert result['status'] == 'SKETCH_ACCEPTED'
    patch = {'natural_language_statement': quote + '\n\n' + prose(selected), 'source': source_text}
    save('parent-metadata-patch-request.json', patch)
    current = api.request('/theorems/' + ident)
    assert current['formal_statement'] == before['formal_statement'] and current['preamble'] == before['preamble']
    if not all(current.get(k) == v for k, v in patch.items()):
        save('parent-metadata-patch-response.json', api.request('/theorems/' + ident, patch, 'PATCH'))
    for name, tid in [(parent, ident)] + list(ids.items()):
        state = api.request('/theorems/' + tid)
        assert state['theorem_name'] == name and state['visibility'] == 'private' and state['mathlib_rev'] == ENV
        assert state['status'] == ('Proved' if name in closed_children else 'Open')
        assert not state.get('deprecated', False) and not state.get('is_deprecated', False)
        if name == parent:
            assert state['formal_statement'] == before['formal_statement'] and state['preamble'] == before['preamble']
            assert all(state[k] == v for k, v in patch.items())
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
    verify_graph(baseline, after, ids, definition_id, result, direct_results)
    print('Two child proofs ACCEPTED; exact three-child reduction SKETCH_ACCEPTED; conductor extension remains Open.', flush=True)


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


def definition_code(row):
    values = [row[key] for key in ['definition', 'definitions'] if row.get(key)]
    assert values, ('Definition record has no nonempty source code', row.get('theorem_id'))
    assert all(value == values[0] for value in values)
    return values[0]


def retained_definitions(before, after, definition_id):
    """Hidden graph Definitions need exact saved GET evidence, never deletion."""
    old = {z['theorem_id']: z for z in before['nodes'] if z.get('status') == 'Definition'}
    current = {z['theorem_id']: z for z in after['nodes'] if z.get('status') == 'Definition'}
    assert set(current) - set(old) == {definition_id}
    missing = set(old) - set(current)
    retention = read('definition-retention-readbacks.json') if missing else {'definitions': []}
    rows = retention['definitions']
    saved = {z['theorem_id']: z for z in rows}
    assert len(saved) == len(rows) and set(saved) == missing
    evidence = []
    for ident, previous in old.items():
        visible = ident in current
        row = current[ident] if visible else saved[ident]
        assert row['theorem_id'] == ident and row['theorem_name'] == previous['theorem_name']
        assert row['status'] == 'Definition'
        assert row['formal_statement'] == previous['formal_statement']
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
    return {'existing_definitions': evidence, 'missing_from_graph_ids': sorted(missing),
            'retention_readbacks_sha256': sha(b / 'definition-retention-readbacks.json') if missing else None,
            'new_definition_id': definition_id}


def verify_graph(before, after, ids, definition_id, reduction, direct_results):
    """Record observed graph deltas; no registry or pending-database mutation."""
    old = summary_without_direct_proof_nodes(before, set())
    new = summary_without_direct_proof_nodes(after, {z['id'] for z in direct_results.values()})
    assert before['mathematical_closure_complete'] and after['mathematical_closure_complete']
    assert not after.get('has_hidden_deprecated') and not after.get('has_hidden_deprecated_sketches')
    old_nodes = {z['theorem_name']: z for z in before['nodes'] if z['node_type'] == 'theorem' and z['status'] != 'Definition'}
    new_nodes = {z['theorem_name']: z for z in after['nodes'] if z['node_type'] == 'theorem' and z['status'] != 'Definition'}
    assert set(new_nodes) - set(old_nodes) == set(children)
    assert set(old_nodes) <= set(new_nodes)
    for name, node in old_nodes.items():
        current = new_nodes[name]
        assert current['theorem_id'] == node['theorem_id'] and current['status'] == node['status']
        assert current['formal_statement'] == node['formal_statement']
        for key in ['deprecated', 'is_deprecated']:
            assert current.get(key) == node.get(key)
    assert new_nodes[parent]['status'] == 'Open'
    assert new_nodes['AbcAdaptation.Tripod.Fermat.canonicalEstimate']['status'] == 'Open'
    assert new_nodes['abc.goal.lt_constant_mul_fix']['status'] == 'Open'
    definition_retention = retained_definitions(before, after, definition_id)
    sketches = [z for z in after['nodes'] if z['node_type'] == 'sketch'
                and z['submission_id'] == reduction['id']]
    assert len(sketches) == 1 and sketches[0]['status'] == 'SKETCH_ACCEPTED'
    assert sketches[0]['parent_theorem_id'] == old_nodes[parent]['theorem_id']
    actual = {e['source'] for e in after['edges'] if e['kind'] == 'sketch'
              and e['target'] == sketches[0]['node_id'] and e['source'] in set(ids.values())}
    all_math_ids = {z['theorem_id'] for z in new_nodes.values()}
    all_actual = {e['source'] for e in after['edges'] if e['kind'] == 'sketch'
                  and e['target'] == sketches[0]['node_id'] and e['source'] in all_math_ids}
    assert actual == all_actual == set(ids.values())
    # Direct proofs with no theorem imports may be absent from sketch nodes or
    # present with zero mathematical dependencies. They do not count as reductions.
    for name, result in direct_results.items():
        assert result['status'] == 'ACCEPTED'
        for sketch in [z for z in after['nodes'] if z['node_type'] == 'sketch'
                       and z['submission_id'] == result['id']]:
            deps = {e['source'] for e in after['edges'] if e['kind'] == 'sketch'
                    and e['target'] == sketch['node_id'] and e['source'] in all_math_ids}
            assert deps == set(), (name, deps)
    prior_reductions = {z['submission_id']: z for z in old['reductions']}
    current_reductions = {z['submission_id']: z for z in new['reductions']}
    assert set(current_reductions) - set(prior_reductions) == {reduction['id']}
    assert all(current_reductions[k] == v for k, v in prior_reductions.items())
    pairs = {(parent, name) for name in children}
    assert new['dependency_pairs'] - old['dependency_pairs'] == pairs
    assert old['dependency_pairs'] <= new['dependency_pairs']
    assert old['counts'] == {k: EXPECTED_BEFORE[k] for k in ['accepted_reductions', 'published_children', 'dependency_edges']}
    assert new['counts'] == {k: EXPECTED_AFTER[k] for k in ['accepted_reductions', 'published_children', 'dependency_edges']}
    bf, af = read('root-frontier-before.json'), read('root-frontier-after.json')
    assert bf['all_pages_fetched'] and af['all_pages_fetched']
    assert bf['total'] == af['total'] == 17
    assert {z['theorem_id'] for z in af['open_leaves']} == ({z['theorem_id'] for z in bf['open_leaves']}
        - {old_nodes[parent]['theorem_id']}) | {ids[open_child]}
    registry = read('registry-before.json')
    direct = {z['name'] for z in registry['direct_closed_proofs']}
    assert len(direct) == 38 and not direct.intersection(closed_children)
    assert all(new_nodes[n]['status'] == 'Proved' for n in direct | set(closed_children))
    save('graph-count-evidence.json', {'before': EXPECTED_BEFORE, 'after': EXPECTED_AFTER,
        'new_definition_id': definition_id, 'published_child_ids': ids,
        'new_reductions': [current_reductions[reduction['id']]],
        'new_dependencies': [[parent, n] for n in children],
        'direct_closed_proofs': [{'name': n, 'submission_id': z['id'], 'status': 'ACCEPTED',
                                 'mathematical_dependencies': []} for n, z in direct_results.items()],
        'definition_retention': definition_retention,
        'remaining_open_child': open_child, 'existing_nodes_preserved': True,
        'existing_reductions_preserved': True, 'deprecations': [],
        'Fermat_route_preserved': True, 'parent': 'Open', 'canonicalEstimate': 'Open', 'root': 'Open'})
    save('direct-graph-evidence.json', {'parent_id': old_nodes[parent]['theorem_id'],
        'submission_id': reduction['id'], 'actual_child_ids': sorted(all_actual),
        'expected_child_ids': sorted(ids.values()), 'only_open_child': ids[open_child],
        'closed_child_ids': [ids[n] for n in closed_children], 'parent_and_root_open': True})


if __name__ == '__main__':
    {'bind': bind, 'generate': generate, 'preflight': preflight, 'publish': publish}[sys.argv[1]]()
