"""Order/index delivery gates. Importing this module has no external effects."""
from pathlib import Path
import hashlib
import json
import math
import re

ROOT_DIR = Path('/home/admin-wsl/Coq/abc')
WORKSPACE = ROOT_DIR / 'prove2me_workspace'
UNIT = 'order-index-sourceproof-20261114'
UNIT_REL = '.local/adaptation/' + UNIT + '/'
EVIDENCE = WORKSPACE / UNIT_REL
PREFIX = 'AbcAdaptation.Tripod.Fermat.Proper.'
ENV = '0df444a360eaa60ab8c11dca51a86af692955474'
PIN = '9ce4d3f793d3bc831f2fc7214b7dbad90ea012d8'
ROOT_ID = 'e33ff731-60a7-43ef-87ae-c12aeba23cb5'
ROOT_NAME = 'abc.goal.lt_constant_mul_fix'
MODULES = ['FermatNoncriticalOrderSource']
TARGETS = ['noncriticalPolynomialOrderAtRegularPoint', 'noncriticalPolynomialOrderAtPole',
           'noncriticalInverseRamification']
ANCESTORS = ['noncriticalElementaryCompositionRamification', 'noncriticalCompositionRamification']
HELPERS = [PREFIX + 'Place.' + n for n in ['noncritical_ord_eq_zero_of_residue_ne_zero',
                                         'noncritical_residue_eq_zero_of_ord_pos']]
PUBLIC_READBACK_NAMES = set(HELPERS + [PREFIX + n for n in TARGETS])
IDS_PATH = WORKSPACE / '.local/adaptation/fermat-noncritical-elementary-20261114/published-child-ids.json'


def read(name):
    return json.loads((EVIDENCE / name).read_text())


def save(name, value):
    path = EVIDENCE / name
    temporary = path.with_name(path.name + '.tmp')
    temporary.write_text(json.dumps(value, ensure_ascii=False, indent=2) + '\n')
    temporary.replace(path)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def theorem_path(name):
    return 'Theorems/Thm_' + (PREFIX + name).replace('.', '_') + '.lean'


def solution_path(name):
    return UNIT_REL + 'Solution_' + name + '.lean'


def lookup_input(inputs, relative):
    return inputs.get(relative, inputs.get(str(WORKSPACE / relative)))


def checked_receipt(check):
    tag, source = check['tag'], check['source']
    review, artifact = check.get('review', False), check.get('artifact', False)
    assert not (review and artifact), tag
    receipt = read(tag + '-result.json')
    assert receipt['status'] == 'succeeded', (tag, receipt['status'])
    request, result, resources = receipt['request'], receipt['result'], receipt['resources']
    assert result['exit_code'] == 0, tag
    assert request['workspace'] == str(WORKSPACE) and request['exclusive'] is True, tag
    params = {'args': [source, '-o', '.lake/build/lib/lean/' + source[:-5] + '.olean']} if artifact else {'source': source}
    assert request['parameters'] == params, (tag, request['parameters'])
    assert request['task_type'] == ('full' if artifact else 'review' if review else 'leaf'), tag
    assert request['target'] == ('module' if artifact else 'file'), tag
    assert request['worktree_manifest']['source_sha256'] == sha(WORKSPACE / source), tag
    snapshot = result['snapshot']
    assert snapshot['workspace_mode'] == 'exclusive_worktree' and snapshot['snapshot_id'] is None, tag
    assert result['actual_arguments'] == ['lean'] + (params['args'] if artifact else [source]), tag
    assert 'sorryAx' not in result.get('stdout', '') + result.get('stderr', ''), tag
    rss = resources.get('peak_rss_bytes')
    if request['task_type'] == 'leaf':
        assert rss is not None and rss <= 16 * 1024 ** 3, (tag, rss)
    cpu, user, system = (resources.get(k) for k in ['cpu_time_seconds', 'cpu_user_seconds', 'cpu_system_seconds'])
    if None not in [cpu, user, system]:
        assert math.isclose(cpu, user + system, abs_tol=0.1), tag
    if review:
        assert result['review']['passed'] is True, tag
    return receipt


def readback_rows():
    value = read('final-readbacks.json')
    return value['declarations'] if isinstance(value, dict) else value


def readback_prose(rows):
    assert rows
    for row in rows:
        for lang in ['en', 'zh_Hans', 'ja']:
            assert isinstance(row[lang], str) and row[lang].strip(), (row['declaration'], lang)
    return '\n\n'.join('**' + title + '**\n\n' + '\n\n'.join(
        '`' + row['declaration'] + '`\n\n' + row[lang] for row in rows)
        for lang, title in [('en', 'English'), ('zh_Hans', '简体中文'), ('ja', '日本語')])


def readback_compiler_bindings(rows, graph):
    bindings = []
    for row in rows:
        matches = [item for item in graph if item.get('userName', item['name']) == row['declaration'] or item['name'] == row['declaration']]
        assert len(matches) == 1, ('Readback compiler owner is not unique', row['declaration'])
        owner = matches[0]
        assert row.get('compiler_name', owner['name']) == owner['name']
        if row.get('elaboratedType') is not None:
            assert row['elaboratedType'] == owner['elaboratedType']
        if row.get('compiler_source_span') is not None:
            span = row['compiler_source_span']
            assert span == {'startLine': owner['startLine'], 'endLine': owner['endLine']}
        bindings.append({'declaration': row['declaration'], 'compiler_name': owner['name'],
                         'module': owner['module'], 'isPrivate': owner.get('isPrivate', False)})
    return bindings


def preflight():
    validation = read('sourceproof-validation.json')
    assert validation['passed'] is True and validation['exact_platform_types_equal'] is True
    definitions = {'Definitions/Def_' + mod + '.lean' for mod in MODULES}
    assert set(validation['definition_hashes']) == definitions
    assert set(validation['theorem_hashes']) == {PREFIX + n for n in TARGETS}
    assert set(validation['solution_hashes']) == {solution_path(n) for n in TARGETS}
    current = dict(validation['definition_hashes'])
    current.update({theorem_path(n): validation['theorem_hashes'][PREFIX + n] for n in TARGETS})
    current.update(validation['solution_hashes'])
    for relative, expected in current.items():
        assert sha(WORKSPACE / relative) == expected, relative
    assert sha(EVIDENCE / 'decl_graph.jsonl') == validation['declaration_graph_sha256']
    checks = validation['compiler_checks']
    assert checks and len({c['tag'] for c in checks}) == len(checks)
    receipts = [checked_receipt(c) for c in checks]
    modes = {(c['source'], c.get('review', False), c.get('artifact', False)) for c in checks}
    for source in definitions | {theorem_path(n) for n in TARGETS}:
        assert (source, False, False) in modes and (source, False, True) in modes, source
    for n in TARGETS:
        assert (solution_path(n), False, False) in modes
    review_sources = [c['source'] for c in checks if c.get('review')]
    own_checks = [s for s in review_sources if s.startswith('Solutions/Checks_')]
    assert own_checks and any(s.endswith('/AuditAllDefinitions.lean') for s in review_sources)
    assert any(s.endswith('/ProductionGates.lean') for s in review_sources)
    assert any('Extract' in Path(c['source']).name and 'Graph' in Path(c['source']).name for c in checks)
    assert any(Path(c['source']).name == 'ValidateExistingTypes.lean' for c in checks)
    assert read('existing-types-equal.json') is True
    # Final reviews bind the complete delivered proof unit to its current inputs.
    for check, receipt in zip(checks, receipts):
        if not check.get('review'):
            continue
        inputs = receipt['request']['worktree_manifest'].get('input_hashes', {})
        for relative, expected in current.items():
            if relative in validation['solution_hashes']:
                continue
            assert lookup_input(inputs, relative) == expected, (check['tag'], relative)
    for n in TARGETS:
        solution = (WORKSPACE / solution_path(n)).read_text()
        assert 'sorry' not in solution and 'admit' not in solution
        allowed = {'Theorems.Thm_' + (PREFIX + TARGETS[0]).replace('.', '_')} if n == TARGETS[2] else set()
        imports = [module for line in solution.splitlines() if line.startswith('import ') for module in line[7:].split()]
        assert all(not module.startswith(('Solutions.', 'Open.')) for module in imports), n
        assert {module for module in imports if module.startswith('Theorems.')} <= allowed, n
    context = EVIDENCE / 'published-child-context.json'
    if context.exists():
        values = json.loads(context.read_text())
        if isinstance(values, dict):
            values = values.get('theorems', [values] if values else [])
        assert isinstance(values, list)
        for item in values:
            assert item['theorem_name'] == PREFIX + TARGETS[0] and item['status'] == 'Proved'
            assert item['visibility'] == 'private' and item['mathlib_rev'] == ENV
    graph = [json.loads(line) for line in (EVIDENCE / 'decl_graph.jsonl').read_text().splitlines() if line.strip()]
    by_name = {row['name']: row for row in graph}
    assert len(by_name) == len(graph) and PUBLIC_READBACK_NAMES <= set(by_name)
    visited, todo = set(), [PREFIX + n for n in TARGETS]
    while todo:
        name = todo.pop()
        if name in visited:
            continue
        visited.add(name)
        assert name != 'sorryAx'
        if name in by_name:
            row = by_name[name]
            assert row['module'].startswith('Definitions.') or name in {PREFIX + n for n in TARGETS} or name.startswith('_private.'), name
            todo.extend(row.get('typeDeps', []) + row.get('valueDeps', []))
        elif name.startswith(('AbcAdaptation.', '_private.')):
            raise AssertionError(('Project dependency missing from proof closure', name))
    assert not any('sorryAx' in row.get('typeDeps', []) + row.get('valueDeps', []) for row in graph)
    rows = readback_rows()
    names = {row['declaration'] for row in rows}
    assert len(rows) == len(names) and PUBLIC_READBACK_NAMES <= names
    if 'readback_names' in validation:
        assert names == set(validation['readback_names'])
    else:
        # The private helper may be read back under a stable source name or its compiler name.
        assert all(name in PUBLIC_READBACK_NAMES or name.endswith('noncritical_exists_ramIdx_eq_mul_inv') for name in names)
    readback_prose(rows)
    readback_compiler_bindings(rows, graph)
    for row in rows:
        relative = row['path']
        assert relative in definitions | {theorem_path(n) for n in TARGETS}, relative
        # A parent-supplied independent readback receipt binds both array and object forms.
        if row.get('source_sha256') is not None:
            assert row['source_sha256'] == current[relative]
    raw = read('final-readbacks.json')
    inputs = raw.get('input_file_sha256', {}) if isinstance(raw, dict) else {}
    for relative, expected in current.items():
        if relative in validation['solution_hashes']:
            continue
        if inputs:
            assert lookup_input(inputs, relative) == expected
    if not inputs:
        assert validation.get('readbacks_sha256') == sha(EVIDENCE / 'final-readbacks.json'), 'Bind direct-array readbacks with validation.readbacks_sha256'
    source = read('source-consumer.json')
    assert source.get('reference_commit', source.get('pin')) == PIN
    scope = source.get('scope', {})
    assert scope.get('new_mathematical_Open_nodes', source.get('new_open_obligations', 0)) == 0
    assert scope.get('new_assumptions', 0) == 0
    assert source['producers'] and all(p.get('consumers') for p in source['producers'])
    link = read('source-ledger-link.json')
    assert sha(ROOT_DIR / link['production_ledger']) == link['production_ledger_sha256']
    ids = json.loads(IDS_PATH.read_text())
    assert set(ids) == {PREFIX + n for n in TARGETS}
    return validation, ids, rows


def publication_results(tag):
    submitted = read(tag + '-submit.json')
    assert not submitted.get('errors'), tag
    jobs = submitted.get('jobs') or [{'job_id': submitted['job_id']}]
    assert len(jobs) == 1
    results = []
    for job in jobs:
        result = read(tag + '-' + job['job_id'] + '-result.json')
        assert result['status'] == 'PUBLISHED' and result['visibility'] == 'private'
        assert result['id'] == job['job_id']
        results.append(result)
    return results


def graph_summary(graph):
    assert graph['root_id'] == ROOT_ID and graph['mathematical_closure_complete'] is True
    assert not graph.get('has_hidden_deprecated') and not graph.get('has_hidden_deprecated_sketches')
    mathematical = {n['theorem_id']: n for n in graph['nodes'] if n['node_type'] == 'theorem' and n['status'] != 'Definition'}
    assert mathematical[ROOT_ID]['theorem_name'] == ROOT_NAME
    assert all(not n.get('deprecated_at') for n in mathematical.values())
    for n in mathematical.values():
        if n.get('has_more_children'):
            assert n.get('missing_children') and all(e.get('hidden_by_definitions') is True for e in n['missing_children'])
    reductions, pairs = [], set()
    for node in graph['nodes']:
        if node['node_type'] != 'sketch':
            continue
        assert node['status'] in ['ACCEPTED', 'SKETCH_ACCEPTED'] and not node.get('deprecated_at')
        parent = node['parent_theorem_id']
        assert parent in mathematical
        assert any(e['kind'] == 'sketch' and e['source'] == node['node_id'] and e['target'] == parent for e in graph['edges'])
        children = sorted({mathematical[e['source']]['theorem_name'] for e in graph['edges']
                           if e['kind'] == 'sketch' and e['target'] == node['node_id'] and e['source'] in mathematical})
        assert children
        name = mathematical[parent]['theorem_name']
        reductions.append({'parent': name, 'children': children, 'submission_id': node['submission_id'], 'status': node['status']})
        pairs.update((name, child) for child in children)
    return {'mathematical': mathematical, 'reductions': reductions, 'dependency_pairs': pairs,
            'counts': {'accepted_reductions': len(reductions), 'published_children': len(mathematical) - 1,
                       'dependency_edges': len(pairs)}}


def compare_graphs(before_graph, after_graph, ids, before_frontier, after_frontier, accepted_inverse_proof=None):
    before, after = graph_summary(before_graph), graph_summary(after_graph)
    old = {n['theorem_name']: n for n in before['mathematical'].values()}
    new = {n['theorem_name']: n for n in after['mathematical'].values()}
    assert set(before['mathematical']) == set(after['mathematical'])
    inverse, regular = PREFIX + TARGETS[2], PREFIX + TARGETS[0]
    expected_pair = (inverse, regular)
    assert after['dependency_pairs'] - before['dependency_pairs'] == {expected_pair}
    assert not (before['dependency_pairs'] - after['dependency_pairs']), 'An existing dependency was removed'
    old_reductions = {edge['submission_id']: edge for edge in before['reductions']}
    new_reductions = {edge['submission_id']: edge for edge in after['reductions']}
    assert len(old_reductions) == len(before['reductions']) and len(new_reductions) == len(after['reductions'])
    assert set(old_reductions) < set(new_reductions), 'An existing reduction was removed'
    added_ids = set(new_reductions) - set(old_reductions)
    assert len(added_ids) == 1, 'Only the accepted inverse proof may add a dependency reduction'
    added = new_reductions[next(iter(added_ids))]
    if accepted_inverse_proof is None:
        accepted_inverse_proof = read('prove-' + TARGETS[2] + '-verify-result.json')
        submitted = read('prove-' + TARGETS[2] + '-verify-submit.json')
        assert accepted_inverse_proof['id'] == submitted['submission_id']
    assert accepted_inverse_proof['status'] == 'ACCEPTED'
    assert accepted_inverse_proof['theorem_id'] == ids[inverse]
    assert added == {'parent': inverse, 'children': [regular],
                     'submission_id': accepted_inverse_proof['id'], 'status': 'ACCEPTED'}
    assert new[inverse]['status'] == new[regular]['status'] == 'Proved'
    for submission_id, old_edge in old_reductions.items():
        edge = new_reductions[submission_id]
        assert (edge['parent'], edge['children']) == (old_edge['parent'], old_edge['children']), 'An existing reduction identity changed'
        if edge['status'] != old_edge['status']:
            assert old_edge['status'] == 'SKETCH_ACCEPTED' and edge['status'] == 'ACCEPTED'
            assert all(new[child]['status'] == 'Proved' for child in edge['children'])
    assert after['counts'] == {'accepted_reductions': before['counts']['accepted_reductions'] + 1,
                               'published_children': before['counts']['published_children'],
                               'dependency_edges': before['counts']['dependency_edges'] + 1}
    after['added_existing_child_dependency'] = {
        'parent': inverse, 'parent_theorem_id': ids[inverse],
        'child': regular, 'children': [regular], 'child_theorem_id': ids[regular],
        'submission_id': accepted_inverse_proof['id'], 'status': 'ACCEPTED',
        'parent_status': new[inverse]['status'], 'child_status': new[regular]['status'],
        'proof_type': 'prove', 'proof_receipt': UNIT_REL + 'prove-' + TARGETS[2] + '-verify-result.json'}
    targets = {PREFIX + n for n in TARGETS}
    for name in targets:
        assert old[name]['theorem_id'] == new[name]['theorem_id'] == ids[name]
        assert new[name]['status'] == 'Proved', (name, new[name]['status'])
    assert old[ROOT_NAME]['status'] != 'Proved' and new[ROOT_NAME]['status'] != 'Proved'
    # Accepted sketches can propagate proof status upward. Observe, never set, those statuses.
    eligible = {name for name, node in old.items() if node['status'] == 'Proved'} | targets
    while True:
        expanded = eligible | {edge['parent'] for edge in before['reductions'] if set(edge['children']) <= eligible}
        if expanded == eligible:
            break
        eligible = expanded
    changes = []
    for name, node in new.items():
        if node['status'] == old[name]['status']:
            continue
        assert old[name]['status'] == 'Open' and node['status'] == 'Proved' and name in eligible, name
        if name not in targets:
            assert any(e['parent'] == name and all(new[c]['status'] == 'Proved' for c in e['children']) for e in after['reductions']), name
        changes.append({'name': name, 'before': old[name]['status'], 'after': node['status'], 'direct': name in targets})
    frontiers = []
    for frontier, nodes in [(before_frontier, old), (after_frontier, new)]:
        rows = frontier['open_leaves']
        assert frontier['all_pages_fetched'] and len(rows) == frontier['total'] == len({r['theorem_id'] for r in rows})
        for row in rows:
            assert nodes[row['theorem_name']]['theorem_id'] == row['theorem_id']
            assert nodes[row['theorem_name']]['status'] == 'Open'
        frontiers.append({r['theorem_id'] for r in rows})
    prior_ids, final_ids = frontiers
    assert set(ids.values()) <= prior_ids and not (set(ids.values()) & final_ids)
    changed_ids = {new[row['name']]['theorem_id'] for row in changes}
    assert prior_ids - final_ids <= changed_ids, 'An unrelated frontier leaf disappeared'
    for ident in final_ids - prior_ids:
        name = after['mathematical'][ident]['theorem_name']
        assert name in eligible - targets and new[name]['status'] == 'Open'
        assert any(e['parent'] == name and all(new[c]['status'] == 'Proved' for c in e['children']) for e in after['reductions'])
    return before, after, new, changes


def ancestor_metadata(name, baseline):
    """Remove only obsolete proof-status text; preserve the reviewed mathematical statement."""
    assert name in ANCESTORS and baseline['theorem_name'] == PREFIX + name
    natural, source = baseline['natural_language_statement'], baseline['source']
    if name == ANCESTORS[0]:
        obsolete = [
            ' The body is exactly `by sorry`: this elementary chain-rule child is OPEN, and this statement is not an established theorem in this review.',
            '证明体恰为 `by sorry`：这个初等复合链式法则子义务尚未完成，本次审阅不能将该陈述视为已证定理。',
            '証明本体は正確に `by sorry` である。この初等合成の連鎖律に関する子課題は未解決であり、本審査では証明済みの定理として扱えない。',
        ]
        for sentence in obsolete:
            assert natural.count(sentence) == 1, ('Baseline status sentence changed; review preview', name)
            natural = natural.replace(sentence, '', 1)
        replacements = {
            'The actual single-elementary-map composition theorem remains Open; the parent combines source positivity and list induction.':
                'The existing accepted elementary-composition reduction consumes the three closed polynomial-order and inversion source proofs from order-index-sourceproof-20261114.',
            'The source polynomial/inversion/Möbius proof remains Open; no free map or chain-rule law is supplied.':
                'The regular-order, pole-order and inversion source proofs are supplied by those three closed children. The existing polynomial and Möbius composition proofs consume them. No free map or chain-rule law is supplied.',
        }
    else:
        replacements = {
            'Positivity, transcendence preservation, actual values and ramification multiplication for all elementary composites remain Open.':
                'The existing positivity proof and list induction consume the elementary composition theorem. Its three polynomial-order and inversion children have complete source proofs in order-index-sourceproof-20261114.',
        }
    for old, new in replacements.items():
        assert source.count(old) == 1, ('Baseline source status sentence changed; review preview', name)
        source = source.replace(old, new, 1)
    before_zh, zh_and_ja = natural.split('**简体中文**', 1)
    zh, after_zh = zh_and_ja.split('**日本語**', 1)
    zh = zh.replace('赋值点', '处').replace('赋值位', '处')
    natural = before_zh + '**简体中文**' + zh + '**日本語**' + after_zh
    assert 'by sorry' not in natural and 'remains Open' not in source and 'remain Open' not in source
    return natural, source
