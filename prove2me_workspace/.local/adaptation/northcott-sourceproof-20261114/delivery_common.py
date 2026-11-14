"""Strong Northcott gates. Importing this module performs no write, API call or compilation."""
from pathlib import Path
import hashlib
import json
import math
import re

ROOT_DIR = Path('/home/admin-wsl/Coq/abc')
WORKSPACE = ROOT_DIR / 'prove2me_workspace'
UNIT = 'northcott-sourceproof-20261114'
UNIT_REL = '.local/adaptation/' + UNIT + '/'
EVIDENCE = WORKSPACE / UNIT_REL
PREFIX = 'AbcAdaptation.Tripod.'
ENV = '0df444a360eaa60ab8c11dca51a86af692955474'
ROOT_ID = 'e33ff731-60a7-43ef-87ae-c12aeba23cb5'
ROOT_NAME = 'abc.goal.lt_constant_mul_fix'
PARENT = PREFIX + 'boundedDegreeFiniteness'
PARENT_ID = 'bfd60e2f-e299-4833-ab7e-03d2b7ccfd94'
MODULES = ['TripodNorthcottInputs', 'TripodNorthcottComposition']
CHILDREN = [PREFIX + 'northcottFiniteRoots', PREFIX + 'northcottPolynomialWitness']
INPUT_DECLARATIONS = [PREFIX + 'Northcott.' + name for name in [
    'heightBound', 'heightBound_pos', 'natDegree_minpoly_int_le', 'coeffBoundOf',
    'eval₂_minpoly_int_algebraMap', 'coeffBound', 'polySet', 'FiniteRoots', 'PolynomialWitness']]


def configuration(plan=None):
    plan = read('delivery-plan.json') if plan is None else plan
    assert plan['unit'] == UNIT and plan['unit_relative'] == UNIT_REL
    assert plan['root_id'] == ROOT_ID and plan['parent_id'] == PARENT_ID and plan['parent_name'] == PARENT
    assert plan['mathlib_rev'] == ENV and plan['visibility'] == 'private'
    nodes = plan['new_mathematical_nodes']
    assert len(nodes) == len(set(nodes)) == 5 and all(name.startswith(PREFIX) and name.isascii() for name in nodes)
    dependencies = plan['true_dependencies']
    assert set(dependencies) == {CHILDREN[1], PARENT}
    estimates = dependencies[CHILDREN[1]]
    assert len(estimates) == len(set(estimates)) == 3
    assert set(nodes) == set(estimates + CHILDREN) and set(dependencies[PARENT]) == set(CHILDREN)
    assert {item['name'] for item in plan['definitions']} == set(MODULES)
    assert len(plan['definitions']) == 2
    sources = {item['source'] for item in plan['definitions']} | {theorem_path(n) for n in nodes + [PARENT]}
    assert {item['source'] for item in plan['definitions']} == {'Definitions/Def_' + mod + '.lean' for mod in MODULES}
    solutions = {item['name']: item for item in plan['solutions']}
    assert len(solutions) == 6 and set(solutions) == set(nodes + [PARENT])
    for name, item in solutions.items():
        assert item['source'] == solution_path(name)
    return {'plan': plan, 'nodes': nodes, 'estimates': estimates, 'targets': nodes + [PARENT],
            'dependencies': dependencies, 'sources': sources, 'solutions': solutions,
            'readback_names': set(nodes + [PARENT] + INPUT_DECLARATIONS + [PREFIX + 'boundedDegreeFiniteness_of_northcott_children'])}


def theorem_path(name):
    return 'Theorems/Thm_' + name.replace('.', '_') + '.lean'


def solution_path(name):
    return UNIT_REL + 'Solution_' + name.removeprefix(PREFIX).replace('.', '_') + '.lean'


def verify_tag(name):
    return 'verify-' + name.removeprefix(PREFIX).replace('.', '_')


def imports(text):
    return [module for line in text.splitlines() if line.startswith('import ') for module in line[7:].split()]


def read(name):
    return json.loads((EVIDENCE / name).read_text())

def save(name, value):
    path = EVIDENCE / name
    temporary = path.with_name(path.name + '.tmp')
    temporary.write_text(json.dumps(value, ensure_ascii=False, indent=2) + '\n')
    temporary.replace(path)

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

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


def source_archive_evidence():
    manifest = read('SOURCE_MANIFEST.json')
    reference = manifest['reference_iut']
    assert reference.get('runtime_imports', []) == []
    assert manifest['platform_mathlib']['revision'] == ENV
    current = {}
    for section in [reference, manifest['platform_mathlib']]:
        for item in section['source_files']:
            path = Path(item['path'])
            assert path.is_absolute() and sha(path) == item['sha256'], str(path)
            if 'bytes' in item:
                assert path.stat().st_size == item['bytes']
            current[str(path)] = item['sha256']
    northcott = [item for item in reference['source_files'] if item['path'].endswith('/Iut/Tripod/Northcott.lean')]
    assert len(northcott) == 1
    pin = read('source-pin-draft.json')
    assert pin['exact_archive_path'] == northcott[0]['path'] and pin['sha256'] == northcott[0]['sha256']
    assert pin['tracked_blob_required_before_delivery'] is False
    # The ignored archive is pinned by its actual bytes. A content OID is not a tracked-blob claim.
    assert pin.get('tracked_blob_entry_at_prepare') is None
    iut_license = next(item['sha256'] for item in reference['source_files'] if item['path'].endswith('/LICENSE'))
    mathlib_license = next(item['sha256'] for item in manifest['platform_mathlib']['source_files'] if item['path'].endswith('/LICENSE'))
    assert sha(EVIDENCE / 'licenses/LICENSE.iut') == iut_license
    assert sha(EVIDENCE / 'licenses/LICENSE.mathlib') == mathlib_license
    return {'archive_path': pin['exact_archive_path'], 'archive_sha256': pin['sha256'],
            'source_manifest_sha256': sha(EVIDENCE / 'SOURCE_MANIFEST.json'),
            'source_files_verified_by_sha256': current,
            'root_head_snapshot_context': pin.get('root_head_at_prepare'),
            'historical_upstream_revision': reference.get('upstream_revision_in_existing_source_ledger'),
            'historical_upstream_revision_verified': False, 'tracked_blob_claim': False,
            'upstream_revision_verification_limit': reference['upstream_revision_verification'],
            'candidate_hashes_scope': 'Historical source adaptation inventory; current delivery-validation hashes and CI receipts bind final platform declaration names.'}


def bound_file(validation, name, *fields):
    present = [validation[field] for field in fields if field in validation]
    assert present, ('Missing compiler evidence hash', name, fields)
    expected = sha(EVIDENCE / name)
    assert all(value == expected for value in present), name


def compiler_formals(validation, config):
    bound_file(validation, 'compiler-formals.json', 'compiler_formals_sha256', 'syntax_sha256')
    formals = read('compiler-formals.json')
    assert set(formals) == set(config['targets'])
    for name, row in formals.items():
        assert set(['preamble', 'formal_statement', 'source', 'syntax']) <= set(row), name
        source_path = Path(row['source'])
        relative_source = str(source_path.relative_to(WORKSPACE)) if source_path.is_absolute() else str(source_path)
        assert relative_source == theorem_path(name)
        assert isinstance(row['preamble'], str) and isinstance(row['formal_statement'], str)
        assert row['syntax'], ('Compiler Syntax evidence is missing', name)
    return formals


def preflight(delivery=None):
    """Can replace Delivery.preflight; it does not compile, publish, or write."""
    if delivery is not None:
        assert Path(delivery.workspace) == WORKSPACE and Path(delivery.evidence) == EVIDENCE
    config = configuration(delivery.plan if delivery is not None else None)
    plan, targets = config['plan'], config['targets']
    validation = read('delivery-validation.json')
    for key in ['passed', 'exact_existing_target_type_equal', 'readbacks_compiler_bound']:
        assert validation[key] is True, key
    assert validation['new_open_mathematical_obligations'] == 0
    assert set(validation['source_hashes']) == config['sources']
    assert set(validation['solution_hashes']) == {solution_path(name) for name in targets}
    for relative, expected in validation['source_hashes'].items() | validation['solution_hashes'].items():
        assert sha(WORKSPACE / relative) == expected, relative
    bound_file(validation, 'decl_graph.jsonl', 'declaration_graph_sha256', 'graph_sha256')
    bound_file(validation, 'final-readbacks.json', 'readbacks_sha256', 'readback_sha256')
    checks = validation['compiler_checks']
    assert checks and len({item['tag'] for item in checks}) == len(checks)
    receipts = [checked_receipt(check) for check in checks]
    modes = {(c['source'], c.get('review', False), c.get('artifact', False)) for c in checks}
    for relative in config['sources']:
        assert (relative, False, False) in modes and (relative, False, True) in modes, relative
    for name in targets:
        assert (solution_path(name), False, False) in modes, name
    review_sources = {item['source'] for item in checks if item.get('review')}
    assert any(path.startswith('Solutions/Checks_') for path in review_sources)
    assert any(path.endswith('/AuditAllDefinitions.lean') for path in review_sources)
    assert any(path.endswith('/ProductionGates.lean') for path in review_sources)
    assert any('Extract' in Path(c['source']).name and 'Graph' in Path(c['source']).name for c in checks)
    assert any('Syntax' in Path(c['source']).name or 'Formal' in Path(c['source']).name for c in checks)
    assert any('Validate' in Path(c['source']).name and 'Types' in Path(c['source']).name for c in checks)
    assert read('existing-types-equal.json') is True
    for check, receipt in zip(checks, receipts):
        if not check.get('review'):
            continue
        inputs = receipt['request']['worktree_manifest'].get('input_hashes', {})
        for relative, expected in validation['source_hashes'].items():
            assert lookup_input(inputs, relative) == expected, (check['tag'], relative)
    for item in plan['definitions']:
        payload = read(item['payload'])
        assert payload['definition_name'] == item['name'] and payload['env'] == ENV and payload['private'] is True
        assert payload['definition'] == (WORKSPACE / item['source']).read_text()
        assert item['source_sha256'] == validation['source_hashes'][item['source']]
        assert not any(module.startswith('Theorems.') for module in imports(payload['definition']))
    for name, item in config['solutions'].items():
        text = (WORKSPACE / item['source']).read_text()
        assert not re.search(r'\b(sorry|admit|axiom|unsafe)\b', text), name
        actual_imports = imports(text)
        assert not any(module.startswith(('Solutions.', 'Open.', 'Iut.', 'Genl.', 'Heights.')) for module in actual_imports)
        expected = {'Theorems.Thm_' + child.replace('.', '_') for child in config['dependencies'].get(name, [])}
        assert {module for module in actual_imports if module.startswith('Theorems.')} == expected, name
        assert set(item['theorem_imports']) == expected
        assert item['source_sha256'] == validation['solution_hashes'][item['source']]
        request = read(verify_tag(name) + '-request-draft.json')
        assert request['theorem_name'] == name and request['proof_type'] == 'prove'
        assert request['file'] == item['source'] and request['source_sha256'] == item['source_sha256']
    for relative in config['sources']:
        text = (WORKSPACE / relative).read_text()
        assert not re.search(r'\b(sorry|admit|axiom|unsafe)\b', text), relative
        assert not any(module.startswith(('Solutions.', 'Open.', 'Iut.', 'Genl.', 'Heights.')) or 'Act2' in module or 'Scene2' in module for module in imports(text))
        owners = [name for name in targets if theorem_path(name) == relative]
        if owners:
            expected_modules = {'Theorems.Thm_' + child.replace('.', '_') for child in config['dependencies'].get(owners[0], [])}
            assert {module for module in imports(text) if module.startswith('Theorems.')} == expected_modules, relative
    rows = read('final-readbacks.json')['declarations']
    assert len(rows) == len({row['declaration'] for row in rows}) == 16
    assert {row['declaration'] for row in rows} == config['readback_names']
    graph = [json.loads(line) for line in (EVIDENCE / 'decl_graph.jsonl').read_text().splitlines() if line.strip()]
    by_name = {row['name']: row for row in graph}
    assert len(by_name) == len(graph)
    bindings = readback_compiler_bindings(rows, graph)
    assert {binding['declaration'] for binding in bindings} == config['readback_names']
    for row in rows:
        assert {'compiler_name', 'elaboratedType', 'compiler_source_span'} <= set(row), row['declaration']
        assert row['path'] in config['sources']
        owner = by_name[row['compiler_name']]
        assert owner['module'].replace('.', '/') + '.lean' == row['path']
        assert row.get('source_file_sha256', validation['source_hashes'][row['path']]) == validation['source_hashes'][row['path']]
    readback_prose(rows)
    readbacks = read('final-readbacks.json')
    for relative, expected in validation['source_hashes'].items():
        assert lookup_input(readbacks['input_file_sha256'], relative) == expected
    # Every owned output is reachable from a real consumer in the six source proofs.
    visited, todo = set(), list(targets)
    while todo:
        name = todo.pop()
        if name in visited:
            continue
        visited.add(name)
        assert name != 'sorryAx'
        if name not in by_name:
            assert not name.startswith(('AbcAdaptation.', '_private.')), ('Missing project dependency', name)
            continue
        row = by_name[name]
        generated = row['startLine'] == 0 and row['endLine'] == 0 and any(
            name.startswith(dep + '.') and dep in by_name and by_name[dep]['module'].startswith('Definitions.')
            for dep in row.get('typeDeps', []) + row.get('valueDeps', []))
        assert row['module'].startswith('Definitions.') or name in targets or name.startswith('_private.') or generated, name
        todo.extend(row.get('typeDeps', []) + row.get('valueDeps', []))
    assert config['readback_names'] <= visited
    for name in targets:
        row = by_name[name]
        actual_theorems = {dep for dep in row.get('typeDeps', []) + row.get('valueDeps', [])
                           if dep in by_name and by_name[dep]['module'].startswith('Theorems.') and by_name[dep]['startLine'] > 0}
        assert actual_theorems == set(config['dependencies'].get(name, [])), (name, actual_theorems)
    assert all(row['kind'] != 'axiom' and 'sorryAx' not in row.get('typeDeps', []) + row.get('valueDeps', []) for row in graph)
    formals = compiler_formals(validation, config)
    batch = read('northcott-children-payload.json')
    assert batch['env'] == ENV and batch['private'] is True
    existing = plan.get('existing_child_matches', {})
    assert existing == {}, 'This unit expects five actual newly published mathematical nodes'
    assert {item['theorem_name'] for item in batch['problems']} == set(config['nodes'])
    quote = (EVIDENCE / 'mochizuki-quotation.md').read_text().strip()
    assert quote
    by_readback = {row['declaration']: row for row in rows}
    for item in batch['problems']:
        name = item['theorem_name']
        assert item['preamble'] == formals[name]['preamble']
        assert item['formal_statement'] == formals[name]['formal_statement']
        assert item['natural_language_statement'] == quote + '\n\n' + readback_prose([by_readback[name]])
    patch = read('parent-metadata-patch-draft.json')
    assert set(patch) == {'natural_language_statement', 'source'}
    assert patch['natural_language_statement'] == quote + '\n\n' + readback_prose([by_readback[PARENT]])
    for item in plan['definitions']:
        selected = [row for row in rows if row['path'] == item['source']]
        assert read(item['payload'])['natural_language_statement'] == quote + '\n\n' + readback_prose(selected)
    provenance = source_archive_evidence()
    metadata_sources = [patch['source']] + [item['source'] for item in batch['problems']] + [read(item['payload'])['source'] for item in plan['definitions']]
    for statement in metadata_sources:
        assert provenance['archive_sha256'] in statement
        assert 'not independently verified' in statement or 'unverified' in statement
    integration = read('integration.json')
    assert set(validation['source_hashes']) <= set(integration['files'])
    for relative, expected in validation['source_hashes'].items():
        assert integration['files'][relative] == expected
    assert integration['parent_target_preserved'] is True
    return validation


def proof_receipt(name, ident):
    tag = verify_tag(name)
    submitted = read(tag + '-submit.json')
    result = read(tag + '-result.json')
    request = read(tag + '-verification-requested.json')
    assert request['theorem_id'] == ident and request['proof_type'] == 'prove'
    assert request['file'] == solution_path(name)
    assert request['source_sha256'] == sha(WORKSPACE / request['file'])
    assert result['id'] == submitted['submission_id'] and result['theorem_id'] == ident
    assert result['status'] in ({'SKETCH_ACCEPTED', 'ACCEPTED'} if name == PARENT else {'ACCEPTED'})
    return {'name': name, 'theorem_id': ident, 'submission_id': result['id'], 'status': result['status'],
            'receipt': UNIT_REL + tag + '-result.json'}


def compare_graphs(before_graph, after_graph, before_frontier, after_frontier, ids, proofs, plan=None):
    config = configuration(plan)
    before, after = graph_summary(before_graph), graph_summary(after_graph)
    old = {node['theorem_name']: node for node in before['mathematical'].values()}
    new = {node['theorem_name']: node for node in after['mathematical'].values()}
    assert set(ids) == set(config['nodes']) and len(set(ids.values())) == 5
    assert set(new) - set(old) == set(config['nodes']) and not (set(old) - set(new))
    assert set(after['mathematical']) - set(before['mathematical']) == set(ids.values())
    assert not (set(before['mathematical']) - set(after['mathematical']))
    assert old[PARENT]['theorem_id'] == new[PARENT]['theorem_id'] == PARENT_ID
    assert old[PARENT]['status'] == 'Open' and new[PARENT]['status'] == 'Proved'
    assert old[ROOT_NAME]['status'] == new[ROOT_NAME]['status'] == 'Open'
    for name in config['nodes']:
        assert new[name]['theorem_id'] == ids[name] and new[name]['status'] == 'Proved'
    for name, node in old.items():
        if name != PARENT:
            assert new[name]['theorem_id'] == node['theorem_id'] and new[name]['status'] == node['status'], name
    assert set(proofs) == set(config['targets'])
    for name, proof in proofs.items():
        assert proof['theorem_id'] == (PARENT_ID if name == PARENT else ids[name])
        assert proof['status'] in ({'SKETCH_ACCEPTED', 'ACCEPTED'} if name == PARENT else {'ACCEPTED'})
    expected_pairs = {(parent, child) for parent, children in config['dependencies'].items() for child in children}
    assert len(expected_pairs) == 5
    assert after['dependency_pairs'] - before['dependency_pairs'] == expected_pairs
    assert not (before['dependency_pairs'] - after['dependency_pairs'])
    old_reductions = {edge['submission_id']: edge for edge in before['reductions']}
    new_reductions = {edge['submission_id']: edge for edge in after['reductions']}
    assert len(old_reductions) == len(before['reductions']) and len(new_reductions) == len(after['reductions'])
    assert set(old_reductions) <= set(new_reductions)
    expected_added_ids = {proofs[name]['submission_id'] for name in config['dependencies']}
    assert len(expected_added_ids) == 2
    assert set(new_reductions) - set(old_reductions) == expected_added_ids
    added = []
    for name, children in config['dependencies'].items():
        edge = new_reductions[proofs[name]['submission_id']]
        assert edge == {'parent': name, 'children': sorted(children),
                        'submission_id': proofs[name]['submission_id'], 'status': 'ACCEPTED'}
        added.append(edge | {'proof_receipt': proofs[name]['receipt'], 'parent_status': new[name]['status'],
                             'child_statuses': {child: new[child]['status'] for child in children}})
    for submission_id, edge in old_reductions.items():
        current = new_reductions[submission_id]
        assert (edge['parent'], edge['children']) == (current['parent'], current['children'])
        if current['status'] != edge['status']:
            assert edge['status'] == 'SKETCH_ACCEPTED' and current['status'] == 'ACCEPTED'
            assert all(new[child]['status'] == 'Proved' for child in current['children'])
    assert after['counts'] == {'accepted_reductions': before['counts']['accepted_reductions'] + 2,
                               'published_children': before['counts']['published_children'] + 5,
                               'dependency_edges': before['counts']['dependency_edges'] + 5}
    frontiers = []
    for frontier, nodes in [(before_frontier, old), (after_frontier, new)]:
        rows = frontier['open_leaves']
        assert frontier['all_pages_fetched'] and len(rows) == frontier['total'] == len({row['theorem_id'] for row in rows})
        for row in rows:
            assert nodes[row['theorem_name']]['theorem_id'] == row['theorem_id'] and nodes[row['theorem_name']]['status'] == 'Open'
        frontiers.append({row['theorem_id'] for row in rows})
    assert PARENT_ID in frontiers[0] and frontiers[1] == frontiers[0] - {PARENT_ID}
    assert after_frontier['total'] == before_frontier['total'] - 1
    after['added_mathematical_dependencies'] = added
    after['new_mathematical_node_ids'] = ids
    return before, after, new


def publication_results(tag, expected_count):
    submitted = read(tag + '-submit.json')
    assert not submitted.get('errors')
    jobs = submitted.get('jobs') or [{'job_id': submitted['job_id']}]
    assert len(jobs) == expected_count
    results = []
    for job in jobs:
        result = read(tag + '-' + job['job_id'] + '-result.json')
        assert result['id'] == job['job_id'] and result['status'] == 'PUBLISHED' and result['visibility'] == 'private'
        results.append(result)
    return results
