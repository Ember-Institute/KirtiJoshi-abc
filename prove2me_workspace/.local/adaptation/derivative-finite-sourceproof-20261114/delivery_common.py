"""Draft delivery gates. Importing this module does not write or contact the platform."""
from pathlib import Path
import hashlib
import json
import math
import re

ROOT_DIR = Path('/home/admin-wsl/Coq/abc')
WORKSPACE = ROOT_DIR / 'prove2me_workspace'
UNIT = 'derivative-finite-sourceproof-20261114'
UNIT_REL = '.local/adaptation/' + UNIT + '/'
EVIDENCE = WORKSPACE / UNIT_REL
PREFIX = 'AbcAdaptation.Tripod.Fermat.Proper.'
ENV = '0df444a360eaa60ab8c11dca51a86af692955474'
ROOT_ID = 'e33ff731-60a7-43ef-87ae-c12aeba23cb5'
ROOT_NAME = 'abc.goal.lt_constant_mul_fix'
TARGET = 'noncriticalDerivativeBadPlacesFinite'
PARENT = 'noncriticalRamificationFinite'
MODULES = ['FermatCurveDerivationAdjoin', 'FermatCurveDerivationLocalization']
HELPERS = [PREFIX + 'CurveDeriv.' + n for n in [
    'extendOfFormallyEtale_algebraMap', 'polyDeriv_apply', 'derivAlong_aeval',
    'aeval_mem', 'mem_of_mem_adjoin', 'derivAlong_mem_of_mem_adjoin',
    'derivAlong_mem_chartRing_of_generators', 'derivAlong_mem_place_of_chartRing']]
READBACK_NAMES = set(HELPERS + [PREFIX + TARGET])
CHECK_SOURCE = 'Solutions/Checks_FermatDerivativeFiniteLocalization.lean'
PIN = '9ce4d3f793d3bc831f2fc7214b7dbad90ea012d8'


def read(name):
    return json.loads((EVIDENCE / name).read_text())


def save(name, value):
    (EVIDENCE / name).write_text(json.dumps(value, ensure_ascii=False, indent=2) + '\n')


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def theorem_path(name=TARGET):
    return 'Theorems/Thm_' + (PREFIX + name).replace('.', '_') + '.lean'


def solution_path():
    return UNIT_REL + 'Solution_' + TARGET + '.lean'


def checked_receipt(tag, source, review=False, artifact=False):
    receipt = read(tag + '-result.json')
    assert receipt['status'] == 'succeeded', (tag, receipt['status'])
    request, result = receipt['request'], receipt['result']
    assert result['exit_code'] == 0, tag
    rss = receipt['resources'].get('peak_rss_bytes')
    assert rss is None or rss <= 16 * 1024 ** 3, (tag, rss)
    assert request['workspace'] == str(WORKSPACE) and request['exclusive'] is True, tag
    expected_params = {'args': [source, '-o', '.lake/build/lib/lean/' + source[:-5] + '.olean']} if artifact else {'source': source}
    assert request['parameters'] == expected_params, (tag, request['parameters'])
    assert request['task_type'] == ('full' if artifact else 'review' if review else 'leaf'), tag
    assert request['target'] == ('module' if artifact else 'file'), tag
    assert request['worktree_manifest']['source_sha256'] == sha(WORKSPACE / source), tag
    snapshot = result['snapshot']
    assert snapshot['workspace_mode'] == 'exclusive_worktree' and snapshot['snapshot_id'] is None, tag
    assert result['actual_arguments'] == ['lean'] + (expected_params['args'] if artifact else [source]), tag
    assert 'sorryAx' not in result.get('stdout', '') + result.get('stderr', ''), tag
    if review:
        assert result['review']['passed'] is True, tag
    return receipt


def preflight():
    validation = read('sourceproof-validation.json')
    assert validation['passed'] is True and validation['exact_platform_types_equal'] is True
    definitions = {'Definitions/Def_' + mod + '.lean' for mod in MODULES}
    assert set(validation['definition_hashes']) == definitions
    assert set(validation['theorem_hashes']) == {PREFIX + TARGET}
    current = dict(validation['definition_hashes'])
    current[theorem_path()] = validation['theorem_hashes'][PREFIX + TARGET]
    for relative, expected in current.items():
        assert sha(WORKSPACE / relative) == expected, relative
    assert sha(EVIDENCE / 'decl_graph.jsonl') == validation['declaration_graph_sha256']
    receipts = []
    for mod in MODULES:
        source = 'Definitions/Def_' + mod + '.lean'
        receipts.append(checked_receipt(mod + '-leaf', source))
        receipts.append(checked_receipt(mod + '-artifact', source, artifact=True))
    receipts.append(checked_receipt(TARGET + '-leaf', theorem_path()))
    receipts.append(checked_receipt(TARGET + '-artifact', theorem_path(), artifact=True))
    receipts.append(checked_receipt('solution-' + TARGET + '-leaf', solution_path()))
    receipts.append(checked_receipt('source-graph-leaf', UNIT_REL + 'ExtractDerivativeProofGraph.lean'))
    receipts.append(checked_receipt('existing-types-leaf', UNIT_REL + 'ValidateExistingTypes.lean'))
    assert read('existing-types-equal.json') is True
    receipts.append(checked_receipt('closed-axioms-review', CHECK_SOURCE, review=True))
    receipts.append(checked_receipt('all-definitions-axioms-review', UNIT_REL + 'AuditAllDefinitions.lean', review=True))
    receipts.append(checked_receipt('production-gates-review', UNIT_REL + 'ProductionGates.lean', review=True))
    for check in validation.get('additional_leaf_checks', []):
        receipts.append(checked_receipt(check['tag'], check['source'], review=check.get('review', False), artifact=check.get('artifact', False)))
    # Earlier independent Definition leaves predate a proof-only consumer repair.
    # Their own source hash was checked above; final theorem/graph/audit receipts bind the whole current unit.
    for receipt in receipts[2 * len(MODULES):]:
        inputs = receipt['request']['worktree_manifest'].get('input_hashes', {})
        for relative, expected in current.items():
            if relative in inputs:
                assert inputs[relative] == expected, (receipt['job_id'], relative)
    solution = (WORKSPACE / solution_path()).read_text()
    assert 'sorry' not in solution and 'admit' not in solution
    assert not re.search(r'^\s*import\s+(?:Theorems|Solutions|Open)\.', solution, re.M)
    # The complete submission has no abstract child context. Optional context evidence
    # must say exactly that rather than silently accepting an Open dependency.
    context = EVIDENCE / 'published-child-context.json'
    if context.exists():
        assert json.loads(context.read_text()) in [[], {}], 'Direct proof must not rely on published Open child context'
    graph = [json.loads(line) for line in (EVIDENCE / 'decl_graph.jsonl').read_text().splitlines() if line.strip()]
    by_name = {row['name']: row for row in graph}
    assert len(by_name) == len(graph) and READBACK_NAMES <= set(by_name)
    visited, todo = set(), [PREFIX + TARGET]
    while todo:
        name = todo.pop()
        if name in visited:
            continue
        visited.add(name)
        assert name != 'sorryAx'
        if name.startswith('AbcAdaptation.'):
            assert name in by_name, ('Project dependency missing from source closure', name)
            row = by_name[name]
            assert name == PREFIX + TARGET or row['module'].startswith('Definitions.'), ('Open/theorem dependency in direct closure', name)
            todo.extend(row.get('typeDeps', []) + row.get('valueDeps', []))
    assert not any('sorryAx' in row.get('valueDeps', []) for row in graph)
    rb = read('readbacks-final.json')
    rows = rb['declarations']
    assert len(rows) == len(READBACK_NAMES) and {row['declaration'] for row in rows} == READBACK_NAMES
    readback_prose(rows)
    # Bind every normalized readback to its current corresponding source file.
    for row in rows:
        path = WORKSPACE / row['path']
        assert path.is_file()
        assert path == WORKSPACE / theorem_path() or path in {WORKSPACE / rel for rel in definitions}
    inputs = rb.get('input_file_sha256', {})
    assert inputs, 'Readback must record exact input file hashes'
    for relative, expected in current.items():
        recorded = inputs.get(relative, inputs.get(str(WORKSPACE / relative)))
        assert recorded == expected, ('Readback source hash mismatch', relative)
    source = read('source-consumer.json')
    assert source['pin'] == PIN and source['new_open_obligations'] == 0
    link = read('source-ledger-link.json')
    assert sha(ROOT_DIR / link['production_ledger']) == link['production_ledger_sha256']
    ids = json.loads((WORKSPACE / '.local/adaptation/fermat-noncritical-finite-20261114/published-child-ids.json').read_text())
    assert PREFIX + TARGET in ids
    return validation, {PREFIX + TARGET: ids[PREFIX + TARGET]}, rows


def readback_prose(rows):
    assert rows
    for row in rows:
        for lang in ['en', 'zh_Hans', 'ja']:
            assert isinstance(row[lang], str) and row[lang].strip(), (row['declaration'], lang)
    return '\n\n'.join('**' + title + '**\n\n' + '\n\n'.join(
        '`' + row['declaration'] + '`\n\n' + row[lang] for row in rows)
        for lang, title in [('en', 'English'), ('zh_Hans', '简体中文'), ('ja', '日本語')])


def publication_results(tag):
    submitted = read(tag + '-submit.json')
    assert not submitted.get('errors'), tag
    jobs = submitted.get('jobs') or [{'job_id': submitted['job_id']}]
    assert len(jobs) == 1
    results = []
    for job in jobs:
        result = read(tag + '-' + job['job_id'] + '-result.json')
        assert result['status'] == 'PUBLISHED' and result['visibility'] == 'private', tag
        assert result['id'] == job['job_id'], tag
        results.append(result)
    return results


def graph_summary(graph):
    assert graph['root_id'] == ROOT_ID
    assert not graph.get('has_hidden_deprecated') and not graph.get('has_hidden_deprecated_sketches')
    mathematical = {node['theorem_id']: node for node in graph['nodes']
                    if node['node_type'] == 'theorem' and node['status'] != 'Definition'}
    assert ROOT_ID in mathematical and mathematical[ROOT_ID]['theorem_name'] == ROOT_NAME
    assert all(not node.get('deprecated_at') for node in mathematical.values())
    # The overview can omit Definition-only edges at its cap. Mathematical children must be complete.
    for node in mathematical.values():
        if node.get('has_more_children'):
            missing = node.get('missing_children')
            assert missing and all(edge.get('hidden_by_definitions') is True for edge in missing), node.get('theorem_name', node.get('node_id'))
    sketches = [node for node in graph['nodes'] if node['node_type'] == 'sketch']
    edges, pairs = [], set()
    for node in sketches:
        assert node['status'] in ['ACCEPTED', 'SKETCH_ACCEPTED'] and not node.get('deprecated_at')
        parent = node['parent_theorem_id']
        assert parent in mathematical
        assert any(edge['kind'] == 'sketch' and edge['source'] == node['node_id'] and edge['target'] == parent
                   for edge in graph['edges'])
        children = sorted({mathematical[edge['source']]['theorem_name'] for edge in graph['edges']
                           if edge['kind'] == 'sketch' and edge['target'] == node['node_id'] and edge['source'] in mathematical})
        assert children, node['submission_id']
        parent_name = mathematical[parent]['theorem_name']
        edges.append({'parent': parent_name, 'children': children, 'submission_id': node['submission_id'], 'status': node['status']})
        pairs.update((parent_name, child) for child in children)
    return {'mathematical': mathematical, 'reductions': edges, 'dependency_pairs': pairs,
            'counts': {'accepted_reductions': len(edges), 'published_children': len(mathematical) - 1,
                       'dependency_edges': len(pairs)}}
