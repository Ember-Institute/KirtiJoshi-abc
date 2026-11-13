from pathlib import Path
import hashlib
import json

ROOT_DIR = Path('/home/admin-wsl/Coq/abc')
WORKSPACE = ROOT_DIR / 'prove2me_workspace'
EVIDENCE = WORKSPACE / '.local/adaptation/fermat-noncritical-elementary-20261114'
UNIT_REL = '.local/adaptation/fermat-noncritical-elementary-20261114/'
PREFIX = 'AbcAdaptation.Tripod.Fermat.Proper.'
ENV = '0df444a360eaa60ab8c11dca51a86af692955474'
ROOT_ID = 'e33ff731-60a7-43ef-87ae-c12aeba23cb5'
ROOT_NAME = 'abc.goal.lt_constant_mul_fix'
MODULES = ['FermatNoncriticalElementarySource']
READBACK_EXTRAS = [PREFIX + 'NoncriticalElementarySource.poly_spec', PREFIX + 'NoncriticalElementarySource.mob_spec']
CHILDREN = ['noncriticalPolynomialOrderAtRegularPoint', 'noncriticalPolynomialOrderAtPole', 'noncriticalInverseRamification']
PARENTS = ['noncriticalElementaryCompositionRamification']


def read(name):
    return json.loads((EVIDENCE / name).read_text())


def save(name, value):
    (EVIDENCE / name).write_text(json.dumps(value, ensure_ascii=False, indent=2) + '\n')


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def theorem_path(name):
    if name.startswith('Theorems/'):
        return name
    if not name.startswith(PREFIX):
        name = PREFIX + name
    return 'Theorems/Thm_' + name.replace('.', '_') + '.lean'


def checked_receipt(tag, source, review=False, sorry=False):
    receipt = read(tag + '-result.json')
    assert receipt['status'] == 'succeeded', (tag, receipt['status'])
    request, result = receipt['request'], receipt['result']
    assert result['exit_code'] == 0, tag
    assert request['workspace'] == str(WORKSPACE) and request['exclusive'] is True, tag
    assert request['parameters']['source'] == source, (tag, source)
    assert request['worktree_manifest']['source_sha256'] == sha(WORKSPACE / source), tag
    snapshot = result['snapshot']
    assert snapshot['workspace_mode'] == 'exclusive_worktree' and snapshot['snapshot_id'] is None, tag
    parameters = request['parameters']
    expected = ['lean'] + (parameters['args'] if 'args' in parameters else [source])
    assert result['actual_arguments'] == expected, tag
    if review:
        assert result['review']['passed'], tag
    if sorry:
        assert 'sorryAx' in result['stdout'], tag
    else:
        assert 'sorryAx' not in result['stdout'], tag
    return receipt


def preflight():
    validation = read('upload-validation.json')
    for flag in ['passed', 'elaborated_types_equal', 'existing_target_types_definitionally_equal']:
        assert validation[flag] is True, flag
    definitions = {'Definitions/Def_' + mod + '.lean' for mod in MODULES}
    assert validation['new_theorem_count'] == len(CHILDREN)
    assert set(validation['definition_hashes']) == definitions
    for relative, expected in validation['definition_hashes'].items():
        assert sha(WORKSPACE / relative) == expected, relative
    theorem_hashes = {theorem_path(name): value for name, value in validation['source_theorem_hashes'].items()}
    assert set(theorem_hashes) == {theorem_path(name) for name in CHILDREN + PARENTS}
    for relative, expected in theorem_hashes.items():
        assert sha(WORKSPACE / relative) == expected, relative
    assert sha(EVIDENCE / 'decl_graph.jsonl') == validation['source_graph_sha256']
    assert sha(EVIDENCE / 'upload-problem-items.json') == validation['upload_problem_items_sha256']
    receipts = []
    for mod in MODULES:
        receipts.append(checked_receipt(mod + '-leaf', 'Definitions/Def_' + mod + '.lean'))
    for name in CHILDREN + PARENTS:
        receipts.append(checked_receipt(name + '-leaf', theorem_path(name)))
    for name in PARENTS:
        receipts.append(checked_receipt('solution-' + name + '-leaf', UNIT_REL + 'Solution_' + name + '.lean'))
        assert b'sorry' not in (EVIDENCE / ('Solution_' + name + '.lean')).read_bytes()
    receipts.append(checked_receipt('source-graph-leaf', UNIT_REL + 'ExtractElementaryGraph.lean'))
    receipts.append(checked_receipt('elaborated-types-leaf', UNIT_REL + 'ValidateElaboratedTypes.lean'))
    receipts.append(checked_receipt('existing-types-leaf', UNIT_REL + 'ValidateExistingTypes.lean'))
    # These files are emitted only after the corresponding Lean checks succeed.
    assert read('existing-types-equal.json') is True
    elaborated = read('upload-elaborated-types.json')
    assert isinstance(elaborated, list) and len(elaborated) == len(CHILDREN)
    graph_rows = [json.loads(line) for line in (EVIDENCE / 'decl_graph.jsonl').read_text().splitlines() if line.strip()]
    by_name = {row['name']: row for row in graph_rows}
    assert {row['name'] for row in elaborated} == {PREFIX + name for name in CHILDREN}
    assert read('export-types-equal.json') is True  # Lean.Meta.isDefEq compares actual types; pretty notation can differ.
    receipts.append(checked_receipt('closed-axioms-review', 'Solutions/Checks_FermatNoncriticalElementaryClosed.lean', review=True))
    receipts.append(checked_receipt('reduction-axioms-leaf', 'Solutions/Checks_FermatNoncriticalElementaryReduction.lean', sorry=True))
    receipts.append(checked_receipt('all-definitions-axioms-review', UNIT_REL + 'AuditAllDefinitions.lean', review=True))
    receipts.append(checked_receipt('production-gates-review', UNIT_REL + 'ProductionGates.lean', review=True))
    # Optional exact-context mirrors are gated only when the root provides them.
    for check in validation.get('additional_leaf_checks', []):
        receipts.append(checked_receipt(check['tag'], check['source'],
                                        review=check.get('review', False), sorry=check.get('sorry', False)))
    # Bind final audit inputs to the current unit sources when the manifest records the closure.
    current = validation['definition_hashes'] | theorem_hashes
    for receipt in receipts[len(MODULES) + len(CHILDREN) + len(PARENTS):]:
        recorded = receipt['request']['worktree_manifest'].get('input_hashes', {})
        for relative, expected in current.items():
            if relative in recorded:
                assert recorded[relative] == expected, (receipt['job_id'], relative)
    items = read('upload-problem-items.json')
    assert isinstance(items, list) and {item['theorem_name'] for item in items} == {PREFIX + n for n in CHILDREN}
    assert len(items) == len(CHILDREN)
    for item in items:
        # Compiler source ranges may include the declaration's doc comment.
        assert item['preamble'] and item['formal_statement'].count('theorem ' + item['theorem_name']) == 1
        assert 'sorry' in item['formal_statement']
    old_ids = json.loads((WORKSPACE / '.local/adaptation/fermat-noncritical-composition-20261114/published-child-ids.json').read_text())
    old_ids = {PREFIX + name: old_ids[PREFIX + name] for name in PARENTS}
    return validation, items, old_ids


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
    assert jobs
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
    for node in graph['nodes']:
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
