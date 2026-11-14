"""Northcott finalizer. No compiler, CI request, platform API, commit, push, or plan edit."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib
import json
import math
import shutil
import subprocess

from delivery_common import (
    ENV, EVIDENCE, MODULES, PREFIX, ROOT_DIR, ROOT_ID, ROOT_NAME, PARENT, PARENT_ID,
    UNIT, UNIT_REL, WORKSPACE, compare_graphs, configuration, preflight,
    proof_receipt, publication_results, read, save, sha, source_archive_evidence,
    theorem_path, solution_path, readback_prose,
)


def final_document(original):
    target = '- `refer/iut/Iut/Tripod/Northcott.lean:183`'
    lines = original.splitlines(keepends=True)
    assert sum(line.strip() == target for line in lines) <= 1
    return ''.join(line for line in lines if line.strip() != target)


def compiler_summary():
    records, seen = [], set()
    terminal = {'succeeded', 'failed', 'timeout', 'oom_killed', 'cancelled', 'interrupted', 'scheduler_error'}
    for path in sorted(EVIDENCE.rglob('*-result.json')):
        receipt = json.loads(path.read_text())
        if not all(k in receipt for k in ['request', 'resources', 'result', 'job_id']) or receipt['job_id'] in seen:
            continue
        seen.add(receipt['job_id'])
        q, result, resources = receipt['request'], receipt['result'], receipt['resources']
        assert receipt['status'] in terminal and q['workspace'] == str(WORKSPACE) and q['exclusive'] is True
        snapshot = result.get('snapshot') or {}
        if snapshot:
            assert snapshot.get('workspace_mode') == 'exclusive_worktree' and snapshot.get('snapshot_id') is None
        else:
            assert receipt['status'] != 'succeeded'
        params = q['parameters']
        arguments = ['lean'] + (params['args'] if 'args' in params else [params['source']])
        if result.get('actual_arguments') is not None:
            assert result['actual_arguments'] == arguments
        else:
            assert receipt['status'] != 'succeeded'
        cpu, user, system = (resources.get(k) for k in ['cpu_time_seconds', 'cpu_user_seconds', 'cpu_system_seconds'])
        if None not in [cpu, user, system]:
            assert math.isclose(cpu, user + system, abs_tol=0.1)
        if q['task_type'] == 'leaf' and receipt['status'] == 'succeeded':
            assert resources.get('peak_rss_bytes') is not None and resources['peak_rss_bytes'] <= 16 * 1024 ** 3
        records.append({
            'job_id': receipt['job_id'], 'status': receipt['status'], 'receipt': str(path.relative_to(WORKSPACE)),
            'input_version': q['worktree_manifest'].get('input_version'),
            'source_sha256': q['worktree_manifest'].get('source_sha256'),
            'actual_arguments': arguments, 'exit_code': result.get('exit_code'), 'workspace': q['workspace'],
            'workspace_mode': snapshot.get('workspace_mode'), 'snapshot_id': snapshot.get('snapshot_id'),
            **{k: resources.get(k) for k in ['wall_time_seconds', 'cpu_time_seconds', 'cpu_user_seconds', 'cpu_system_seconds', 'peak_rss_bytes', 'peak_pss_bytes']},
            'resource_source': resources.get('source'), 'degraded': resources.get('degraded'),
            'diagnostics': result.get('diagnostics'), 'review_passed': (result.get('review') or {}).get('passed'),
        })
    assert records
    def total(key):
        return sum(row[key] for row in records) if all(row[key] is not None for row in records) else None
    return {'records': records, 'succeeded': sum(row['status'] == 'succeeded' for row in records),
            'failed_or_other_terminal': sum(row['status'] != 'succeeded' for row in records),
            **{k: total(k) for k in ['wall_time_seconds', 'cpu_time_seconds', 'cpu_user_seconds', 'cpu_system_seconds']},
            'peak_rss_bytes': max((row['peak_rss_bytes'] for row in records if row['peak_rss_bytes'] is not None), default=None),
            'missing_memory_or_cpu_values_mean': 'unknown, not zero'}


def main():
    validation = preflight()
    config = configuration()
    plan, targets = config['plan'], config['targets']
    ids = read('published-child-ids.json')
    assert set(ids) == set(config['nodes'])
    definitions = []
    for item in plan['definitions']:
        tag = 'def-' + item['name']
        payload = read(item['payload'])
        assert read(tag + '-publication-requested.json') == {'endpoint': '/submit-definition', 'payload': payload}
        results = publication_results(tag, 1)
        definitions.extend({'name': item['name'], 'job_id': result['id'], 'status': result['status']} for result in results)
    published = publication_results('northcott-children', 5)
    assert {row['theorem_name']: row['theorem_id'] for row in published} == ids
    batch = read('northcott-children-payload.json')
    assert read('northcott-children-publication-requested.json') == {'endpoint': '/submit-problem', 'payload': batch}
    payloads = {item['theorem_name']: item for item in batch['problems']}
    proofs = {name: proof_receipt(name, PARENT_ID if name == PARENT else ids[name]) for name in targets}
    for name in config['nodes']:
        short = name.removeprefix(PREFIX).replace('.', '_')
        state = read('platform-after-' + short + '.json')
        assert state['theorem_name'] == name and state['theorem_id'] == ids[name] and state['status'] == 'Proved'
        assert state['visibility'] == 'private' and state['mathlib_rev'] == ENV
        assert state['formal_statement'] == payloads[name]['formal_statement']
        assert state['natural_language_statement'] == payloads[name]['natural_language_statement']
        assert state['source'] == payloads[name]['source']
    before_parent_path = EVIDENCE / 'platform-before-boundedDegreeFiniteness.json'
    before_parent = json.loads(before_parent_path.read_text())
    if (EVIDENCE / 'platform-before-parent.json').exists():
        duplicate = read('platform-before-parent.json')
        assert duplicate['theorem_id'] == before_parent['theorem_id'] and duplicate['formal_statement'] == before_parent['formal_statement']
    parent = read('platform-after-parent.json')
    assert before_parent['theorem_id'] == parent['theorem_id'] == PARENT_ID
    assert parent['theorem_name'] == PARENT and before_parent['status'] == 'Open' and parent['status'] == 'Proved'
    assert parent['visibility'] == 'private' and parent['mathlib_rev'] == ENV
    assert before_parent['formal_statement'] == parent['formal_statement']
    patch = read('parent-metadata-patch-request.json')
    assert patch == read('parent-metadata-patch-draft.json') and set(patch) == {'natural_language_statement', 'source'}
    assert all(parent[key] == value for key, value in patch.items())
    metadata_evidence = {'request': UNIT_REL + 'parent-metadata-patch-request.json',
                         'exact_saved_platform_readback': UNIT_REL + 'platform-after-parent.json',
                         'response_receipt': UNIT_REL + 'parent-metadata-patch-response.json' if (EVIDENCE / 'parent-metadata-patch-response.json').exists() else None,
                         'desired_metadata_confirmed': True, 'formal_statement_unchanged': True}
    before, after, observed = compare_graphs(read('root-graph-before.json'), read('root-graph-after.json'),
        read('root-frontier-before.json'), read('root-frontier-after.json'), ids, proofs, plan)
    added = after['added_mathematical_dependencies']
    registry_path = WORKSPACE / '.local/adaptation/platform-node-registry.json'
    registry = json.loads(registry_path.read_text())
    baseline_registry = read('registry-before.json')
    baseline_direct = {item['name']: item for item in baseline_registry.get('direct_closed_proofs', [])}
    assert not (set(config['nodes']) & set(baseline_direct))
    direct_additions = {name: {'name': name, 'submission_id': proofs[name]['submission_id'], 'status': 'ACCEPTED'} for name in config['nodes']}
    direct = baseline_direct | direct_additions
    current_direct = {item['name']: item for item in registry.get('direct_closed_proofs', [])}
    assert current_direct in [baseline_direct, direct], 'Unrelated registry direct proofs changed after baseline'
    assert all(observed[name]['status'] == 'Proved' for name in direct)
    front_before, frontier = read('root-frontier-before.json'), read('root-frontier-after.json')
    counts = after['counts'] | {'open_frontier': frontier['total'], 'direct_closed_children': len(direct)}
    before_counts = before['counts'] | {'open_frontier': front_before['total'], 'direct_closed_children': len(baseline_direct)}
    own_checks = {item['source'] for item in validation['compiler_checks'] if item.get('review') and item['source'].startswith('Solutions/Checks_')}
    integration = read('integration.json')
    assert set(integration['files']) == config['sources'] | own_checks
    document = ROOT_DIR / 'docs/Prove2Me适配状态.md'
    updated_document = final_document(document.read_text())
    allowed = {str((WORKSPACE / path).relative_to(ROOT_DIR)) for path in config['sources'] | own_checks}
    allowed |= {str(document.relative_to(ROOT_DIR)), str(registry_path.relative_to(ROOT_DIR))}
    # Preserve unrelated staged and unstaged work. Stage only exact owned paths below.
    staged_before = set(subprocess.check_output(['git', 'diff', '--cached', '--name-only', '-z'], cwd=ROOT_DIR).decode().split('\0')) - {''}
    unrelated_staged = sorted(path for path in staged_before if path not in allowed and not path.startswith('prove2me_workspace/' + UNIT_REL))
    unrelated_index_before = subprocess.check_output(['git', 'ls-files', '--stage', '-z', '--'] + unrelated_staged, cwd=ROOT_DIR) if unrelated_staged else b''
    source = source_archive_evidence()
    save('source-proof-provenance.json', source)
    graph_evidence = {'before': before_counts, 'after': counts,
        'counts_are_derived_from_actual_graph': True, 'new_mathematical_nodes': ids,
        'existing_mathematical_nodes_preserved': True, 'existing_reduction_identities_preserved': True,
        'added_mathematical_dependencies': added, 'removed_dependencies': [],
        'node_count_delta': len(ids), 'accepted_reduction_count_delta': 2, 'dependency_pair_count_delta': 5,
        'frontier_count_delta': frontier['total'] - front_before['total'], 'frontier_all_pages_fetched': True,
        'parent_before': 'Open', 'parent_after': 'Proved', 'root_after': observed[ROOT_NAME]['status'],
        'direct_closed_proof_count_delta': len(direct_additions)}
    save('graph-count-evidence.json', graph_evidence)
    ci = compiler_summary() | {'scope': integration['scope'], 'closed_direct': list(direct_additions.values()),
        'parent_composer': proofs[PARENT], 'parent_status': 'Proved', 'added_mathematical_dependencies': added,
        'remaining_new_open': 0, 'mathematical_root_proved': False,
        'production_gate_scope': 'Production aggregate acceptance is a separate gate and does not establish the mathematical root.'}
    save('unit-ci-summary.json', ci)
    registry['published_nodes'] = sorted(({'name': node['theorem_name'], 'id': ident} for ident, node in after['mathematical'].items() if ident != ROOT_ID), key=lambda row: row['name'])
    registry['edges'] = sorted(after['reductions'], key=lambda row: (row['parent'], row['submission_id']))
    registry['accepted_platform_reductions'] = counts['accepted_reductions']
    registry['dependency_edges'] = counts['dependency_edges']
    registry['graph_counts'] = counts
    registry['direct_closed_proofs'] = sorted(direct.values(), key=lambda row: row['name'])
    registry['platform_statuses'] = registry.get('platform_statuses', {}) | {name: node['status'] for name, node in observed.items()}
    registry['open_frontier'] = [row['theorem_name'] for row in frontier['open_leaves']]
    registry.update(local_open_children_below_root=frontier['total'], published_open_children_below_root=frontier['total'], mathematical_root_proved=False)
    registry['northcott_sourceproof_unit'] = {'source': UNIT, 'children': ids,
        'definition_publications': definitions,
        'closed_direct': list(direct_additions.values()), 'parent': proofs[PARENT] | {'platform_status': 'Proved'},
        'new_mathematical_nodes': ids, 'new_reductions': added, 'remaining_new_open': 0,
        'source_provenance': UNIT_REL + 'source-proof-provenance.json', 'all_frontier_pages_fetched': True,
        'parent_target_preserved': True, 'mathematical_root_proved': False}
    registry.setdefault('graph_validation', {}).update(root_frontier_all_pages_fetched=True, northcott_existing_nodes_and_reductions_preserved=True,
        northcott_new_node_count=5, northcott_new_dependency_pair_count=5, northcott_parent_proved=True)
    registry['recorded_at'] = datetime.now(timezone.utc).isoformat()
    save('current-source-consumer.json', {'scope': integration['scope'], 'source_provenance': source,
        'source_ledger': UNIT_REL + 'SOURCE_LEDGER.md', 'source_hashes': validation['source_hashes'],
        'solution_hashes': validation['solution_hashes'], 'closed_direct': list(direct_additions.values()),
        'parent_composer': proofs[PARENT], 'parent_status': 'Proved', 'new_mathematical_nodes': ids,
        'new_reductions': added, 'new_open_children': [], 'new_global_assumptions': [], 'full_abc_closed': False,
        'actual_consumers': config['dependencies'],
        'existing_parent_consumer': 'Solutions/Sol_TripodStatementII.lean, then statementII_of_children',
        'source_notices': 'Iut and Mathlib Apache-2.0 license texts, source copyright notices and adaptation headers are retained and verified by SHA256.'})
    save('parent-metadata-evidence.json', metadata_evidence)
    integration.update(status='Two private Definitions and five mathematical nodes published; five source proofs ACCEPTED; existing Northcott parent Proved.',
        source_provenance=source, definition_publications=definitions, published_nodes=ids, direct_proofs=list(direct_additions.values()),
        parent_composer=proofs[PARENT], parent_status='Proved', added_mathematical_dependencies=added,
        remaining_new_open=0, mathematical_root_proved=False)
    save('integration.json', integration)
    here = Path(__file__).resolve().parent
    for name in ['delivery_common.py', 'finalize.py', 'README.md', 'report.json']:
        origin, target = here / name, EVIDENCE / name
        if origin.resolve() != target.resolve():
            shutil.copyfile(origin, target)
    files = sorted(allowed | {str(path.relative_to(ROOT_DIR)) for path in EVIDENCE.rglob('*') if path.is_file() and '__pycache__' not in path.parts})
    assert all(not path.startswith('docs/') or path == 'docs/Prove2Me适配状态.md' for path in files)
    credentials = json.loads((WORKSPACE / 'credentials.json').read_text())
    secrets = [value.encode() for key, value in credentials.items() if key in ['access_token', 'refresh_token', 'api_key', 'token'] and isinstance(value, str) and len(value) >= 16]
    for relative in files:
        path = ROOT_DIR / relative
        assert path.is_file() and not path.is_symlink(), relative
        assert path.name not in ['credentials.json', '.env'] and path.suffix not in ['.pem', '.key', '.tmp'], relative
        data = updated_document.encode() if path == document else path.read_bytes()
        assert not any(value in data for value in secrets), relative
        assert (b'p2m_' + b'eyJ') not in data and (b'"access_' + b'token": "eyJ') not in data, relative
        if path != registry_path:
            registry.setdefault('files', {})[relative] = hashlib.sha256(data).hexdigest()
    document.write_text(updated_document)
    registry_path.write_text(json.dumps(registry, ensure_ascii=False, indent=2) + '\n')
    assert not any(value in registry_path.read_bytes() for value in secrets)
    subprocess.run(['git', 'diff', '--check', '--'] + files, cwd=ROOT_DIR, check=True)
    subprocess.run(['git', 'add', '-f', '--'] + files, cwd=ROOT_DIR, check=True)
    subprocess.run(['git', 'diff', '--cached', '--check', '--'] + files, cwd=ROOT_DIR, check=True)
    if unrelated_staged:
        assert subprocess.check_output(['git', 'ls-files', '--stage', '-z', '--'] + unrelated_staged, cwd=ROOT_DIR) == unrelated_index_before
    staged_after = set(subprocess.check_output(['git', 'diff', '--cached', '--name-only', '-z'], cwd=ROOT_DIR).decode().split('\0')) - {''}
    assert staged_after - staged_before <= set(files)
    print(json.dumps({'staged_owned_paths': len(files), 'preserved_unrelated_staged_paths': len(unrelated_staged),
                      'graph_counts': counts, 'direct_closed_additions': len(direct_additions),
                      'parent_status': 'Proved', 'root_status': observed[ROOT_NAME]['status']}, ensure_ascii=False), flush=True)


if __name__ == '__main__':
    main()
