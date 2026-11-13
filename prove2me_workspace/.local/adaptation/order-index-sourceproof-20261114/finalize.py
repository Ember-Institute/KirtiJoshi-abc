"""Draft finalizer. Validate evidence, update this unit's registry/docs, and stage exact unit files.

No platform request, compiler, commit, push, or development-plan change occurs here.
"""
from pathlib import Path
from datetime import datetime, timezone
import json
import math
import shutil
import subprocess

from delivery_common import (
    ANCESTORS, ENV, EVIDENCE, MODULES, PIN, PREFIX, ROOT_DIR, ROOT_ID, TARGETS, UNIT, UNIT_REL,
    WORKSPACE, ancestor_metadata, compare_graphs, preflight, publication_results, read, save, sha,
    solution_path, theorem_path,
)


def final_document(original, observed):
    paragraphs = original.split('\n\n')
    for name in TARGETS:
        matches = [i for i, paragraph in enumerate(paragraphs) if paragraph.startswith('`Proper.' + name + '`')]
        assert len(matches) <= 1
        if matches:
            del paragraphs[matches[0]]
    composition = PREFIX + 'noncriticalCompositionRamification'
    if observed.get(composition, {}).get('status') == 'Proved':
        paragraphs = [p.replace('分歧有限性、复合分歧公式或既有', '分歧有限性或既有') for p in paragraphs]
    updated = '\n\n'.join(paragraphs)
    assert '三个子义务仍 Open' not in updated
    assert not any(p.startswith('`Proper.' + n + '`') for p in paragraphs for n in TARGETS)
    return updated


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
    validation, ids, rows = preflight()
    integration = read('integration.json')
    own_checks = {c['source'] for c in validation['compiler_checks'] if c.get('review') and c['source'].startswith('Solutions/Checks_')}
    core_files = {'Definitions/Def_' + module + '.lean' for module in MODULES} | {theorem_path(n) for n in TARGETS}
    assert core_files <= set(integration['files']) <= core_files | own_checks
    definition_receipts = []
    for module in MODULES:
        tag = 'def-' + module
        payload = read(tag + '-payload.json')
        assert payload['definition_name'] == module and payload['private'] is True and payload['env'] == ENV
        assert payload['definition'] == (WORKSPACE / ('Definitions/Def_' + module + '.lean')).read_text()
        definition_receipts.extend({'module': module, 'job_id': item['id'], 'status': item['status']} for item in publication_results(tag))
    proofs, statuses = [], {}
    for name in TARGETS:
        tag = 'prove-' + name
        request, submitted, result = (read(tag + suffix) for suffix in ['-verify-request.json', '-verify-submit.json', '-verify-result.json'])
        assert request['theorem_id'] == ids[PREFIX + name] and request['proof_type'] == 'prove'
        assert request['file'] == solution_path(name) and request['source_sha256'] == sha(WORKSPACE / solution_path(name))
        assert (EVIDENCE / (tag + '-solution.lean')).read_bytes() == (WORKSPACE / solution_path(name)).read_bytes()
        assert result['id'] == submitted['submission_id'] and result['theorem_id'] == ids[PREFIX + name] and result['status'] == 'ACCEPTED'
        proofs.append({'name': PREFIX + name, 'submission_id': submitted['submission_id'], 'status': 'ACCEPTED'})
        before, after = read('platform-before-' + name + '.json'), read('platform-after-' + name + '.json')
        assert before['theorem_id'] == after['theorem_id'] == ids[PREFIX + name]
        assert before['status'] == 'Open' and after['status'] == 'Proved'
        assert after['theorem_name'] == PREFIX + name and after['visibility'] == 'private' and after['mathlib_rev'] == ENV
        assert before['formal_statement'] == after['formal_statement']
        patch = read('metadata-' + name + '-patch-request.json')
        assert patch['endpoint'] == '/theorems/' + ids[PREFIX + name] and patch['method'] == 'PATCH'
        assert set(patch['payload']) == {'natural_language_statement', 'source'}
        assert read('metadata-' + name + '-patch-response.json') is not None
        metadata_after = read('metadata-' + name + '-after.json')
        assert metadata_after == after
        assert all(after[k] == v for k, v in patch['payload'].items())
        statuses[PREFIX + name] = after['status']
    before, after, observed, changes = compare_graphs(read('root-graph-before.json'), read('root-graph-after.json'), ids,
                                                       read('root-frontier-before.json'), read('root-frontier-after.json'))
    for name in ANCESTORS:
        if observed[PREFIX + name]['status'] != 'Proved':
            continue
        baseline = read('platform-before-' + name + '.json')
        natural, source = ancestor_metadata(name, baseline)
        patch = read('metadata-' + name + '-patch-request.json')
        assert patch['payload'] == {'natural_language_statement': natural, 'source': source}
        assert read('metadata-' + name + '-patch-response.json') is not None
        current = read('metadata-' + name + '-after.json')
        assert current['formal_statement'] == baseline['formal_statement'] and current['status'] == 'Proved'
        assert current['natural_language_statement'] == natural and current['source'] == source
    registry_path = WORKSPACE / '.local/adaptation/platform-node-registry.json'
    registry = json.loads(registry_path.read_text())
    old_direct = {item['name']: item for item in read('registry-before.json').get('direct_closed_proofs', [])}
    assert not (set(ids) & set(old_direct))
    direct = old_direct | {proof['name']: proof for proof in proofs}
    current_direct = {item['name']: item for item in registry.get('direct_closed_proofs', [])}
    assert current_direct in [old_direct, direct], 'Unrelated registry direct-proof entries changed after baseline'
    assert all(item['status'] == 'ACCEPTED' and observed[name]['status'] == 'Proved' for name, item in direct.items())
    added_dependency = after['added_existing_child_dependency']
    prior_frontier, frontier = read('root-frontier-before.json'), read('root-frontier-after.json')
    counts = after['counts'] | {'open_frontier': frontier['total'], 'direct_closed_children': len(direct)}
    prior_counts = before['counts'] | {'open_frontier': prior_frontier['total'], 'direct_closed_children': len(old_direct)}
    document = ROOT_DIR / 'docs/Prove2Me适配状态.md'
    updated_document = final_document(document.read_text(), observed)
    # Check the existing index before any document or registry write.
    known_paths = {str((WORKSPACE / p).relative_to(ROOT_DIR)) for p in core_files | own_checks}
    known_paths |= {'docs/Prove2Me适配状态.md', str(registry_path.relative_to(ROOT_DIR))}
    existing_staged = set(subprocess.check_output(['git', 'diff', '--cached', '--name-only', '-z'], cwd=ROOT_DIR).decode().split('\0')) - {''}
    assert all(p in known_paths or p.startswith('prove2me_workspace/' + UNIT_REL) for p in existing_staged), 'Unrelated paths are already staged; preserve them and reconcile before running this finalizer'
    summary = compiler_summary() | {'scope': integration.get('scope', 'Three existing polynomial-order and inverse-index source proofs'), 'closed_direct': proofs,
                                   'observed_status_changes': changes, 'added_existing_child_dependency': added_dependency, 'remaining_new_open': 0,
                                   'mathematical_root_proved': False,
                                   'production_gate_scope': 'Production aggregate acceptance does not establish the mathematical root.'}
    save('graph-count-evidence.json', {'before': prior_counts, 'after': counts,
        'counts_are_derived_from_actual_graph': True, 'mathematical_nodes_unchanged': True,
        'existing_reduction_identities_preserved': True,
        'added_existing_child_dependency': added_dependency, 'removed_dependencies': [],
        'reduction_count_delta': after['counts']['accepted_reductions'] - before['counts']['accepted_reductions'],
        'dependency_edge_count_delta': after['counts']['dependency_edges'] - before['counts']['dependency_edges'],
        'definitions_excluded_from_mathematical_nodes_and_edges': True,
        'observed_status_changes': changes, 'frontier_all_pages_fetched': True,
        'direct_proof_count_delta': len(proofs), 'frontier_count_delta': frontier['total'] - prior_frontier['total']})
    save('unit-ci-summary.json', summary)
    canonical = lambda values: sorted(values, key=lambda item: (item['parent'], item['submission_id']))
    registry['published_nodes'] = sorted(({'name': n['theorem_name'], 'id': ident} for ident, n in after['mathematical'].items() if ident != ROOT_ID), key=lambda item: item['name'])
    registry['edges'] = canonical(after['reductions'])
    registry['accepted_platform_reductions'] = counts['accepted_reductions']
    registry['dependency_edges'] = counts['dependency_edges']
    registry['graph_counts'] = counts
    registry['direct_closed_proofs'] = sorted(direct.values(), key=lambda item: item['name'])
    registry['platform_statuses'] = registry.get('platform_statuses', {}) | {name: node['status'] for name, node in observed.items()}
    registry['open_frontier'] = [item['theorem_name'] for item in frontier['open_leaves']]
    registry.update(local_open_children_below_root=frontier['total'], published_open_children_below_root=frontier['total'], mathematical_root_proved=False)
    registry['order_index_sourceproof_unit'] = {'source': UNIT, 'closed_direct': proofs, 'new_children': [],
        'new_reductions': [added_dependency], 'added_existing_child_dependency': added_dependency,
        'remaining_new_open': 0, 'observed_status_changes': changes,
        'all_frontier_pages_fetched': True, 'source_ledger_link': UNIT_REL + 'source-ledger-link.json'}
    registry.setdefault('graph_validation', {}).pop('order_index_direct_proofs_preserve_mathematical_graph', None)
    registry['graph_validation'].update(root_frontier_all_pages_fetched=True,
        order_index_existing_mathematical_nodes_and_reductions_preserved=True,
        order_index_added_existing_child_dependency=added_dependency)
    # Refresh only the two existing units consumed by these proofs.
    actual_reductions = {edge['submission_id']: edge for edge in after['reductions']}
    for key in ['noncritical_elementary_unit', 'noncritical_composition_unit']:
        if key not in registry:
            continue
        previous_unit = registry[key]
        child_names = set(previous_unit.get('children', {}))
        assert child_names <= set(observed)
        previous_unit['remaining_new_open'] = sum(observed[name]['status'] != 'Proved' for name in child_names)
        previous_unit['actual_platform_statuses'] = {name: observed[name]['status'] for name in child_names}
        previous_unit['closed_by_sourceproof_unit'] = UNIT
        reduction = previous_unit.get('reduction')
        if reduction:
            actual_edge = actual_reductions[reduction['submission_id']]
            assert actual_edge['parent'] == reduction['name']
            reduction['status'] = actual_edge['status']
        if key == 'noncritical_elementary_unit':
            previous_unit['closed_direct'] = proofs
    registry['recorded_at'] = datetime.now(timezone.utc).isoformat()
    save('current-source-consumer.json', {'source_pin': PIN, 'original_delivery_ledger': 'source-consumer.json',
        'source_boundary_link': 'source-ledger-link.json', 'definition_hashes': validation['definition_hashes'],
        'theorem_hashes': validation['theorem_hashes'], 'solution_hashes': validation['solution_hashes'],
        'declaration_graph_sha256': validation['declaration_graph_sha256'], 'closed_direct': proofs,
        'new_open_children': [], 'new_reductions': [added_dependency],
        'added_existing_child_dependency': added_dependency, 'actual_platform_states': {name: node['status'] for name, node in observed.items()},
        'new_global_assumptions': [], 'full_abc_closed': False, 'consumer_chain': read('source-consumer.json')['producers'],
        'source_notices': 'source copyright, author notices and Apache-2.0 release headers preserved; no bundled upstream license-text claim'})
    integration.update(status='One private Definition PUBLISHED; three existing order/index proofs ACCEPTED and Proved; the inverse proof records its proved regular-child dependency.',
        added_existing_child_dependency=added_dependency, new_reductions=[added_dependency],
        new_mathematical_theorem_nodes=0, direct_proofs=proofs, definition_receipts=definition_receipts, observed_status_changes=changes,
        platform_statuses={name: node['status'] for name, node in observed.items()}, remaining_new_open=0, mathematical_root_proved=False)
    save('integration.json', integration)
    here = Path(__file__).resolve().parent
    for name in ['delivery_common.py', 'graph_completion.py', 'platform_publish.py', 'finalize.py', 'README.md', 'report.json', 'ancestor-metadata-preview.json', 'ancestor-metadata.diff']:
        source, target = here / name, EVIDENCE / name
        if source.resolve() != target.resolve():
            shutil.copyfile(source, target)
    files = sorted(known_paths | {str(path.relative_to(ROOT_DIR)) for path in EVIDENCE.rglob('*') if path.is_file() and '__pycache__' not in path.parts})
    assert 'docs/开发计划.Prove2Me适配.md' not in files
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
            registry.setdefault('files', {})[relative] = __import__('hashlib').sha256(data).hexdigest()
    document.write_text(updated_document)
    registry_path.write_text(json.dumps(registry, ensure_ascii=False, indent=2) + '\n')
    assert not any(value in registry_path.read_bytes() for value in secrets)
    subprocess.run(['git', 'diff', '--check', '--'] + files, cwd=ROOT_DIR, check=True)
    subprocess.run(['git', 'add', '-f', '--'] + files, cwd=ROOT_DIR, check=True)
    subprocess.run(['git', 'diff', '--cached', '--check'], cwd=ROOT_DIR, check=True)
    print(json.dumps({'staged_paths': len(files), 'graph_counts': counts, 'closed_direct': proofs,
                      'observed_status_changes': changes, 'mathematical_root_proved': False}, ensure_ascii=False), flush=True)


if __name__ == '__main__':
    main()
