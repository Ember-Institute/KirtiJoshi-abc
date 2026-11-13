"""DRAFT finalizer: validates accepted evidence, updates unit registry, and stages exact files.

No publication, commit, push, or plan-checkbox edit occurs here. The main agent must
review and explicitly run this after platform synchronization.
"""
from pathlib import Path
from datetime import datetime, timezone
import json
import math
import shutil
import subprocess

from delivery_common import (
    CHECK_SOURCE, ENV, EVIDENCE, MODULES, PARENT, PIN, PREFIX, ROOT_DIR,
    ROOT_ID, ROOT_NAME, TARGET, UNIT, UNIT_REL, WORKSPACE, graph_summary,
    preflight, publication_results, read, save, sha, solution_path, theorem_path,
)


def main():
    w, b, r, pre = WORKSPACE, EVIDENCE, ROOT_DIR, PREFIX
    validation, ids, rows = preflight()
    integration = read('integration.json')
    expected_files = {'Definitions/Def_' + module + '.lean' for module in MODULES} | {theorem_path()}
    assert set(integration['files']) in [expected_files, expected_files | {CHECK_SOURCE}]
    definition_receipts = []
    for module in MODULES:
        tag = 'def-' + module
        payload = read(tag + '-payload.json')
        assert payload['definition_name'] == module and payload['private'] is True and payload['env'] == ENV
        assert payload['definition'] == (w / ('Definitions/Def_' + module + '.lean')).read_text()
        published = publication_results(tag)
        definition_receipts.extend({'module': module, 'job_id': item['id'], 'status': item['status']} for item in published)

    tag = 'prove-' + TARGET
    request, submitted, result = (read(tag + suffix) for suffix in ['-verify-request.json', '-verify-submit.json', '-verify-result.json'])
    assert request['theorem_id'] == ids[pre + TARGET] and request['proof_type'] == 'prove'
    assert request['file'] == solution_path() and request['source_sha256'] == sha(w / solution_path())
    assert (b / (tag + '-solution.lean')).read_bytes() == (w / solution_path()).read_bytes()
    assert result['id'] == submitted['submission_id'] and result['theorem_id'] == ids[pre + TARGET]
    assert result['status'] == 'ACCEPTED'
    proof = {'name': pre + TARGET, 'submission_id': submitted['submission_id'], 'status': 'ACCEPTED'}
    statuses = {}
    for name in [TARGET, PARENT]:
        before, after = read('platform-before-' + name + '.json'), read('platform-after-' + name + '.json')
        assert before['theorem_id'] == after['theorem_id']
        assert after['theorem_name'] == pre + name and after['visibility'] == 'private' and after['mathlib_rev'] == ENV
        assert before['formal_statement'] == after['formal_statement'], name
        assert before['status'] == 'Open', (name, before['status'])
        assert after['status'] == ('Proved' if name == TARGET else 'Open'), (name, after['status'])
        statuses[pre + name] = after['status']

    actual, baseline = graph_summary(read('root-graph-after.json')), graph_summary(read('root-graph-before.json'))
    by_name = {node['theorem_name']: node for node in actual['mathematical'].values()}
    before_names = {node['theorem_name']: node for node in baseline['mathematical'].values()}
    assert set(actual['mathematical']) == set(baseline['mathematical']), 'No mathematical node may be added or lost'
    assert actual['dependency_pairs'] == baseline['dependency_pairs'], 'No reduction dependency changes in direct proof'
    assert actual['counts'] == baseline['counts'], 'Mathematical graph counts must remain unchanged'
    canonical = lambda values: sorted(values, key=lambda item: (item['parent'], item['submission_id']))
    assert canonical(actual['reductions']) == canonical(baseline['reductions']), 'No new or changed reduction'
    assert by_name[pre + TARGET]['theorem_id'] == ids[pre + TARGET]
    assert by_name[pre + TARGET]['status'] == 'Proved' and by_name[pre + PARENT]['status'] == 'Open'
    assert by_name[ROOT_NAME]['status'] != 'Proved', 'This unit does not close the mathematical root'
    assert all(node['status'] == before_names[name]['status'] for name, node in by_name.items() if name != pre + TARGET)
    frontier, prior_frontier = read('root-frontier-after.json'), read('root-frontier-before.json')
    for current in [frontier, prior_frontier]:
        assert current['all_pages_fetched'] and len(current['open_leaves']) == current['total']
        assert len({item['theorem_id'] for item in current['open_leaves']}) == current['total']
    prior_ids = {item['theorem_id'] for item in prior_frontier['open_leaves']}
    final_ids = {item['theorem_id'] for item in frontier['open_leaves']}
    assert ids[pre + TARGET] in prior_ids and final_ids == prior_ids - {ids[pre + TARGET]}
    assert frontier['total'] == prior_frontier['total'] - 1
    for item in frontier['open_leaves']:
        assert item['theorem_name'] in by_name and by_name[item['theorem_name']]['theorem_id'] == item['theorem_id']

    # Keep every terminal attempt, including failed attempts, with unknown data as null.
    records, seen = [], set()
    terminal = {'succeeded', 'failed', 'timeout', 'oom_killed', 'cancelled', 'interrupted', 'scheduler_error'}
    for path in sorted(b.rglob('*-result.json')):
        receipt = json.loads(path.read_text())
        if not all(key in receipt for key in ['request', 'resources', 'result', 'job_id']) or receipt['job_id'] in seen:
            continue
        seen.add(receipt['job_id'])
        q, out, resources = receipt['request'], receipt['result'], receipt['resources']
        assert receipt['status'] in terminal
        assert q['workspace'] == str(w) and q['exclusive'] is True
        snapshot = out.get('snapshot') or {}
        if snapshot:
            assert snapshot.get('workspace_mode') == 'exclusive_worktree' and snapshot.get('snapshot_id') is None
        else:
            assert receipt['status'] != 'succeeded'
        params = q['parameters']
        arguments = ['lean'] + (params['args'] if 'args' in params else [params['source']])
        if out.get('actual_arguments') is not None:
            assert out['actual_arguments'] == arguments
        else:
            assert receipt['status'] != 'succeeded'
        cpu, user, system = (resources.get(key) for key in ['cpu_time_seconds', 'cpu_user_seconds', 'cpu_system_seconds'])
        if all(value is not None for value in [cpu, user, system]):
            assert math.isclose(cpu, user + system), receipt['job_id']
        if q['task_type'] == 'leaf' and receipt['status'] == 'succeeded' and resources.get('peak_rss_bytes') is not None:
            assert resources['peak_rss_bytes'] <= 16 * 1024 ** 3, receipt['job_id']
        manifest = q['worktree_manifest']
        records.append({
            'job_id': receipt['job_id'], 'status': receipt['status'], 'receipt': str(path.relative_to(w)),
            'input_version': manifest.get('input_version'), 'source_sha256': manifest.get('source_sha256'),
            'actual_arguments': arguments, 'exit_code': out.get('exit_code'), 'workspace': q['workspace'],
            'workspace_mode': snapshot.get('workspace_mode'), 'snapshot_id': snapshot.get('snapshot_id'),
            **{key: resources.get(key) for key in ['wall_time_seconds', 'cpu_time_seconds', 'cpu_user_seconds', 'cpu_system_seconds', 'peak_rss_bytes', 'peak_pss_bytes']},
            'resource_source': resources.get('source', 'MCP-CI process-tree physical RSS; source field not supplied'),
            'degraded': resources.get('degraded'), 'diagnostics': out.get('diagnostics'),
            'review_passed': (out.get('review') or {}).get('passed'),
        })
    assert records
    def total(key):
        return sum(record[key] for record in records) if all(record[key] is not None for record in records) else None

    regp = w / '.local/adaptation/platform-node-registry.json'
    registry = json.loads(regp.read_text())
    baseline_direct = {item['name']: item for item in read('registry-before.json').get('direct_closed_proofs', [])}
    current_direct = {item['name']: item for item in registry.get('direct_closed_proofs', [])}
    assert pre + TARGET not in baseline_direct
    direct = baseline_direct | {pre + TARGET: proof}
    assert current_direct in [baseline_direct, direct], 'Unrelated registry direct proof changed after baseline'
    assert all(item['status'] == 'ACCEPTED' and by_name[name]['status'] == 'Proved' for name, item in direct.items())
    counts = actual['counts'] | {'open_frontier': frontier['total'], 'direct_closed_children': len(direct)}
    before_counts = baseline['counts'] | {'open_frontier': prior_frontier['total'], 'direct_closed_children': len(baseline_direct)}
    save('graph-count-evidence.json', {
        'before': before_counts, 'after': counts, 'counts_are_derived_from_actual_graph': True,
        'mathematical_nodes_unchanged': True, 'reductions_unchanged': True, 'dependency_pairs_unchanged': True,
        'definitions_excluded_from_mathematical_nodes_and_edges': True,
        'only_frontier_change': pre + TARGET, 'frontier_all_pages_fetched': True,
        'direct_proof_count_delta': 1, 'frontier_count_delta': -1,
    })
    summary = {
        'scope': integration['scope'], 'records': records,
        'succeeded': sum(item['status'] == 'succeeded' for item in records),
        'failed': sum(item['status'] == 'failed' for item in records),
        'failed_or_other_terminal': sum(item['status'] != 'succeeded' for item in records),
        **{key: total(key) for key in ['wall_time_seconds', 'cpu_time_seconds', 'cpu_user_seconds', 'cpu_system_seconds']},
        'peak_rss_bytes': max((item['peak_rss_bytes'] for item in records if item['peak_rss_bytes'] is not None), default=None),
        'missing_memory_or_cpu_values_mean': 'unknown, not zero', 'closed_direct': [proof],
        'platform_statuses': statuses, 'remaining_new_open': 0, 'mathematical_root_proved': False,
        'parent_remains_open': pre + PARENT,
        'production_gate_scope': 'Existing production aggregate is a gate, not mathematical proof closure.',
    }
    save('unit-ci-summary.json', summary)
    registry['published_nodes'] = sorted(({'name': node['theorem_name'], 'id': ident} for ident, node in actual['mathematical'].items() if ident != ROOT_ID), key=lambda item: item['name'])
    registry['edges'] = canonical(actual['reductions'])
    registry['accepted_platform_reductions'] = counts['accepted_reductions']
    registry['dependency_edges'] = counts['dependency_edges']
    registry['graph_counts'] = counts
    registry['direct_closed_proofs'] = sorted(direct.values(), key=lambda item: item['name'])
    registry['platform_statuses'] = registry.get('platform_statuses', {}) | {name: node['status'] for name, node in by_name.items()}
    registry['open_frontier'] = [item['theorem_name'] for item in frontier['open_leaves']]
    registry.update(local_open_children_below_root=frontier['total'], published_open_children_below_root=frontier['total'], mathematical_root_proved=False)
    registry['derivative_finite_sourceproof_unit'] = {
        'source': UNIT, 'closed_direct': [proof], 'new_children': [], 'new_reductions': [],
        'remaining_new_open': 0, 'parent_remains_open': pre + PARENT,
        'all_frontier_pages_fetched': True, 'source_ledger_link': UNIT_REL + 'source-ledger-link.json',
    }
    registry.setdefault('graph_validation', {}).update(root_frontier_all_pages_fetched=True, derivative_finite_direct_proof_preserves_mathematical_graph=True)
    registry['recorded_at'] = datetime.now(timezone.utc).isoformat()

    # Remove exactly the delivered paragraph. Every other paragraph is preserved.
    pending_path = r / 'docs/Prove2Me适配状态.md'
    original = pending_path.read_text()
    paragraphs = original.split('\n\n')
    matches = [index for index, paragraph in enumerate(paragraphs) if paragraph.startswith('`Proper.' + TARGET + '`')]
    assert len(matches) <= 1
    if matches:
        del paragraphs[matches[0]]
    pending_path.write_text('\n\n'.join(paragraphs))
    # No development-plan file or checkbox is read, rewritten, or staged by this script.
    save('current-source-consumer.json', {
        'source_pin': PIN, 'original_delivery_ledger': 'source-consumer.json',
        'source_boundary_link': 'source-ledger-link.json', 'definition_hashes': validation['definition_hashes'],
        'theorem_hashes': validation['theorem_hashes'], 'declaration_graph_sha256': validation['declaration_graph_sha256'],
        'closed_direct': [proof], 'new_open_children': [], 'new_reductions': [],
        'actual_platform_states': statuses, 'new_global_assumptions': [], 'full_abc_closed': False,
        'consumer_chain': read('source-consumer.json')['producers'],
        'parent_remains_open': pre + PARENT,
        'source_notices': 'Pinned source copyright, author notices, and Apache-2.0 license retained.',
    })
    integration.update(status='Two private Definitions PUBLISHED; existing derivative-finiteness proof ACCEPTED and Proved; no new child or reduction.', direct_proofs=[proof], definition_receipts=definition_receipts, platform_statuses=statuses, remaining_new_open=0, mathematical_root_proved=False)
    save('integration.json', integration)
    here = Path(__file__).resolve().parent
    for name in ['delivery_common.py', 'graph_completion.py', 'platform_publish.py', 'finalize.py']:
        source, target = here / name, b / name
        if source.resolve() != target.resolve():
            shutil.copyfile(source, target)
    files = ['docs/Prove2Me适配状态.md', str(regp.relative_to(r))]
    files += [str((w / relative).relative_to(r)) for relative in sorted(expected_files | {CHECK_SOURCE})]
    files += [str(path.relative_to(r)) for path in sorted(b.rglob('*')) if path.is_file() and '__pycache__' not in path.parts]
    files = list(dict.fromkeys(files))
    assert 'docs/开发计划.Prove2Me适配.md' not in files
    already_staged = set(subprocess.check_output(['git', 'diff', '--cached', '--name-only', '-z'], cwd=r).decode().split('\0')) - {''}
    assert already_staged <= set(files), ('Unrelated paths already staged', sorted(already_staged - set(files)))
    credentials = json.loads((w / 'credentials.json').read_text())
    secrets = [value.encode() for key, value in credentials.items() if key in ['access_token', 'refresh_token', 'api_key', 'token'] and isinstance(value, str) and len(value) >= 16]
    for relative in files:
        path = r / relative
        assert path.is_file() and not path.is_symlink(), relative
        assert path.name not in ['credentials.json', '.env'] and path.suffix not in ['.pem', '.key'], relative
        data = path.read_bytes()
        assert not any(value in data for value in secrets), relative
        assert (b'p2m_' + b'eyJ') not in data and (b'"access_' + b'token": "eyJ') not in data, relative
        if path != regp:
            registry.setdefault('files', {})[relative] = sha(path)
    regp.write_text(json.dumps(registry, ensure_ascii=False, indent=2) + '\n')
    assert not any(value in regp.read_bytes() for value in secrets)
    subprocess.run(['git', 'diff', '--check', '--'] + files, cwd=r, check=True)
    subprocess.run(['git', 'add', '-f', '--'] + files, cwd=r, check=True)
    subprocess.run(['git', 'diff', '--cached', '--check'], cwd=r, check=True)
    print(json.dumps({'staged_paths': len(files), 'graph_counts': counts, 'closed_direct': [proof], 'parent_remains_open': pre + PARENT, 'mathematical_root_proved': False}, ensure_ascii=False), flush=True)


if __name__ == '__main__':
    main()
