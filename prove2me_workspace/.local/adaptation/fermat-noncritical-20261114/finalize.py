from pathlib import Path
from datetime import datetime, timezone
import hashlib
import json
import math
import shutil
import subprocess

from delivery_common import (
    CHILDREN, ENV, EVIDENCE, MODULES, PARENTS, PREFIX, RIEMANN,
    ROOT_DIR, ROOT_ID, ROOT_NAME, UNIT_REL, WORKSPACE, graph_summary,
    preflight, publication_results, read, save, sha,
)

w, b, r, pre = WORKSPACE, EVIDENCE, ROOT_DIR, PREFIX
validation, items, existing_ids = preflight()
integration = read('integration.json')
expected_files = {'Definitions/Def_' + name + '.lean' for name in MODULES}
expected_files |= {'Theorems/Thm_' + (pre + name).replace('.', '_') + '.lean' for name in CHILDREN + PARENTS}
assert set(integration['files']) == expected_files and len(integration['files']) == len(expected_files)

# Require terminal Definition receipts for the exact validated local code.
definition_receipts = []
for module in MODULES:
    tag = 'def-' + module
    payload = read(tag + '-payload.json')
    assert payload['definition_name'] == module and payload['private'] is True and payload['env'] == ENV
    assert payload['definition'] == (w / ('Definitions/Def_' + module + '.lean')).read_text()
    published = publication_results(tag)
    assert len(published) == 1
    definition_receipts.extend({'module': module, 'job_id': item['id'], 'status': item['status']} for item in published)

child_payload = read('noncritical-children-payload.json')
assert child_payload['env'] == ENV and child_payload['private'] is True
assert len(child_payload['problems']) == len(CHILDREN)
assert {item['theorem_name'] for item in child_payload['problems']} == {pre + name for name in CHILDREN}
plain_items = {item['theorem_name']: item for item in items}
for item in child_payload['problems']:
    original = plain_items[item['theorem_name']]
    for field in ['preamble', 'formal_statement']:
        assert item[field] == original[field], (item['theorem_name'], field)
child_results = publication_results('noncritical-children')
assert len(child_results) == len(CHILDREN)
ids = {item['theorem_name']: item['theorem_id'] for item in child_results}
assert ids == read('published-child-ids.json') and set(ids) == {pre + name for name in CHILDREN}

proofs = {}
for name, tag, expected in [('cuspsFinite', 'prove-cuspsFinite', 'ACCEPTED'),
                             ('noncriticalSelection', 'reduce-noncriticalSelection', 'SKETCH_ACCEPTED')]:
    request = read(tag + '-verify-request.json')
    submitted, result = read(tag + '-verify-submit.json'), read(tag + '-verify-result.json')
    relative = UNIT_REL + 'Solution_' + name + '.lean'
    assert request['theorem_id'] == existing_ids[pre + name] and request['file'] == relative
    assert request['proof_type'] == 'prove' and request['source_sha256'] == sha(w / relative)
    assert (b / (tag + '-solution.lean')).read_bytes() == (w / relative).read_bytes()
    assert result['id'] == submitted['submission_id'] and result['theorem_id'] == existing_ids[pre + name]
    assert result['status'] == expected, (name, result['status'])
    proofs[name] = {'name': pre + name, 'submission_id': submitted['submission_id'], 'status': result['status']}

statuses = {}
for name in CHILDREN + PARENTS:
    current = read('platform-after-' + name + '.json')
    assert current['theorem_id'] == (ids if name in CHILDREN else existing_ids)[pre + name]
    assert current['theorem_name'] == pre + name and current['visibility'] == 'private' and current['mathlib_rev'] == ENV
    assert current['status'] == ('Proved' if name == 'cuspsFinite' else 'Open'), (name, current['status'])
    if name in PARENTS:
        before = read('platform-before-' + name + '.json')
        assert before['theorem_id'] == current['theorem_id']
        assert before['formal_statement'] == current['formal_statement'], name
    statuses[pre + name] = current['status']

graph = read('root-graph-after.json')
actual = graph_summary(graph)
by_name = {node['theorem_name']: node for node in actual['mathematical'].values()}
for name, status in statuses.items():
    assert by_name[name]['status'] == status
    assert by_name[name]['theorem_id'] == (ids | existing_ids)[name]
reduction = [edge for edge in actual['reductions'] if edge['submission_id'] == proofs['noncriticalSelection']['submission_id']]
assert len(reduction) == 1
assert reduction[0]['parent'] == pre + 'noncriticalSelection'
assert reduction[0]['status'] == 'SKETCH_ACCEPTED'
assert set(reduction[0]['children']) == {pre + name for name in CHILDREN + RIEMANN}
assert all(by_name[pre + name]['status'] == 'Proved' for name in RIEMANN)
assert by_name[ROOT_NAME]['status'] != 'Proved', 'This unit does not close the mathematical root'

frontier = read('root-frontier-after.json')
assert frontier['all_pages_fetched'] and len(frontier['open_leaves']) == frontier['total']
assert len({item['theorem_id'] for item in frontier['open_leaves']}) == frontier['total']
frontier_names = {item['theorem_name'] for item in frontier['open_leaves']}
assert {pre + name for name in CHILDREN} <= frontier_names
assert not {pre + name for name in PARENTS} & frontier_names
for item in frontier['open_leaves']:
    assert item['theorem_name'] in by_name and by_name[item['theorem_name']]['theorem_id'] == item['theorem_id']

# Preserve every terminal compile attempt and its actual scheduler resource data.
records, seen_jobs = [], set()
for path in sorted(b.rglob('*-result.json')):
    receipt = json.loads(path.read_text())
    if not all(key in receipt for key in ['request', 'resources', 'result', 'job_id']):
        continue
    if receipt['job_id'] in seen_jobs:
        continue
    seen_jobs.add(receipt['job_id'])
    request, result, resources = receipt['request'], receipt['result'], receipt['resources']
    assert receipt['status'] in ['succeeded', 'failed', 'timeout', 'oom_killed', 'cancelled', 'interrupted', 'scheduler_error']
    assert request['workspace'] == str(w) and request['exclusive'] is True
    snapshot = result.get('snapshot') or {}
    if snapshot:
        assert snapshot.get('workspace_mode') == 'exclusive_worktree' and snapshot.get('snapshot_id') is None
    else:
        assert receipt['status'] != 'succeeded', receipt['job_id']
    parameters = request['parameters']
    arguments = ['lean'] + (parameters['args'] if 'args' in parameters else [parameters['source']])
    if result.get('actual_arguments') is not None:
        assert result['actual_arguments'] == arguments
    else:
        assert receipt['status'] != 'succeeded', receipt['job_id']
    cpu, user, system = (resources.get(key) for key in ['cpu_time_seconds', 'cpu_user_seconds', 'cpu_system_seconds'])
    if cpu is not None and user is not None and system is not None:
        assert math.isclose(cpu, user + system), receipt['job_id']
    if receipt['status'] == 'succeeded' and request['task_type'] == 'leaf' and resources.get('peak_rss_bytes') is not None:
        assert resources['peak_rss_bytes'] <= 16 * 1024 ** 3, receipt['job_id']
    manifest = request['worktree_manifest']
    records.append({
        'job_id': receipt['job_id'], 'status': receipt['status'], 'receipt': str(path.relative_to(w)),
        'input_version': manifest.get('input_version'), 'source_sha256': manifest.get('source_sha256'),
        'actual_arguments': arguments, 'exit_code': result.get('exit_code'), 'workspace': request['workspace'],
        'workspace_mode': snapshot.get('workspace_mode'), 'snapshot_id': snapshot.get('snapshot_id'),
        **{key: resources.get(key) for key in ['wall_time_seconds', 'cpu_time_seconds', 'cpu_user_seconds', 'cpu_system_seconds', 'peak_rss_bytes', 'peak_pss_bytes']},
        'resource_source': resources.get('source', 'MCP-CI process-tree physical RSS; source field not supplied'),
        'degraded': resources.get('degraded'), 'diagnostics': result.get('diagnostics'),
        'review_passed': (result.get('review') or {}).get('passed'),
    })
assert records
def total(key):
    return sum(record[key] for record in records) if all(record[key] is not None for record in records) else None

before_actual = graph_summary(read('root-graph-before.json'))
assert set(actual['mathematical']) == set(before_actual['mathematical']) | set(ids.values()), 'Mathematical graph coverage changed'
save('graph-overview-completeness.json', {'requested_depth':10,'actual_depth':graph['depth'],'warning':graph.get('warning'),'mathematical_ids_equal_baseline_plus_three_new_children':True,'omitted_edges_only_definitions':True,'frontier_all_pages_fetched':True})
regp = w / '.local/adaptation/platform-node-registry.json'
registry = json.loads(regp.read_text())
old_direct = registry.get('direct_closed_proofs', [])
direct = {proof['name']: proof for proof in old_direct}
direct[pre + 'cuspsFinite'] = proofs['cuspsFinite']
assert all(proof['status'] == 'ACCEPTED' and by_name[name]['status'] == 'Proved' for name, proof in direct.items())
counts = actual['counts'] | {'open_frontier': frontier['total'], 'direct_closed_children': len(direct)}
summary = {
    'scope': integration['scope'], 'records': records,
    'resource_estimate_deviation': {'job_id':'ci-010176-78ccc9c3','source':'Solutions/Checks_FermatNoncriticalReduction.lean','expected_memory_requested':'8GiB','required_first_leaf_estimate':'16GiB','result':'succeeded','peak_rss_bytes':4223152128,'corrective_action':'Future first leaf audit checks use 60s/16GiB; no unnecessary recompile of this already succeeded source.'},
    'succeeded': sum(record['status'] == 'succeeded' for record in records),
    'failed': sum(record['status'] == 'failed' for record in records),
    'failed_or_other_terminal': sum(record['status'] != 'succeeded' for record in records),
    **{key: total(key) for key in ['wall_time_seconds', 'cpu_time_seconds', 'cpu_user_seconds', 'cpu_system_seconds']},
    'peak_rss_bytes': max((record['peak_rss_bytes'] for record in records if record['peak_rss_bytes'] is not None), default=None),
    'missing_memory_or_cpu_values_mean': 'unknown, not zero', 'platform_statuses': statuses,
    'closed_direct': [proofs['cuspsFinite']], 'accepted_reduction': proofs['noncriticalSelection'],
    'remaining_new_open': [pre + name for name in CHILDREN], 'root_proved': False,
}
save('unit-ci-summary.json', summary)
save('graph-count-evidence.json', {
    'before': before_actual['counts'], 'after': counts,
    'expected_from_unchanged_baseline': {'accepted_reductions': 13, 'published_children': 46, 'open_frontier': 28, 'direct_closed_children': 6, 'dependency_edges': 51},
    'counts_are_derived_from_actual_graph': True,
    'definitions_excluded_from_mathematical_nodes_and_edges': True,
    'new_reduction_dependencies': reduction[0],
})
registry['published_nodes'] = sorted(({'name': node['theorem_name'], 'id': node['theorem_id']}
                                      for ident, node in actual['mathematical'].items() if ident != ROOT_ID), key=lambda item: item['name'])
registry['edges'] = sorted(actual['reductions'], key=lambda item: (item['parent'], item['submission_id']))
registry['accepted_platform_reductions'] = counts['accepted_reductions']
registry['dependency_edges'] = counts['dependency_edges']
registry['graph_counts'] = counts
registry['direct_closed_proofs'] = sorted(direct.values(), key=lambda item: item['name'])
registry['platform_statuses'] = registry.get('platform_statuses', {}) | {name: node['status'] for name, node in by_name.items()}
registry['open_frontier'] = [item['theorem_name'] for item in frontier['open_leaves']]
registry.update(local_open_children_below_root=frontier['total'], published_open_children_below_root=frontier['total'], mathematical_root_proved=False)
registry['noncritical_unit'] = {
    'source': 'fermat-noncritical-20261114', 'children': ids,
    'closed_direct': [proofs['cuspsFinite']], 'reduction': proofs['noncriticalSelection'],
    'dependencies': reduction[0]['children'], 'remaining_new_open': len(CHILDREN),
    'all_frontier_pages_fetched': True, 'source_ledger_link': UNIT_REL + 'source-ledger-link.json',
}
registry.setdefault('graph_validation', {}).update(root_frontier_all_pages_fetched=True, root_graph_depth_used=graph['depth'],
                                                  noncritical_parent_and_six_actual_dependencies_present=True)
registry['recorded_at'] = datetime.now(timezone.utc).isoformat()

# Replace only the completed parent paragraph with the three actual Open children.
paragraphs = (r / 'docs/Prove2Me适配状态.md').read_text().split('\n\n')
old = [i for i, paragraph in enumerate(paragraphs) if paragraph.startswith('`Proper.noncriticalSelection`')]
new_paragraphs = [
    '`Proper.noncriticalRamificationFinite` 仍需证明任意实际非常数函数 ψ 的分歧处集有限。应在全部真赋值处上，使用实际导数 d/dψ 对正则局部环的保持性、图册的有限个模生成元及 ψ 的有限极点集，证明 `{P | 1 < ramIdx ψ P}` 有限；不能以预先给定的有限分歧值集代替该结论。',
    '`Proper.noncriticalCompositionRamification` 仍需证明实际分歧指数为正，以及每个有理 Möbius 变换／正次数有理多项式列表在实际曲线函数上的复合公式。结论必须同时保留复合函数超越性、所有完整剩余域嵌入下的点值公式，以及原函数分歧指数与实际 P¹ 复合指数的乘积公式；不能只验证单个嵌入或逐点选择不同复合函数。',
    '`Proper.noncriticalP1Zero` 仍需为任意有限且对全部有理代数自同构稳定、又不含零的实际 P¹ 代数点集，构造同一个有理 Möbius 变换／正次数有理多项式列表。该复合须把整个给定集合送入 `{0,1,∞}`，把零送到其外，并把所有分歧点的像送入这三个值；来源中的有理情形、最小多项式降阶及嵌套归纳尚待移植。三个 Open 子节点共同供应既有 `noncriticalSelection` 的实际分解，父归约验收不表示这些数学义务已闭合。',
]
if old:
    assert len(old) == 1 and '`Proper.cuspsFinite`' in paragraphs[old[0]]
    assert not any(paragraph.startswith('`Proper.' + name + '`') for paragraph in paragraphs for name in CHILDREN)
    paragraphs[old[0]:old[0] + 1] = new_paragraphs
else:
    assert all(paragraphs.count(paragraph) == 1 for paragraph in new_paragraphs), 'Unexpected pending inventory state'
(r / 'docs/Prove2Me适配状态.md').write_text('\n\n'.join(paragraphs).rstrip() + '\n')

# Keep the original source-consumer candidate ledger as historical evidence.
source_link = read('source-ledger-link.json')
if 'production_ledger' in source_link and 'production_ledger_sha256' in source_link:
    assert sha(r / source_link['production_ledger']) == source_link['production_ledger_sha256']
save('current-source-consumer.json', {
    'source_pin': integration['source_pin'], 'original_delivery_ledger': 'source-consumer.json',
    'source_boundary_link': 'source-ledger-link.json', 'definition_hashes': validation['definition_hashes'],
    'source_theorem_hashes': validation['source_theorem_hashes'], 'source_graph_sha256': validation['source_graph_sha256'],
    'closed_direct': [proofs['cuspsFinite']], 'accepted_reduction': proofs['noncriticalSelection'],
    'actual_dependencies': reduction[0]['children'], 'open_mathematical_children': [pre + name for name in CHILDREN],
    'actual_platform_states': statuses,
    'consumer_chain': ['actual zero/pole supports -> model_cuspsFinite -> cuspsFinite',
                       'closed Riemann finite/upper/eventual -> actual simple-zero function',
                       'simple-zero function + finite ramification + actual composition chain rule + actual P1 list -> noncriticalSelection',
                       'cuspsFinite and conditional noncriticalSelection -> existing ArithmeticDivisorChoices/canonicalEstimate consumers'],
    'new_global_assumptions': [], 'full_abc_closed': False,
})
integration.update(status='Three Definitions PUBLISHED; three actual Open children PUBLISHED; cuspsFinite ACCEPTED; noncriticalSelection SKETCH_ACCEPTED.',
                   direct_proofs=[proofs['cuspsFinite']], reductions=[proofs['noncriticalSelection']],
                   published_children=ids, platform_statuses=statuses, remaining_new_open=len(CHILDREN))
save('integration.json', integration)
save('plan-checkbox-evidence.json', {'changed_entries': [], 'reason': 'This source reuse and three-child decomposition unit establishes no additional whole-plan or mathematical completion checkbox.'})

here = Path(__file__).resolve().parent
for name in ['delivery_common.py', 'platform_publish.py', 'finalize.py']:
    source, target = here / name, b / name
    if source.resolve() != target.resolve():
        shutil.copyfile(source, target)

files = ['docs/Prove2Me适配状态.md', str(regp.relative_to(r))]
files += [str((w / relative).relative_to(r)) for relative in integration['files']]
files += ['prove2me_workspace/Solutions/Checks_FermatNoncriticalClosed.lean',
          'prove2me_workspace/Solutions/Checks_FermatNoncriticalReduction.lean']
files += [str(path.relative_to(r)) for path in sorted(b.rglob('*')) if path.is_file() and '__pycache__' not in path.parts]
files = list(dict.fromkeys(files))
assert str((w / 'credentials.json').relative_to(r)) not in files
already_staged = set(subprocess.check_output(['git', 'diff', '--cached', '--name-only', '-z'], cwd=r).decode().split('\0')) - {''}
assert already_staged <= set(files), ('Unrelated files are already staged', sorted(already_staged - set(files)))
credentials = json.loads((w / 'credentials.json').read_text())
secrets = [value.encode() for key, value in credentials.items()
           if key in ['access_token', 'refresh_token', 'api_key', 'token'] and isinstance(value, str) and len(value) >= 16]
for relative in files:
    path = r / relative
    assert path.is_file() and not path.is_symlink(), relative
    assert path.name not in ['credentials.json', '.env'] and path.suffix not in ['.pem', '.key'], relative
    data = path.read_bytes()
    assert not any(value in data for value in secrets), relative
    assert (b'p2m_' + b'eyJ') not in data and (b'"access_' + b'token": "eyJ') not in data, relative
    if path != regp:
        registry.setdefault('files', {})[relative] = hashlib.sha256(data).hexdigest()
regp.write_text(json.dumps(registry, ensure_ascii=False, indent=2) + '\n')
assert not any(value in regp.read_bytes() for value in secrets)
subprocess.run(['git', 'diff', '--check', '--'] + files, cwd=r, check=True)
subprocess.run(['git', 'add', '-f', '--'] + files, cwd=r, check=True)
subprocess.run(['git', 'diff', '--cached', '--check'], cwd=r, check=True)
staged = set(subprocess.check_output(['git', 'diff', '--cached', '--name-only', '-z'], cwd=r).decode().split('\0')) - {''}
assert staged <= set(files)
print(json.dumps({'staged_paths': len(staged), 'graph_counts': counts,
                  'direct_closed': pre + 'cuspsFinite', 'conditional_parent': pre + 'noncriticalSelection',
                  'remaining_new_open': len(CHILDREN)}, ensure_ascii=False), flush=True)
