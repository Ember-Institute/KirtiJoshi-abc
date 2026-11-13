from pathlib import Path
from datetime import datetime, timezone
import hashlib
import json
import math
import shutil
import subprocess

from delivery_common import (
    CHILDREN, ENV, EVIDENCE, MODULES, PARENTS, PREFIX,
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

child_payload = read('canonical-children-payload.json')
assert child_payload['env'] == ENV and child_payload['private'] is True
assert len(child_payload['problems']) == len(CHILDREN)
assert {item['theorem_name'] for item in child_payload['problems']} == {pre + name for name in CHILDREN}
plain_items = {item['theorem_name']: item for item in items}
for item in child_payload['problems']:
    original = plain_items[item['theorem_name']]
    for field in ['preamble', 'formal_statement']:
        assert item[field] == original[field], (item['theorem_name'], field)
child_results = publication_results('canonical-children')
assert len(child_results) == len(CHILDREN)
ids = {item['theorem_name']: item['theorem_id'] for item in child_results}
assert ids == read('published-child-ids.json') and set(ids) == {pre + name for name in CHILDREN}

proofs = {}
for name, tag, expected in [('infinityDivisorExists', 'prove-infinityDivisorExists', 'ACCEPTED'),
                             ('canonicalDivisorDegree', 'reduce-canonicalDivisorDegree', 'SKETCH_ACCEPTED')]:
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
    assert current['status'] == ('Proved' if name == 'infinityDivisorExists' else 'Open'), (name, current['status'])
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
reduction = [edge for edge in actual['reductions'] if edge['submission_id'] == proofs['canonicalDivisorDegree']['submission_id']]
assert len(reduction) == 1
assert reduction[0]['parent'] == pre + 'canonicalDivisorDegree'
assert reduction[0]['status'] == 'SKETCH_ACCEPTED'
assert set(reduction[0]['children']) == {pre + name for name in CHILDREN}
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
save('graph-overview-completeness.json', {'requested_depth':10,'actual_depth':graph['depth'],'warning':graph.get('warning'),'mathematical_ids_equal_baseline_plus_one_new_child':True,'omitted_edges_only_definitions':True,'frontier_all_pages_fetched':True})
regp = w / '.local/adaptation/platform-node-registry.json'
registry = json.loads(regp.read_text())
old_direct = registry.get('direct_closed_proofs', [])
direct = {proof['name']: proof for proof in old_direct}
direct[pre + 'infinityDivisorExists'] = proofs['infinityDivisorExists']
assert all(proof['status'] == 'ACCEPTED' and by_name[name]['status'] == 'Proved' for name, proof in direct.items())
counts = actual['counts'] | {'open_frontier': frontier['total'], 'direct_closed_children': len(direct)}
summary = {
    'scope': integration['scope'], 'records': records,
    'succeeded': sum(record['status'] == 'succeeded' for record in records),
    'failed': sum(record['status'] == 'failed' for record in records),
    'failed_or_other_terminal': sum(record['status'] != 'succeeded' for record in records),
    **{key: total(key) for key in ['wall_time_seconds', 'cpu_time_seconds', 'cpu_user_seconds', 'cpu_system_seconds']},
    'peak_rss_bytes': max((record['peak_rss_bytes'] for record in records if record['peak_rss_bytes'] is not None), default=None),
    'missing_memory_or_cpu_values_mean': 'unknown, not zero', 'platform_statuses': statuses,
    'closed_direct': [proofs['infinityDivisorExists']], 'accepted_reduction': proofs['canonicalDivisorDegree'],
    'remaining_new_open': [pre + name for name in CHILDREN], 'root_proved': False,
}
save('unit-ci-summary.json', summary)
save('graph-count-evidence.json', {
    'before': before_actual['counts'], 'after': counts,
    'expected_from_unchanged_baseline': {'accepted_reductions': 14, 'published_children': 47, 'open_frontier': 27, 'direct_closed_children': 7, 'dependency_edges': 52},
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
registry['canonical_coordinate_unit'] = {
    'source': 'fermat-canonical-decomposition-20261114', 'children': ids,
    'closed_direct': [proofs['infinityDivisorExists']], 'reduction': proofs['canonicalDivisorDegree'],
    'dependencies': reduction[0]['children'], 'remaining_new_open': len(CHILDREN),
    'all_frontier_pages_fetched': True, 'source_ledger_link': UNIT_REL + 'source-ledger-link.json',
}
registry.setdefault('graph_validation', {}).update(root_frontier_all_pages_fetched=True, root_graph_depth_used=graph['depth'],
                                                  canonical_parent_and_one_actual_dependency_present=True)
registry['recorded_at'] = datetime.now(timezone.utc).isoformat()

# Preserve unrelated canonical/adjunction/generator debts while replacing the delivered part.
pending_path = r / 'docs/Prove2Me适配状态.md'
paragraphs = pending_path.read_text().split('\n\n')
old = [i for i, paragraph in enumerate(paragraphs) if paragraph.startswith('`Proper.canonicalDivisorExists`')]
assert len(old) == 1
old_paragraph = paragraphs[old[0]]
remaining = (
    '`Proper.canonicalDivisorExists` 仍需证明 `du` 除子的有限支撑；'
    '`Proper.planeAdjunctionExists` 仍需证明实际典范除子与坐标超平面除子之间的具体伴随关系。'
    '应逐处追踪分歧系数，并保留原来的实际 `K`、`H` 和 `J` 契约；'
    '不能把预先定义的数字当作除子身份或次数等式。'
    '`Proper.cuspGeneratorsExists` 还需给出尖点补集的实际坐标环有限生成性，并包含所需的三个三支点函数。'
)
child_debt = (
    '`Proper.coordinatePoleMultiplicity_eq` 仍需证明：对于满足 `0 < N` 的既有实际 Fermat 模型，'
    '两个固定坐标 u、v 在每个真赋值处的实际极点重数 `max(0,-ord)` 相等。'
    '必须覆盖全部正则处、坐标为零的情形以及无穷点；不得只证明极点支撑相同或排除零坐标。'
    '这是新的明确 Fermat 特化义务，固定的 Belyi／Heights 来源及论文引文均未提供其证明。'
    '其结论将实际超平面除子识别为 u 的实际极除子，再由已验收的纤维次数公式和主除子次数为零，'
    '结合原有实际伴随数据得到典范次数；`canonicalDivisorDegree` 的归约验收不关闭该子义务，'
    '也不证明典范除子或伴随数据的存在性。'
)
if '`Proper.infinityDivisorExists`' in old_paragraph or '`Proper.canonicalDivisorDegree`' in old_paragraph:
    assert all('`Proper.' + name + '`' in old_paragraph for name in
               ['canonicalDivisorExists', 'infinityDivisorExists', 'planeAdjunctionExists', 'canonicalDivisorDegree', 'cuspGeneratorsExists'])
    assert not any(paragraph.startswith('`Proper.coordinatePoleMultiplicity_eq`') for paragraph in paragraphs)
    paragraphs[old[0]:old[0] + 1] = [remaining, child_debt]
else:
    assert old_paragraph == remaining and paragraphs.count(child_debt) == 1, 'Unexpected pending inventory state'
assert all(sum('`Proper.' + name + '`' in paragraph for paragraph in paragraphs) >= 1
           for name in ['canonicalDivisorExists', 'planeAdjunctionExists', 'cuspGeneratorsExists'])
pending_path.write_text('\n\n'.join(paragraphs).rstrip() + '\n')

# Keep the original source-consumer candidate ledger as historical evidence.
source_link = read('source-ledger-link.json')
if 'production_ledger' in source_link and 'production_ledger_sha256' in source_link:
    assert sha(r / source_link['production_ledger']) == source_link['production_ledger_sha256']
source_pins = read('source-consumer.json')['reference_commits']
assert source_pins == {'belyi': '9ce4d3f793d3bc831f2fc7214b7dbad90ea012d8',
                       'heights': '721496ca4c158e511d25d8ccf6bfe8503eda73c1'}
save('current-source-consumer.json', {
    'source_pins': source_pins, 'original_delivery_ledger': 'source-consumer.json',
    'source_boundary_link': 'source-ledger-link.json', 'definition_hashes': validation['definition_hashes'],
    'source_theorem_hashes': validation['source_theorem_hashes'], 'source_graph_sha256': validation['source_graph_sha256'],
    'closed_direct': [proofs['infinityDivisorExists']], 'accepted_reduction': proofs['canonicalDivisorDegree'],
    'actual_dependencies': reduction[0]['children'], 'open_mathematical_children': [pre + name for name in CHILDREN],
    'actual_platform_states': statuses,
    'consumer_chain': ['existing finite coordinate supports -> actual max-pole Finsupp -> unchanged InfinityDivisorData -> infinityDivisorExists',
                       'Open all-place coordinate-pole equality -> conditional H=polar(u) -> existing actual fiber degree gives degree(H)=N',
                       'original actual J.coefficient + existing principal/divisor degree laws -> conditional canonicalDivisorDegree',
                       'existing actual arithmeticDivisorChoices/canonical-height/divisor comparison consumers'],
    'new_global_assumptions': [], 'full_abc_closed': False,
    'new_specialization_proof_supplied': False,
    'pinned_source_proof_for_coordinatePoleMultiplicity_eq_claimed': False,
    'excluded_research_proof': 'The old unapproved Fermat common-pole proof is neither copied nor imported.',
    'other_open_parents_unchanged': ['canonicalDivisorExists', 'planeAdjunctionExists', 'cuspGeneratorsExists'],
})

integration.update(status='Two Definitions PUBLISHED; one actual Open coordinate-pole child PUBLISHED; infinityDivisorExists ACCEPTED; canonicalDivisorDegree SKETCH_ACCEPTED.',
                   direct_proofs=[proofs['infinityDivisorExists']], reductions=[proofs['canonicalDivisorDegree']],
                   published_children=ids, platform_statuses=statuses, remaining_new_open=len(CHILDREN))
save('integration.json', integration)
save('plan-checkbox-evidence.json', {'changed_entries': [], 'reason': 'This source reuse and one-child canonical decomposition unit establishes no additional whole-plan or mathematical completion checkbox.'})

here = Path(__file__).resolve().parent
for name in ['delivery_common.py', 'platform_publish.py', 'finalize.py']:
    source, target = here / name, b / name
    if source.resolve() != target.resolve():
        shutil.copyfile(source, target)

files = ['docs/Prove2Me适配状态.md', str(regp.relative_to(r))]
files += [str((w / relative).relative_to(r)) for relative in integration['files']]
files += ['prove2me_workspace/Solutions/Checks_FermatCanonicalCoordinateClosed.lean',
          'prove2me_workspace/Solutions/Checks_FermatCanonicalCoordinateReduction.lean']
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
    assert path.name != 'Def_FermatInfinityDivisor.lean', 'Unapproved research proof is outside this delivery'
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
                  'direct_closed': pre + 'infinityDivisorExists', 'conditional_parent': pre + 'canonicalDivisorDegree',
                  'remaining_new_open': len(CHILDREN)}, ensure_ascii=False), flush=True)
