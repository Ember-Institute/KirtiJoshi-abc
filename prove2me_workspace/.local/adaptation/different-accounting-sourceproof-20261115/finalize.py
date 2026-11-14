"""Finalize the existing different-accounting theorem's accepted direct proof.

No CI, API, compilation or Git mutations. The root agent reviews and stages
explicit allowlisted files separately. Import does not write.
"""
from pathlib import Path
from datetime import datetime, timezone
import hashlib
import importlib.util
import json
import math
import subprocess

b = Path('/home/admin-wsl/Coq/abc/prove2me_workspace/.local/adaptation/different-accounting-sourceproof-20261115')
spec = importlib.util.spec_from_file_location('different_accounting_delivery', b / 'delivery.py')
unit = importlib.util.module_from_spec(spec)
spec.loader.exec_module(unit)
r, w, read, save, sha = unit.r, unit.w, unit.read, unit.save, unit.sha
PRE = 'AbcAdaptation.Tripod.Fermat.Proper.'
TARGET = PRE + 'belyiActualFieldDifferentAccounting'
TARGET_ID = 'd7edb0f4-a7cb-4ab5-8cf1-46eea7d81aa3'
SOURCE = 'Solutions/Source_FermatBelyiDifferentAccounting.lean'
WRAPPER = 'Theorems/Thm_AbcAdaptation_Tripod_Fermat_Proper_belyiActualFieldDifferentAccounting.lean'
CHECKS = 'Solutions/Checks_FermatBelyiDifferentAccounting.lean'
PARENT = PRE + 'belyiActualFieldConductorExtension'
LOCAL = PRE + 'belyiActualFieldLocalConductorComparison'
COMPARISON = PRE + 'belyiDifferentConductorComparison'
CANONICAL = 'AbcAdaptation.Tripod.Fermat.canonicalEstimate'
ROOT = 'abc.goal.lt_constant_mul_fix'
STANDARD = {'propext', 'Classical.choice', 'Quot.sound'}
TERMINAL = {'succeeded', 'failed', 'timeout', 'oom_killed', 'cancelled', 'interrupted', 'scheduler_error'}
FINAL_OUTPUTS = {'source-consumer.json', 'pending-db-scope.json',
                 'graph-count-evidence.json', 'unit-ci-summary.json', 'integration.json'}
BEFORE = {'accepted_reductions': 36, 'published_children': 83, 'dependency_edges': 101,
          'open_frontier': 18, 'direct_closed_children': 40}
AFTER = {'accepted_reductions': 36, 'published_children': 83, 'dependency_edges': 101,
         'open_frontier': 17, 'direct_closed_children': 41}


def theorem_path(name):
    return 'Theorems/Thm_' + name.replace('.', '_') + '.lean'

def git(*args):
    return subprocess.check_output(['git', *args], cwd=r)

def index_entries():
    entries = {}
    for entry in git('ls-files', '--stage', '-z').split(b'\0'):
        if entry:
            metadata, path = entry.split(b'\t', 1)
            entries.setdefault(path.decode(), []).append(metadata)
    return entries

def approved_unit_files():
    """The root agent reviews this exact unit-relative list before execution."""
    approved = read('unit-evidence-allowlist.json')
    assert isinstance(approved, list) and approved and all(isinstance(name, str) for name in approved)
    assert len(approved) == len(set(approved)), 'Duplicate approved unit path'
    for name in approved:
        path = Path(name)
        assert not path.is_absolute() and path.as_posix() == name and '\\' not in name
        assert not {'.', '..', '__pycache__'} & set(path.parts)
        assert path.suffix != '.pyc' and path.name != 'credentials.json'
        assert name != 'staging-candidates.json', 'Review packet is an output, not an allowlist input'
        full = b / path
        assert not full.is_symlink() and full.resolve().is_relative_to(b.resolve())
        assert full.is_file() or name in FINAL_OUTPUTS, ('Approved unit file missing', name)
    return approved

def ci_records(required, approved):
    """Inventory every terminal attempt; required jobs bind final current inputs."""
    records, seen = [], {}
    for name in sorted(name for name in approved if name.endswith('-result.json')):
        path = b / name
        receipt = json.loads(path.read_text())
        if not all(key in receipt for key in ['job_id', 'request', 'result', 'resources']):
            continue
        ident = receipt['job_id']
        if ident in seen:
            assert seen[ident] == receipt, ('Conflicting receipt copies', str(path))
            continue
        seen[ident] = receipt
        q, rs, v = receipt['request'], receipt['result'], receipt['resources']
        assert receipt['status'] in TERMINAL, ('Nonterminal receipt', str(path))
        assert q['workspace'] == str(w) and q['exclusive'] is True and q['language'] == 'lean'
        assert rs['snapshot']['workspace_mode'] == 'exclusive_worktree'
        assert rs['snapshot']['snapshot_id'] is None
        params = q['parameters']
        source = params.get('source') or params['args'][0]
        arguments = [source] if 'source' in params else params['args']
        assert rs['actual_arguments'] == ['lean', *arguments]
        assert q['target'] == ('file' if 'source' in params else 'module')
        manifest = q['worktree_manifest']
        current_hash = sha(w / source)
        if receipt['status'] == 'succeeded':
            assert rs['exit_code'] == 0
            if q['task_type'] == 'review':
                assert rs['review']['passed'] is True
        cpu, user, system = [v.get(k) for k in ['cpu_time_seconds', 'cpu_user_seconds', 'cpu_system_seconds']]
        if None not in [cpu, user, system]:
            assert math.isclose(cpu, user + system, abs_tol=0.1)
        rss = v.get('peak_rss_bytes')
        if q['task_type'] == 'leaf':
            assert rss is not None, ('Missing physical leaf RSS', str(path))
        assert rss is None or rss <= 16 * 1024 ** 3, ('Physical RSS exceeds 16 GiB', str(path))
        records.append({'job_id': ident, 'status': receipt['status'], 'receipt': str(path.relative_to(w)),
            'receipt_sha256': sha(path), 'task_type': q['task_type'], 'source': source,
            'source_sha256': manifest['source_sha256'], 'current_source_sha256': current_hash,
            'source_matches_current': manifest['source_sha256'] == current_hash,
            'input_head': manifest['head'], 'actual_arguments': rs['actual_arguments'],
            'workspace_mode': rs['snapshot']['workspace_mode'], 'snapshot_id': None,
            'exit_code': rs['exit_code'], 'diagnostics': rs.get('diagnostics') or
                ((rs.get('stdout', '') + rs.get('stderr', '')) if receipt['status'] != 'succeeded' else None),
            **{k: v.get(k) for k in ['wall_time_seconds', 'cpu_time_seconds', 'cpu_user_seconds',
                'cpu_system_seconds', 'peak_rss_bytes', 'peak_pss_bytes']},
            'resource_source': v.get('source'), 'degraded': v.get('degraded')})
    by_id = {row['job_id']: row for row in records}
    for receipt in required:
        row = by_id[receipt['job_id']]
        assert row['status'] == 'succeeded' and row['source_matches_current']
        assert seen[row['job_id']] == receipt
    return records


def expected_evidence(approved):
    prepared = unit.preflight()
    validation, jobs = prepared['validation'], prepared['required_jobs']
    own = [SOURCE, WRAPPER, CHECKS]
    assert unit.target == TARGET and unit.PARENT_ID == TARGET_ID
    assert set(prepared['owned_sources']) == set(unit.own) == set(own)
    assert validation['passed'] is True
    assert validation['owned_source_hashes'] == {path: sha(w / path) for path in own}
    assert {row['job_id'] for row in jobs} == set(validation['compiler_checks'])
    assert set(prepared['required_evidence']) <= set(approved) | FINAL_OUTPUTS
    assert all((b / name).is_file() for name in prepared['required_evidence'])
    graph = unit.graph()
    by_name = {row['name']: row for row in graph}
    assert len(by_name) == len(graph)
    authored_modules = {path[:-5].replace('/', '.') for path in [SOURCE, WRAPPER]}
    authored = {row['name'] for row in graph if row['module'] in authored_modules and row['startLine'] > 0}
    assert len(authored) == 9
    rows = read('final-readbacks.json')['declarations']
    bound = {row['declaration']: row for row in rows}
    assert len(rows) == len(bound) == validation['readbacks'] == 9 and set(bound) == authored
    for name, row in bound.items():
        assert row['compiler_type'] == by_name[name]['elaboratedType']
        assert row['module'] == by_name[name]['module']
        assert row['source_sha256'] == sha(w / row['path'])
        assert all(isinstance(row[lang], str) and row[lang].strip() for lang in ['en', 'zh_Hans', 'ja'])
        assert all('【译名待定：' not in row[lang] for lang in ['en', 'zh_Hans', 'ja'])
    binder = read('compiler-readback-type-review.json')
    assert binder['passed'] is True
    assert binder['compiler_evidence']['graph_sha256'] == sha(b / 'decl_graph.jsonl')
    assert len(binder['declarations']) == validation['fresh_compiler_binder_reviews'] == 9
    assert {row['compiler_name'] for row in binder['declarations']} == authored
    for row in binder['declarations']:
        actual = bound[row['compiler_name']]
        assert row['passed'] is True and row['compiler_type'] == actual['compiler_type']
        assert row['current_source']['sha256'] == actual['source_sha256']
        if row.get('corrected_trilingual_statement'):
            assert all(actual[key] == row['corrected_trilingual_statement'][key] for key in ['en', 'zh_Hans', 'ja'])
    audit = {row['name']: row for row in read('all-module-axioms.json')}
    expected_constants = {row['name'] for row in graph if row['module'] in authored_modules}
    assert expected_constants <= set(audit)
    assert all(set(audit[name]['axioms']) <= STANDARD for name in expected_constants)
    assert all(set(row['axioms']) <= STANDARD for row in audit.values())
    reached, todo = set(), [TARGET]
    while todo:
        name = todo.pop()
        if name in reached:
            continue
        reached.add(name)
        if name in by_name:
            todo += by_name[name]['typeDeps'] + by_name[name]['valueDeps']
    assert authored <= reached
    inventory = read('source-consumer.json')['declarations']
    inventory_names = {row['declaration'] for row in inventory}
    assert len(inventory_names) == len(inventory) == 9 and inventory_names == authored
    review = read('independent-delivery-review.json')
    assert review['passed'] is True and review['source_ledger_passed'] is True
    assert review['all_new_outputs_have_actual_consumers'] is True
    assert review['source_ledger_sha256'] == sha(r / 'ArithmeticTeichmullerSpaces/SOURCE_LEDGER.md')
    return validation, own, jobs


def platform_graph(approved):
    result, request, submitted = [read(unit.verify_tag + suffix) for suffix in
        ['-verify-result.json', '-verify-request.json', '-verify-submit.json']]
    assert result['status'] == 'ACCEPTED' and result['id'] == submitted['submission_id']
    assert result['theorem_id'] == request['theorem_id'] == TARGET_ID
    assert request['proof_type'] == 'prove' and request['file'] == unit.sol
    assert request['source_sha256'] == sha(w / unit.sol)
    assert (b / (unit.verify_tag + '-solution.lean')).read_bytes() == (w / unit.sol).read_bytes()
    assert read(unit.verify_tag + '-verification-requested.json') == request
    raw_before, raw_after = read('root-graph-before.json'), read('root-graph-after.json')
    before = unit.summary_without_direct_proof_nodes(raw_before, set())
    after = unit.summary_without_direct_proof_nodes(raw_after, {result['id']})
    assert set(before['mathematical']) == set(after['mathematical'])
    old = {row['theorem_name']: row for row in before['mathematical'].values()}
    now = {row['theorem_name']: row for row in after['mathematical'].values()}
    assert set(old) == set(now)
    assert {name for name in old if old[name]['status'] != now[name]['status']} == {TARGET}
    for name, previous in old.items():
        assert all(now[name][key] == previous[key] for key in ['theorem_id', 'formal_statement'])
        assert not now[name].get('deprecated_at') and not now[name].get('deprecated_by')
    assert old[TARGET]['status'] == 'Open' and now[TARGET]['status'] == 'Proved'
    assert old[TARGET]['theorem_id'] == now[TARGET]['theorem_id'] == TARGET_ID
    assert read('target-id.json')['id'] == TARGET_ID
    assert all(now[name]['status'] == 'Open' for name in [LOCAL, PARENT, COMPARISON, CANONICAL, ROOT])
    assert sorted(before['reductions'], key=lambda row: row['submission_id']) == sorted(after['reductions'], key=lambda row: row['submission_id'])
    assert before['dependency_pairs'] == after['dependency_pairs']
    for summary in [before, after]:
        assert summary['counts'] == {key: BEFORE[key] for key in ['accepted_reductions', 'published_children', 'dependency_edges']}
    all_math = set(after['mathematical'])
    for sketch in [row for row in raw_after['nodes'] if row['node_type'] == 'sketch' and row['submission_id'] == result['id']]:
        assert sketch['parent_theorem_id'] == TARGET_ID and sketch['status'] == 'ACCEPTED'
        assert not {edge['source'] for edge in raw_after['edges'] if edge['kind'] == 'sketch'
            and edge['target'] == sketch['node_id'] and edge['source'] in all_math}
    # Delivery records actual GET evidence for graph-hidden and newly visible
    # old Definitions. No new Definition publication is authorized in this unit.
    retention = unit.retained_definitions(raw_before, raw_after)
    retention_files = {
        'definition-baseline-readbacks.json': retention['baseline_readbacks_sha256'],
        'definition-retention-readbacks.json': retention['retention_readbacks_sha256']}
    assert set(retention_files) <= set(approved)
    assert all(sha(b / name) == digest for name, digest in retention_files.items())
    parent = read('platform-after-parent.json')
    assert parent['theorem_id'] == TARGET_ID and parent['status'] == 'Proved'
    assert parent['formal_statement'] == read('platform-before-parent.json')['formal_statement'] == old[TARGET]['formal_statement']
    assert parent['preamble'] == read('platform-before-parent.json')['preamble']
    patch = read('parent-metadata-patch-request.json')
    assert set(patch) == {'natural_language_statement', 'source'}
    assert all(parent[key] == value for key, value in patch.items())
    assert parent['visibility'] == 'private' and parent['mathlib_rev'] == unit.ENV
    bf, af = read('root-frontier-before.json'), read('root-frontier-after.json')
    for frontier, nodes in [(bf, old), (af, now)]:
        rows = frontier['open_leaves']
        assert frontier['all_pages_fetched'] is True
        assert len(rows) == frontier['total'] == len({row['theorem_id'] for row in rows})
        assert all(nodes[row['theorem_name']]['status'] == 'Open' and
                   nodes[row['theorem_name']]['theorem_id'] == row['theorem_id'] for row in rows)
    expected = {row['theorem_name'] for row in bf['open_leaves']} - {TARGET}
    assert {row['theorem_name'] for row in af['open_leaves']} == expected
    assert bf['total'] == 18 and af['total'] == 17
    return before, after, now, result, expected, retention


def main():
    original_index = index_entries()
    original_staged = {path.decode() for path in git('diff', '--cached', '--name-only', '-z').split(b'\0') if path}
    assert not git('ls-files', '-u'), 'Resolve index conflicts before finalization'
    approved = approved_unit_files()
    validation, own, jobs = expected_evidence(approved)
    before, after, now, result, expected, retention = platform_graph(approved)
    records = ci_records(jobs, approved)
    registry_path = w / '.local/adaptation/platform-node-registry.json'
    registry = json.loads(registry_path.read_text())
    assert registry == read('registry-before.json'), 'Registry changed concurrently'
    assert registry['graph_counts'] == BEFORE
    assert sorted(registry['edges'], key=lambda row: row['submission_id']) == sorted(before['reductions'], key=lambda row: row['submission_id'])
    direct = {row['name']: row for row in registry['direct_closed_proofs']}
    assert len(direct) == len(registry['direct_closed_proofs']) == 40 and TARGET not in direct
    proof = {'name': TARGET, 'theorem_id': TARGET_ID, 'submission_id': result['id'],
        'status': 'ACCEPTED', 'mathematical_dependencies': [],
        'classification': 'Direct accepted source proof; standard Lean axioms only'}
    direct[TARGET] = proof
    assert len(direct) == 41 and all(now[name]['status'] == 'Proved' for name in direct)
    counts = after['counts'] | {'open_frontier': 17, 'direct_closed_children': len(direct)}
    assert counts == AFTER
    document = r / 'docs/Prove2Me适配状态.md'
    original, updated = [(b / name).read_text() for name in ['pending-db-before.md', 'pending-db-after.md']]
    assert document.read_text() == original, 'Pending database changed concurrently'
    prefix = '- `Heights@721496ca4c158e511d25d8ccf6bfe8503eda73c1/Heights/Different/NumberField.lean:'
    removed = [prefix + line + '`' for line in ['228', '256']]
    first, remainder = original.split('\n## 2.', 1)
    candidate = first
    for line in removed:
        assert candidate.count(line + '\n') == 1
        candidate = candidate.replace(line + '\n', '', 1)
    assert updated == candidate + '\n## 2.' + remainder
    assert '- `Heights@721496ca4c158e511d25d8ccf6bfe8503eda73c1/Heights/Different/Conductor.lean:104`' in updated
    assert '- `Genl@ea2846c877d1e16d8f0b911a5fed07f5ee69eaaf/Genl/Curves/BelyiDescent.lean:248`' in updated
    boundary = read('plan-checkbox-boundary-audit.json')
    assert sha(r / boundary['plan']) == boundary['sha256']
    assert boundary['newly_complete_broad_checkboxes'] == [] and boundary['boundary_changed'] is False
    assert boundary['Fermat_route_preserved'] is True and boundary['deprecations'] == []
    common = {'graph_counts': counts, 'target': 'Proved', 'parent': 'Open',
        'local_conductor_child': 'Open', 'comparison': 'Open',
        'canonicalEstimate': 'Open', 'root': 'Open', 'new_definitions': [], 'new_children': [],
        'new_reductions': [], 'new_dependencies': [], 'direct_closed_proof': proof,
        'Fermat_route_preserved': True, 'production_boundary_changed': False,
        'deprecations': [], 'definition_retention': retention}
    registry.update(direct_closed_proofs=sorted(direct.values(), key=lambda row: row['name']),
        graph_counts=counts, accepted_platform_reductions=36, dependency_edges=101,
        open_frontier=sorted(expected), local_open_children_below_root=17,
        published_open_children_below_root=17, mathematical_root_proved=False,
        platform_statuses={name: row['status'] for name, row in now.items()},
        recorded_at=datetime.now(timezone.utc).isoformat())
    registry['different_accounting_sourceproof_unit'] = common | {'source': str(b.relative_to(w)),
        'exact_original_target_type_preserved': True, 'submission_id': result['id']}
    source = read('source-consumer.json')
    source.update(common, status='exclusive_local_audits_passed_and_exact_direct_proof_ACCEPTED',
        platform_submission=result['id'])
    save('source-consumer.json', source)
    save('pending-db-scope.json', {'removed_only': removed, 'first_section_code_only': True,
        'all_later_sections_unchanged': True, 'target_proved': TARGET})
    save('graph-count-evidence.json', common | {'before': BEFORE, 'after': AFTER,
        'mathematical_node_ids_types_reductions_and_dependencies_unchanged': True,
        'changed_statuses_only': {TARGET: ['Open', 'Proved']}})
    rss = [row['peak_rss_bytes'] for row in records if row['peak_rss_bytes'] is not None]
    save('unit-ci-summary.json', common | {'records': records,
        'succeeded': sum(row['status'] == 'succeeded' for row in records),
        'failed_or_other_terminal': sum(row['status'] != 'succeeded' for row in records),
        'peak_rss_bytes': max(rss) if rss else None, 'missing_resource_values': 'unknown, not zero'})
    save('integration.json', common | {'input_head': read('git-input-state.json')['head'],
        'owned_sources': validation['owned_source_hashes'], 'source_ledger': 'source-consumer.json',
        'original_target_type_preserved': True,
        'status': 'Exact existing different-accounting child Proved; conductor-extension parent remains Open'})
    unit_files = sorted(set(approved) | FINAL_OUTPUTS)
    files = sorted({str((w / path).relative_to(r)) for path in own} |
        {str(document.relative_to(r)), str(registry_path.relative_to(r))} |
        {str((b / name).relative_to(r)) for name in unit_files})
    assert all(not (r / path).is_symlink() and (r / path).resolve().is_relative_to(r.resolve()) for path in files)
    registry_relative = str(registry_path.relative_to(r))
    registry['files'].pop(registry_relative, None)
    for relative in files:
        path = r / relative
        if path != registry_path:
            registry['files'][relative] = hashlib.sha256(updated.encode()).hexdigest() if path == document else sha(path)
    registry['files'] = dict(sorted(registry['files'].items()))
    registry_bytes = (json.dumps(registry, ensure_ascii=False, indent=2) + '\n').encode()
    credentials = json.loads((w / 'credentials.json').read_text())
    secrets = [value.encode() for key, value in credentials.items() if key in
        ['api_key', 'access_token', 'refresh_token', 'token'] and isinstance(value, str) and len(value) > 15]
    for relative in files:
        path = r / relative
        data = updated.encode() if path == document else registry_bytes if path == registry_path else path.read_bytes()
        assert path.name != 'credentials.json'
        assert not any(secret in data for secret in secrets) and (b'p2m_' + b'eyJ') not in data, ('Credential scan failed', relative)
        assert all(line.rstrip(b' \t') == line for line in data.splitlines()), ('Trailing whitespace', relative)
        if path.suffix in ['.lean', '.md', '.py']:
            assert not data.endswith(b'\n\n'), ('Extra terminal blank line', relative)
    document.write_text(updated)
    registry_path.write_bytes(registry_bytes)
    candidates = common | {'review_only': True, 'git_index_mutated': False,
        'unit_evidence_allowlist': 'unit-evidence-allowlist.json',
        'unit_evidence_allowlist_sha256': sha(b / 'unit-evidence-allowlist.json'),
        'owned_sources': {str((w / path).relative_to(r)): sha(w / path) for path in own},
        'unit_files': {str((b / name).relative_to(r)): sha(b / name) for name in unit_files},
        'metadata_files': {str(path.relative_to(r)): sha(path) for path in [document, registry_path]},
        'candidate_files': {relative: sha(r / relative) for relative in files},
        'root_must_review_before_staging': True}
    save('staging-candidates.json', candidates)
    subprocess.run(['git', 'diff', '--check'], cwd=r, check=True)
    assert index_entries() == original_index, 'Git index changed during finalization'
    final_staged = {path.decode() for path in git('diff', '--cached', '--name-only', '-z').split(b'\0') if path}
    assert final_staged == original_staged, 'Staged paths changed during finalization'
    assert all(sha(r / relative) == registry['files'][relative] for relative in files if r / relative != registry_path)
    print(json.dumps(common | {'audited_allowlist': len(files), 'git_index_mutated': False,
        'staging_candidates': str(b / 'staging-candidates.json'),
        'owned_sources': candidates['owned_sources'], 'metadata_files': candidates['metadata_files']}), flush=True)


if __name__ == '__main__':
    main()
