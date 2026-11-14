"""Finalize local evidence after accepted publication. Never publishes or compiles."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib
import importlib.util
import json
import math
import subprocess
import sys

b = Path('/home/admin-wsl/Coq/abc/prove2me_workspace/.local/adaptation/canonical-differential-sourceproof-20261114')
spec = importlib.util.spec_from_file_location('unit', b / 'delivery.py')
unit = importlib.util.module_from_spec(spec)
spec.loader.exec_module(unit)
r, w, read, save, sha = unit.r, unit.w, unit.read, unit.save, unit.sha
sys.path.insert(0, str(w / '.local/adaptation/northcott-sourceproof-20261114'))
from delivery_common import graph_summary

PARENT = unit.pre + 'canonicalCuspPolarLinearEquivalence'
PARENT_ID = 'd6a1ff14-5bc3-4b24-bdda-966c29d20c2c'
ROOT = 'abc.goal.lt_constant_mul_fix'
TAG = 'prove-canonicalDifferentialChange'
CHECKS = 'Solutions/Checks_FermatCanonicalDifferentialChange.lean'
TERMINAL = {'succeeded', 'failed', 'timeout', 'oom_killed', 'cancelled', 'interrupted', 'scheduler_error'}


def git(*args):
    return subprocess.check_output(['git', *args], cwd=r)


def index_entries():
    entries = {}
    for entry in git('ls-files', '--stage', '-z').split(b'\0'):
        if entry:
            metadata, path = entry.split(b'\t', 1)
            entries.setdefault(path.decode(), []).append(metadata)
    return entries


def ci_records():
    """Retain all terminal attempts, including failures with old source hashes."""
    records, seen = [], {}
    for path in sorted(b.rglob('*-result.json')):
        z = json.loads(path.read_text())
        if not all(k in z for k in ['job_id', 'request', 'result', 'resources']):
            continue
        if z['job_id'] in seen:
            assert seen[z['job_id']] == z, ('Conflicting receipt copies', path.name)
            continue
        seen[z['job_id']] = z
        q, rs, v = z['request'], z['result'], z['resources']
        assert z['status'] in TERMINAL, ('Nonterminal CI receipt', path.name, z['status'])
        assert q['workspace'] == str(w) and q['exclusive'] is True
        assert rs['snapshot']['workspace_mode'] == 'exclusive_worktree'
        assert rs['snapshot']['snapshot_id'] is None
        params = q['parameters']
        source = params.get('source') or params['args'][0]
        args = [source] if 'source' in params else params['args']
        assert rs['actual_arguments'] == ['lean', *args]
        manifest = q['worktree_manifest']
        current_hash = sha(w / source)
        if z['status'] == 'succeeded':
            assert rs['exit_code'] == 0 and manifest['source_sha256'] == current_hash
            assert 'sorryAx' not in rs.get('stdout', '') + rs.get('stderr', '')
            if q['task_type'] == 'review':
                assert rs['review']['passed'] is True
        cpu, user, system = [v.get(k) for k in ['cpu_time_seconds', 'cpu_user_seconds', 'cpu_system_seconds']]
        if None not in [cpu, user, system]:
            assert math.isclose(cpu, user + system, abs_tol=0.1)
        rss = v.get('peak_rss_bytes')
        if q['task_type'] == 'leaf':
            assert rss is not None, ('Missing leaf RSS', path.name)
        if rss is not None:
            assert rss <= 16 * 1024 ** 3, ('Physical RSS exceeds 16 GiB', path.name)
        records.append({
            'job_id': z['job_id'], 'status': z['status'], 'receipt': str(path.relative_to(w)),
            'task_type': q['task_type'], 'source': source,
            'source_sha256': manifest['source_sha256'], 'current_source_sha256': current_hash,
            'source_matches_current': manifest['source_sha256'] == current_hash,
            'input_head': manifest['head'], 'actual_arguments': rs['actual_arguments'],
            'workspace_mode': rs['snapshot']['workspace_mode'], 'snapshot_id': None,
            'exit_code': rs['exit_code'], 'diagnostics': rs.get('diagnostics'),
            **{k: v.get(k) for k in ['wall_time_seconds', 'cpu_time_seconds', 'cpu_user_seconds',
                                    'cpu_system_seconds', 'peak_rss_bytes', 'peak_pss_bytes']},
            'resource_source': v.get('source'), 'degraded': v.get('degraded')})
    assert records
    return records


def expected_evidence():
    names = [
        'delivery-validation.json', 'decl_graph.jsonl', 'syntax-boundaries.json',
        'all-module-axioms.json', 'final-readbacks.json', 'compiler-readback-type-review.json',
        'solution-type-axioms.json', 'solution-source-closure.json',
        'root-graph-before.json', 'root-graph-after.json', 'root-frontier-before.json',
        'root-frontier-after.json', 'registry-before.json', 'source-consumer.json',
        'platform-before-parent.json', 'platform-after-parent.json',
        'platform-after-canonicalCuspPolarLinearEquivalence.json',
        'parent-metadata-patch-request.json', 'pending-db-before.md', 'pending-db-after.md',
        'pending-db-scope.json', 'plan-checkbox-boundary-audit.json', 'git-input-state.json',
        'consumer-parent-leaf-result.json', 'consumer-parent-artifact-result.json', 'consumer-closed-review-result.json',
        *[TAG + suffix for suffix in ['-verify-result.json', '-verify-request.json',
                                     '-verify-submit.json', '-solution.lean']]]
    checks = [(Path(f).stem.removeprefix('Source_') + '-leaf', f) for f in unit.helpers + [unit.source]]
    checks += [(Path(f).stem.removeprefix('Source_') + '-artifact', f) for f in unit.helpers + [unit.source]]
    checks += [(tag, source) for tag, source in [
        ('closed-axioms-review', CHECKS), ('source-graph-leaf', unit.u + 'ExtractDifferentialGraph.lean'),
        ('syntax-leaf', unit.u + 'ExtractDifferentialSyntax.lean'),
        ('all-constants-review', unit.u + 'AuditAllConstants.lean'),
        ('direct-solution-leaf', unit.sol), ('solution-type-axioms-review', unit.u + 'AuditSolution.lean'),
        ('production-gates-review', unit.u + 'ProductionGates.lean')]]
    names += [tag + '-result.json' for tag, _ in checks]
    assert all((b / name).is_file() for name in names), 'Required final evidence is missing'
    for tag, source in checks:
        z = read(tag + '-result.json')
        assert z['status'] == 'succeeded' and z['request']['worktree_manifest']['source_sha256'] == sha(w / source), tag
    validation = read('delivery-validation.json')
    own = unit.helpers + [unit.source, CHECKS]
    assert len(own) == len(set(own)) == 5
    assert validation['passed'] and validation['owned_source_hashes'] == {f: sha(w / f) for f in own}
    return validation, own


def main():
    # All evidence and concurrent-work guards run before the first write.
    validation, own = expected_evidence()
    before, after = [graph_summary(read(name)) for name in ['root-graph-before.json', 'root-graph-after.json']]
    assert set(before['mathematical']) == set(after['mathematical'])
    old = {z['theorem_name']: z for z in before['mathematical'].values()}
    now = {z['theorem_name']: z for z in after['mathematical'].values()}
    assert len(old) == len(before['mathematical']) and set(old) == set(now)
    assert {n for n in old if old[n]['status'] != now[n]['status']} == {unit.target, PARENT}
    for n in [unit.target, PARENT]:
        assert old[n]['status'] == 'Open' and now[n]['status'] == 'Proved'
    assert now[PARENT]['theorem_id'] == PARENT_ID and old[ROOT]['status'] == now[ROOT]['status'] == 'Open'
    assert all(old[n]['status'] == now[n]['status'] == 'Proved' for n in unit.dependencies)
    prior = {z['submission_id']: z for z in before['reductions']}
    current = {z['submission_id']: z for z in after['reductions']}
    assert len(prior) == len(before['reductions']) and len(current) == len(after['reductions'])
    result, req, submitted = [read(TAG + suffix) for suffix in ['-verify-result.json', '-verify-request.json', '-verify-submit.json']]
    ident = read('target-id.json')['id']
    assert result['status'] == 'ACCEPTED' and result['id'] == submitted['submission_id']
    assert result['theorem_id'] == ident == now[unit.target]['theorem_id']
    assert req['theorem_id'] == ident and req['proof_type'] == 'prove' and req['file'] == unit.sol
    assert req['source_sha256'] == sha(w / unit.sol)
    assert (b / (TAG + '-solution.lean')).read_bytes() == (w / unit.sol).read_bytes()
    assert set(current) - set(prior) == {result['id']} and set(prior) <= set(current)
    edge = current[result['id']]
    assert edge == {'parent': unit.target, 'children': sorted(unit.dependencies), 'submission_id': result['id'], 'status': 'ACCEPTED'}
    promoted = []
    for sid, previous in prior.items():
        actual = current[sid]
        assert previous | {'status': actual['status']} == actual
        if previous['status'] != actual['status']:
            assert previous['status'] == 'SKETCH_ACCEPTED' and actual['status'] == 'ACCEPTED'
            assert all(now[n]['status'] == 'Proved' for n in actual['children'])
            promoted.append(sid)
    additions = {(unit.target, n) for n in unit.dependencies}
    assert before['dependency_pairs'] <= after['dependency_pairs']
    assert after['dependency_pairs'] - before['dependency_pairs'] == additions
    assert after['counts'] == {'accepted_reductions': before['counts']['accepted_reductions'] + 1,
                               'published_children': before['counts']['published_children'],
                               'dependency_edges': before['counts']['dependency_edges'] + len(additions)}
    state = read('platform-after-parent.json')
    assert state['formal_statement'] == read('platform-before-parent.json')['formal_statement']
    assert state['status'] == 'Proved' and state['visibility'] == 'private' and state['mathlib_rev'] == unit.ENV
    assert all(state[k] == v for k, v in read('parent-metadata-patch-request.json').items())
    parent = read('platform-after-canonicalCuspPolarLinearEquivalence.json')
    assert parent['theorem_id'] == PARENT_ID and parent['status'] == 'Proved'
    assert parent['formal_statement'] == read('platform-before-canonicalCuspPolarLinearEquivalence.json')['formal_statement']
    bf, af = read('root-frontier-before.json'), read('root-frontier-after.json')
    for frontier, nodes in [(bf, old), (af, now)]:
        rows = frontier['open_leaves']
        assert frontier['all_pages_fetched'] and len(rows) == frontier['total'] == len({z['theorem_id'] for z in rows})
        assert all(nodes[z['theorem_name']]['status'] == 'Open' and nodes[z['theorem_name']]['theorem_id'] == z['theorem_id'] for z in rows)
    expected = {z['theorem_name'] for z in bf['open_leaves']} - {unit.target, PARENT}
    assert {z['theorem_name'] for z in af['open_leaves']} == expected
    rp = w / '.local/adaptation/platform-node-registry.json'
    reg = json.loads(rp.read_text())
    assert reg == read('registry-before.json'), 'Registry changed concurrently'
    assert sorted(reg['edges'], key=lambda e: e['submission_id']) == sorted(before['reductions'], key=lambda e: e['submission_id'])
    direct = {z['name']: z for z in reg['direct_closed_proofs']}
    assert len(direct) == len(reg['direct_closed_proofs']) and unit.target not in direct
    proof = {'name': unit.target, 'submission_id': result['id'], 'status': 'ACCEPTED',
             'existing_proved_dependencies': unit.dependencies,
             'classification': 'Fully accepted proof with two existing proved imports; retained registry direct_closed_proofs convention'}
    direct[unit.target] = proof
    assert all(now[n]['status'] == 'Proved' for n in direct)
    counts = after['counts'] | {'open_frontier': af['total'], 'direct_closed_children': len(direct)}
    assert counts == {'accepted_reductions': 33, 'published_children': 78, 'dependency_edges': 91,
                      'open_frontier': 19, 'direct_closed_children': 36}
    document = r / 'docs/Prove2Me适配状态.md'
    original, updated = [(b / n).read_text() for n in ['pending-db-before.md', 'pending-db-after.md']]
    assert document.read_text() == original, 'Pending database changed concurrently'
    source_prefix = '- `Belyi@9ce4d3f793d3bc831f2fc7214b7dbad90ea012d8/Belyi/'
    removed = [source_prefix + p + '`\n' for p in ['CurveDeriv/Basic.lean:209', 'CurveDeriv/Basic.lean:214', 'CurveDeriv/Order.lean:83', 'CurveField/RamIdx.lean:237', 'CurveField/RamIdx.lean:257']]
    block = '\n' + ''.join(removed)
    assert original.count(block) == 1 and updated == original.replace(block, '', 1)
    assert read('pending-db-scope.json')['removed_only'] == [line.rstrip('\n') for line in removed]
    boundary = read('plan-checkbox-boundary-audit.json')
    assert sha(r / boundary['plan']) == boundary['sha256']
    assert boundary['newly_complete_broad_checkboxes'] == [] and boundary['boundary_changed'] is False
    assert boundary['Fermat_route_preserved'] is True and boundary['deprecations'] == []
    records = ci_records()
    original_index = index_entries()
    original_staged = {p.decode() for p in git('diff', '--cached', '--name-only', '-z').split(b'\0') if p}
    assert not git('ls-files', '-u'), 'Resolve pre-existing index conflicts before finalization'
    # unit.preflight rechecks all compiler/readback/closure evidence and only rewrites validation.
    unit.preflight()
    assert read('delivery-validation.json')['owned_source_hashes'] == validation['owned_source_hashes']
    reg.update(edges=sorted(after['reductions'], key=lambda e: (e['parent'], e['submission_id'])),
               direct_closed_proofs=sorted(direct.values(), key=lambda e: e['name']), graph_counts=counts,
               accepted_platform_reductions=counts['accepted_reductions'], dependency_edges=counts['dependency_edges'],
               open_frontier=sorted(expected), local_open_children_below_root=af['total'],
               published_open_children_below_root=af['total'], platform_statuses={n: z['status'] for n, z in now.items()},
               mathematical_root_proved=False, recorded_at=datetime.now(timezone.utc).isoformat())
    closure = {'name': PARENT, 'theorem_id': PARENT_ID, 'status': 'Proved', 'basis': 'Automatic closure of existing reduction; no new proof submission'}
    common = {'closed_proof': proof, 'automatically_closed_parent': closure, 'graph_counts': counts,
              'new_nodes': [], 'new_open_debt': 0, 'Fermat_route_preserved': True, 'deprecations': []}
    reg['canonical_differential_sourceproof_unit'] = common | {'source': str(b.relative_to(w)), 'actual_new_edge': edge,
        'original_type_preserved': True, 'all_proper_places_preserved': True, 'production_boundary_changed': False}
    source = read('source-consumer.json')
    for declaration in source['declarations']:
        if 'status' in declaration:
            declaration['draft_status_at_receipt'] = declaration.pop('status')
        declaration['proof_status'] = 'Exclusive local source and axiom checks passed; exact target proof ACCEPTED by Prove2Me'
    source.update(status='exclusive_local_audits_passed_and_platform_ACCEPTED', compiled=True, platform_status='Proved', **common)
    save('source-consumer.json', source)
    save('graph-count-evidence.json', common | {'before': before['counts'] | {'open_frontier': bf['total'], 'direct_closed_children': len(direct) - 1},
        'after': counts, 'mathematical_node_ids_unchanged': True, 'existing_reductions_preserved': True,
        'promoted_existing_reduction_submissions': promoted, 'added_reduction': edge,
        'added_dependency_pairs': [list(pair) for pair in sorted(additions)], 'changed_statuses': [unit.target, PARENT], 'root': 'Open'})
    rss = [z['peak_rss_bytes'] for z in records if z['peak_rss_bytes'] is not None]
    save('unit-ci-summary.json', common | {'records': records, 'succeeded': sum(z['status'] == 'succeeded' for z in records),
        'failed_or_other_terminal': sum(z['status'] != 'succeeded' for z in records),
        'peak_rss_bytes': max(rss) if rss else None, 'missing_resource_values': 'unknown, not zero', 'root': 'Open'})
    save('integration.json', common | {'input_head': read('git-input-state.json')['head'],
        'owned_sources': validation['owned_source_hashes'], 'source_ledger': 'source-consumer.json',
        'status': 'Exact original canonicalDifferentialChange Proved; existing canonical cusp parent automatically Proved',
        'original_target_type_preserved': True, 'production_boundary_changed': False, 'root': 'Open'})
    files = sorted({str((w / f).relative_to(r)) for f in own} | {str(document.relative_to(r)), str(rp.relative_to(r))} |
                   {str(p.relative_to(r)) for p in b.rglob('*') if p.is_file() and '__pycache__' not in p.parts})
    assert all(not (r / f).is_symlink() and (r / f).resolve().is_relative_to(r.resolve()) for f in files)
    assert set(own) == set(read('delivery-validation.json')['owned_source_hashes'])
    for f in files:
        p = r / f
        if p != rp:  # The registry cannot contain its own content hash.
            reg['files'][f] = hashlib.sha256(updated.encode()).hexdigest() if p == document else sha(p)
    reg['files'] = dict(sorted(reg['files'].items()))
    registry_bytes = (json.dumps(reg, ensure_ascii=False, indent=2) + '\n').encode()
    credentials = json.loads((w / 'credentials.json').read_text())
    secrets = [v.encode() for k, v in credentials.items() if k in ['api_key', 'access_token', 'refresh_token', 'token'] and isinstance(v, str) and len(v) > 15]
    for f in files:
        p = r / f
        data = updated.encode() if p == document else registry_bytes if p == rp else p.read_bytes()
        assert p.name != 'credentials.json' and not any(secret in data for secret in secrets) and (b'p2m_' + b'eyJ') not in data, ('Credential scan failed', f)
        assert all(line.rstrip(b' \t') == line for line in data.splitlines()), ('Trailing whitespace', f)
        if p.suffix in ['.lean', '.md', '.py']:
            assert not data.endswith(b'\n\n'), ('Extra terminal blank line', f)
    document.write_text(updated)
    rp.write_bytes(registry_bytes)
    subprocess.run(['git', 'diff', '--check'], cwd=r, check=True)
    subprocess.run(['git', 'add', '-f', '--', *files], cwd=r, check=True)
    subprocess.run(['git', 'diff', '--cached', '--check', '--', *files], cwd=r, check=True)
    final_index = index_entries()
    assert {p: v for p, v in original_index.items() if p not in files} == {p: v for p, v in final_index.items() if p not in files}, 'Unrelated index entries changed'
    final_staged = {p.decode() for p in git('diff', '--cached', '--name-only', '-z').split(b'\0') if p}
    assert final_staged - original_staged <= set(files), 'A file outside the allowlist was newly staged'
    assert all(sha(r / f) == reg['files'][f] for f in files if r / f != rp)
    print(json.dumps({'audited_allowlist': len(files), 'graph_counts': counts, 'target': 'Proved',
                      'automatically_closed_parent': 'Proved', 'root': 'Open', 'new_nodes': []}), flush=True)


if __name__ == '__main__':
    main()
