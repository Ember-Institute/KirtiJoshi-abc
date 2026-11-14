"""Finalize the accepted exact conductor split. Never compile or call the API.

Import performs no mutation. The main agent runs main only after publication,
terminal receipts, independent review and complete platform graph readbacks.
"""
from pathlib import Path
from datetime import datetime, timezone
import hashlib
import importlib.util
import json
import math
import subprocess
import sys

b = Path('/home/admin-wsl/Coq/abc/prove2me_workspace/.local/adaptation/belyi-different-conductor-split-20261114')
spec = importlib.util.spec_from_file_location('conductor_split_delivery', b / 'delivery.py')
unit = importlib.util.module_from_spec(spec)
spec.loader.exec_module(unit)
r, w, read, save, sha = unit.r, unit.w, unit.read, unit.save, unit.sha
sys.path.insert(0, str(w / '.local/adaptation/northcott-sourceproof-20261114'))

PRE = 'AbcAdaptation.Tripod.Fermat.Proper.'
PARENT = PRE + 'belyiDifferentConductorComparison'
PARENT_ID = '0d80f85b-de7c-4f14-999e-b712950af308'
OPEN = PRE + 'belyiActualFieldConductorExtension'
CLOSED = [PRE + 'belyiActualFieldDifferentTower', PRE + 'tripodGeneratorConductorIdentity']
CHILDREN = [OPEN, *CLOSED]
CANONICAL = 'AbcAdaptation.Tripod.Fermat.canonicalEstimate'
ROOT = 'abc.goal.lt_constant_mul_fix'
DEF = 'Definitions/Def_FermatBelyiDifferentConductorChildren.lean'
ADAPTER = 'Solutions/Source_FermatBelyiDifferentConductorAdapters.lean'
COORD = 'Solutions/Source_FermatCoordRingSource.lean'
CHECKS = ['Solutions/Checks_FermatBelyiDifferentConductorClosed.lean',
          'Solutions/Checks_FermatBelyiDifferentConductorReduction.lean']
STANDARD = {'propext', 'Classical.choice', 'Quot.sound'}
TERMINAL = {'succeeded', 'failed', 'timeout', 'oom_killed', 'cancelled', 'interrupted', 'scheduler_error'}
FINAL_OUTPUTS = {'source-consumer.json', 'pending-db-scope.json',
                 'graph-count-evidence.json', 'unit-ci-summary.json', 'integration.json'}


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


def published(tag, endpoint, expected_ids):
    payload = read(tag + '-payload.json')
    assert read(tag + '-publication-requested.json') == {'endpoint': endpoint, 'payload': payload}
    submitted = read(tag + '-submit.json')
    jobs = submitted.get('jobs') or [{'job_id': submitted['job_id']}]
    assert len(jobs) == len({row['job_id'] for row in jobs}) == len(expected_ids)
    terminal_ids = set()
    for row in jobs:
        result = read(tag + '-' + row['job_id'] + '-result.json')
        assert result['id'] == row['job_id'] and result['status'] == 'PUBLISHED'
        terminal_ids.add(result['theorem_id'])
    assert terminal_ids == set(expected_ids)


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
    # Keep the original dependent-instance rewrite failure and any later API
    # repair attempts. Do not overwrite a failed receipt with a retry result.
    repair = read('adapter-discriminant-transport-repair.json')
    failure = by_id[repair['failure_job']]
    assert failure['status'] == 'failed' and failure['source'] == ADAPTER
    assert repair['mathematical_statement_changed'] is False and repair['new_assumptions'] == []
    assert failure['peak_rss_bytes'] == repair['peak_rss_bytes']
    assert math.isclose(failure['wall_time_seconds'], repair['measured_wall_seconds'], abs_tol=0.1)
    return records


def platform_graph(contract, approved):
    direct_ids = {read(tag + '-verify-result.json')['id'] for tag in contract['direct_verify_tags'].values()}
    before = unit.summary_without_direct_proof_nodes(read('root-graph-before.json'), set())
    after = unit.summary_without_direct_proof_nodes(read('root-graph-after.json'), direct_ids)
    old = {row['theorem_name']: row for row in before['mathematical'].values()}
    now = {row['theorem_name']: row for row in after['mathematical'].values()}
    ids = read('published-child-ids.json')
    assert set(ids) == set(CHILDREN) and len(set(ids.values())) == 3
    assert len(old) == len(before['mathematical']) and len(now) == len(after['mathematical'])
    assert set(now) == set(old) | set(CHILDREN)
    assert set(after['mathematical']) == set(before['mathematical']) | set(ids.values())
    for name, previous in old.items():
        assert previous['theorem_id'] == now[name]['theorem_id']
        assert previous['status'] == now[name]['status']
        assert previous['formal_statement'] == now[name]['formal_statement']
    assert now[PARENT]['theorem_id'] == PARENT_ID == read('target-id.json')['id']
    assert all(now[name]['status'] == 'Open' for name in [OPEN, PARENT, CANONICAL, ROOT])
    assert all(now[name]['status'] == 'Proved' for name in CLOSED)
    assert all(now[name]['theorem_id'] == ids[name] for name in CHILDREN)
    published('def-' + unit.definition_name, '/submit-definition', {contract['definition_id']})
    published('different-conductor-children', '/submit-problem', set(ids.values()))
    previous = {row['submission_id']: row for row in before['reductions']}
    current = {row['submission_id']: row for row in after['reductions']}
    assert len(previous) == len(before['reductions']) and len(current) == len(after['reductions'])
    assert all(current[key] == value for key, value in previous.items())
    result, request, submitted = [read(contract['parent_verify_tag'] + suffix) for suffix in
        ['-verify-result.json', '-verify-request.json', '-verify-submit.json']]
    assert result['status'] == 'SKETCH_ACCEPTED' and result['id'] == submitted['submission_id']
    assert result['theorem_id'] == request['theorem_id'] == PARENT_ID
    assert request['proof_type'] == 'prove' and request['file'] == contract['parent_solution']
    assert request['source_sha256'] == sha(w / request['file'])
    assert (b / (contract['parent_verify_tag'] + '-solution.lean')).read_bytes() == (w / request['file']).read_bytes()
    assert set(current) - set(previous) == {result['id']}
    added = current[result['id']]
    assert added == {'parent': PARENT, 'children': sorted(CHILDREN),
                     'submission_id': result['id'], 'status': 'SKETCH_ACCEPTED'}
    assert before['dependency_pairs'] <= after['dependency_pairs']
    assert after['dependency_pairs'] - before['dependency_pairs'] == {(PARENT, name) for name in CHILDREN}
    assert before['counts'] == {'accepted_reductions': 34, 'published_children': 78, 'dependency_edges': 96}
    assert after['counts'] == {'accepted_reductions': 35, 'published_children': 81, 'dependency_edges': 99}
    raw = read('root-graph-after.json')
    sketches = [row for row in raw['nodes'] if row['node_type'] == 'sketch' and row['submission_id'] == result['id']]
    assert len(sketches) == 1 and sketches[0]['parent_theorem_id'] == PARENT_ID
    actual = {edge['source'] for edge in raw['edges'] if edge['kind'] == 'sketch'
              and edge['target'] == sketches[0]['node_id'] and edge['source'] in after['mathematical']}
    assert actual == set(ids.values()), 'The actual mathematical child set must be exact'
    definitions_before = {row['theorem_id']: row for row in read('root-graph-before.json')['nodes']
                          if row['node_type'] == 'theorem' and row['status'] == 'Definition'}
    definitions_after = {row['theorem_id']: row for row in raw['nodes']
                         if row['node_type'] == 'theorem' and row['status'] == 'Definition'}
    assert set(definitions_after) - set(definitions_before) == {contract['definition_id']}
    common_definitions = set(definitions_before) & set(definitions_after)
    for ident in common_definitions:
        previous, current_definition = definitions_before[ident], definitions_after[ident]
        assert all(current_definition[key] == previous[key] for key in
                   ['theorem_id', 'theorem_name', 'status', 'formal_statement'])
        assert current_definition['definition'].encode() == previous['definition'].encode()
    missing_definitions = set(definitions_before) - set(definitions_after)
    retention = {'graph_visible_old_definition_ids': sorted(common_definitions),
                 'graph_hidden_old_definition_ids': sorted(missing_definitions),
                 'all_old_definitions_retained': True}
    if missing_definitions:
        filename = 'definition-retention-readbacks.json'
        assert filename in approved, 'Definition retention readbacks require explicit approval in the unit allowlist'
        details = read(filename)['definitions']
        by_id = {row['theorem_id']: row for row in details}
        assert len(details) == len(by_id) and set(by_id) == missing_definitions
        for ident, detail in by_id.items():
            previous = definitions_before[ident]
            assert all(detail[key] == previous[key] for key in
                       ['theorem_id', 'theorem_name', 'status', 'formal_statement'])
            assert detail['status'] == 'Definition' and detail['visibility'] == 'private'
            assert detail['mathlib_rev'] == previous['mathlib_rev'] == unit.ENV
            codes = [detail[key] for key in ['definition', 'definitions']
                     if isinstance(detail.get(key), str) and detail[key]]
            assert codes and all(code.encode() == previous['definition'].encode() for code in codes)
            assert not detail.get('deprecated_at') and not detail.get('deprecated_by')
            assert not detail.get('deprecated', False) and not detail.get('is_deprecated', False)
        retention.update(readbacks=filename, readbacks_sha256=sha(b / filename))
    assert definitions_after[contract['definition_id']]['definition'].encode() == (w / DEF).read_bytes()
    payload = read(contract['definition_payload'])
    assert payload['definition_name'] == unit.definition_name
    assert payload['definition'].encode() == (w / DEF).read_bytes(), 'Definition payload must contain every audited byte'
    definition = read(contract['definition_readback'])
    assert definition['theorem_id'] == contract['definition_id'] and definition['status'] == 'Definition'
    # Publish-job JSON uses `definitions`; graph/detail versions use `definition`.
    codes = [definition[key] for key in ['definition', 'definitions']
             if isinstance(definition.get(key), str) and definition[key]]
    assert codes and all(code.encode() == (w / DEF).read_bytes() for code in codes)
    assert definition['visibility'] == 'private' and definition['mathlib_rev'] == unit.ENV
    assert not definition.get('deprecated_at') and not definition.get('deprecated_by')
    child_items = read(contract['children_payload'])['problems']
    assert len(child_items) == 3 and {row['theorem_name'] for row in child_items} == set(CHILDREN)
    for item in child_items:
        state = read('platform-after-' + item['theorem_name'].removeprefix(PRE) + '.json')
        assert state['theorem_id'] == ids[item['theorem_name']]
        assert all(state[key] == item[key] for key in ['formal_statement', 'preamble', 'natural_language_statement'])
        assert state['status'] == ('Open' if item['theorem_name'] == OPEN else 'Proved')
        assert state['visibility'] == 'private' and state['mathlib_rev'] == unit.ENV
        assert not state.get('deprecated_at') and not state.get('deprecated_by')
    parent = read('platform-after-parent.json')
    assert parent['theorem_id'] == PARENT_ID and parent['status'] == 'Open'
    assert parent['formal_statement'] == read('platform-before-parent.json')['formal_statement'] == old[PARENT]['formal_statement']
    assert parent['preamble'] == read('platform-before-parent.json')['preamble']
    patch = read('parent-metadata-patch-request.json')
    assert set(patch) == {'natural_language_statement', 'source'}
    assert all(parent[key] == value for key, value in patch.items())
    direct = {}
    for name in CLOSED:
        tag = contract['direct_verify_tags'][name]
        res, req, sub = [read(tag + suffix) for suffix in
            ['-verify-result.json', '-verify-request.json', '-verify-submit.json']]
        assert res['status'] == 'ACCEPTED' and res['id'] == sub['submission_id']
        assert res['theorem_id'] == req['theorem_id'] == ids[name] and req['proof_type'] == 'prove'
        assert req['source_sha256'] == sha(w / req['file'])
        assert (b / (tag + '-solution.lean')).read_bytes() == (w / req['file']).read_bytes()
        proof_nodes = [row for row in raw['nodes'] if row['node_type'] == 'sketch' and row['submission_id'] == res['id']]
        assert all(row['parent_theorem_id'] == ids[name] and row['status'] == 'ACCEPTED' for row in proof_nodes)
        direct[name] = {'name': name, 'theorem_id': ids[name], 'submission_id': res['id'],
            'status': 'ACCEPTED', 'mathematical_dependencies': [],
            'classification': 'Direct accepted source proof; standard Lean axioms only'}
    bf, af = read('root-frontier-before.json'), read('root-frontier-after.json')
    for frontier, nodes in [(bf, old), (af, now)]:
        rows = frontier['open_leaves']
        assert frontier['all_pages_fetched'] is True
        assert len(rows) == frontier['total'] == len({row['theorem_id'] for row in rows})
        assert all(nodes[row['theorem_name']]['status'] == 'Open' and
                   nodes[row['theorem_name']]['theorem_id'] == row['theorem_id'] for row in rows)
    expected = {row['theorem_name'] for row in bf['open_leaves']} - {PARENT} | {OPEN}
    assert {row['theorem_name'] for row in af['open_leaves']} == expected
    assert bf['total'] == af['total'] == 17
    return before, after, now, ids, result, added, direct, bf, af, expected, retention


def expected_evidence(approved):
    # The delivery tool is the single source of the successful final CI plan.
    # It verifies exact types, Definition equivalence, leaves/artifacts, Checks,
    # graph/parser/all constants, three solution types, production and consumer.
    prepared = unit.preflight()
    contract = {'parent_verify_tag': 'reduce-parent', 'parent_solution': unit.sol,
        'direct_verify_tags': {name: 'prove-' + name.removeprefix(PRE) for name in CLOSED},
        'definition_id': read('published-definition-id.json')['id'],
        'definition_payload': 'def-' + unit.definition_name + '-payload.json',
        'definition_readback': 'platform-after-definition.json',
        'children_payload': 'different-conductor-children-payload.json'}
    validation = prepared['validation']
    jobs = prepared['required_jobs']
    own = [DEF, ADAPTER, *[theorem_path(name) for name in CHILDREN + [PARENT]], *CHECKS]
    assert len(own) == len(set(own)) == 8 and set(prepared['owned_sources']) == set(own)
    assert validation['passed'] is True
    assert validation['owned_source_hashes'] == {path: sha(w / path) for path in own}
    assert validation['readbacks'] == 20 and validation['fresh_compiler_binder_reviews'] == 18
    assert set(row['job_id'] for row in jobs) == set(validation['compiler_checks'])
    assert all((b / name).is_file() for name in prepared['required_evidence'])
    assert set(prepared['required_evidence']) <= set(approved) | FINAL_OUTPUTS, 'Required delivery evidence is absent from the approved list'
    assert set(contract['direct_verify_tags']) == set(CLOSED)
    rows = read('final-readbacks.json')['declarations']
    assert len(rows) == len({row['declaration'] for row in rows}) == 20
    assert all(row['source_sha256'] == sha(w / row['path']) for row in rows)
    binder = read('compiler-readback-type-review.json')
    assert binder['passed'] is True and len(binder['declarations']) == 18
    graph = [json.loads(line) for line in (b / 'decl_graph.jsonl').read_text().splitlines() if line]
    by_name = {row['name']: row for row in graph}
    assert len(by_name) == len(graph)
    bound = {row['declaration']: row for row in rows}
    for name, row in bound.items():
        assert row['compiler_type'] == by_name[name]['elaboratedType']
        assert row['module'] == by_name[name]['module']
        assert all(isinstance(row[lang], str) and row[lang].strip() for lang in ['en', 'zh_Hans', 'ja'])
    for row in binder['declarations']:
        assert row['passed'] is True and row['compiler_type'] == bound[row['compiler_name']]['compiler_type']
        assert row['current_source']['sha256'] == bound[row['compiler_name']]['source_sha256']
    audited = read('all-module-axioms.json')
    for row in audited:
        allowed = STANDARD | ({'sorryAx'} if row['name'] in {OPEN, PARENT} else set())
        assert set(row['axioms']) <= allowed
        assert ('sorryAx' in row['axioms']) == (row['name'] in {OPEN, PARENT})
    ledger = read('source-consumer.json')
    authored = {row['name'] for row in graph if row['module'] in {path[:-5].replace('/', '.')
        for path in [DEF, ADAPTER] + [theorem_path(name) for name in CHILDREN + [PARENT]]}
        and row['startLine'] > 0}
    assert len(authored) == 19  # 18 fresh declarations and the reused exact parent.
    # The reused cusp helper is also an actual root/consumer input.
    assert len(ledger['declarations']) == len({row['name'] for row in ledger['declarations']}) == 19
    assert authored - {PARENT} | {unit.coord_helper} == {row['name'] for row in ledger['declarations']}
    review = read('independent-delivery-review.json')
    assert review['passed'] is True and review['source_ledger_passed'] is True
    assert review['all_new_outputs_have_actual_consumers'] is True
    assert review['source_ledger_sha256'] == sha(r / 'ArithmeticTeichmullerSpaces/SOURCE_LEDGER.md')
    baseline = {row['path']: row['sha256'] for row in read('draft-source-ledger.json')['local_inputs']}
    assert sha(w / COORD) == baseline[COORD]
    return validation, own, jobs, contract, baseline[COORD]


def main():
    original_index = index_entries()
    original_staged = {path.decode() for path in git('diff', '--cached', '--name-only', '-z').split(b'\0') if path}
    assert not git('ls-files', '-u'), 'Resolve pre-existing index conflicts before finalization'
    approved = approved_unit_files()
    validation, own, jobs, contract, coord_hash = expected_evidence(approved)
    before, after, now, ids, result, added, new_direct, bf, af, expected, retention = platform_graph(contract, approved)
    records = ci_records(jobs, approved)
    registry_path = w / '.local/adaptation/platform-node-registry.json'
    registry = json.loads(registry_path.read_text())
    assert registry == read('registry-before.json'), 'Registry changed concurrently'
    assert sorted(registry['edges'], key=lambda row: row['submission_id']) == sorted(before['reductions'], key=lambda row: row['submission_id'])
    direct = {row['name']: row for row in registry['direct_closed_proofs']}
    assert len(direct) == len(registry['direct_closed_proofs']) == 38 and not set(CLOSED) & set(direct)
    direct.update(new_direct)
    assert len(direct) == 40 and all(now[name]['status'] == 'Proved' for name in direct)
    counts = after['counts'] | {'open_frontier': af['total'], 'direct_closed_children': len(direct)}
    assert counts == {'accepted_reductions': 35, 'published_children': 81, 'dependency_edges': 99,
                      'open_frontier': 17, 'direct_closed_children': 40}
    document = r / 'docs/Prove2Me适配状态.md'
    original, updated = [(b / name).read_text() for name in ['pending-db-before.md', 'pending-db-after.md']]
    assert document.read_text() == original, 'Pending database changed concurrently'
    old_line = '- `Heights@721496ca4c158e511d25d8ccf6bfe8503eda73c1/Heights/Different/Conductor.lean:202`'
    new_line = old_line.replace(':202`', ':170`')
    first, remainder = original.split('\n## 2.', 1)
    assert first.count(old_line + '\n') == 1 and new_line not in first
    assert updated == first.replace(old_line + '\n', new_line + '\n', 1) + '\n## 2.' + remainder
    keep = '- `Genl@ea2846c877d1e16d8f0b911a5fed07f5ee69eaaf/Genl/Curves/BelyiDescent.lean:248`'
    assert keep in updated and updated.split('\n## 2.', 1)[1] == remainder
    boundary = read('plan-checkbox-boundary-audit.json')
    assert sha(r / boundary['plan']) == boundary['sha256']
    assert boundary['newly_complete_broad_checkboxes'] == [] and boundary['boundary_changed'] is False
    assert boundary['Fermat_route_preserved'] is True and boundary['deprecations'] == []
    common = {'graph_counts': counts, 'children': ids, 'open_child': OPEN, 'closed_children': CLOSED,
        'parent': 'Open', 'canonicalEstimate': 'Open', 'root': 'Open',
        'Fermat_route_preserved': True, 'production_boundary_changed': False, 'deprecations': [],
        'definition_retention': retention}
    registry.update(edges=sorted(after['reductions'], key=lambda row: (row['parent'], row['submission_id'])),
        published_nodes=sorted([{'name': row['theorem_name'], 'id': ident}
            for ident, row in after['mathematical'].items() if ident != unit.ROOT], key=lambda row: row['name']),
        direct_closed_proofs=sorted(direct.values(), key=lambda row: row['name']), graph_counts=counts,
        accepted_platform_reductions=35, dependency_edges=99, open_frontier=sorted(expected),
        local_open_children_below_root=17, published_open_children_below_root=17,
        mathematical_root_proved=False, platform_statuses={name: row['status'] for name, row in now.items()},
        recorded_at=datetime.now(timezone.utc).isoformat())
    registry['belyi_different_conductor_split_unit'] = common | {'source': str(b.relative_to(w)),
        'exact_original_parent_type_preserved': True, 'definition_id': contract['definition_id'],
        'submission_id': result['id'], 'direct_closed_proofs': list(new_direct.values()),
        'no_new_assumptions_beyond_exact_open_child': True}
    source = read('source-consumer.json')
    source.update(common, status='exclusive_local_audits_passed_exact_three_child_SKETCH_ACCEPTED',
        platform_submission=result['id'], direct_closed_proofs=list(new_direct.values()),
        current_proof_debt_scope='Only the exact actual-field conductor-extension child remains Open; the parent, canonicalEstimate and root remain Open.')
    save('source-consumer.json', source)
    save('pending-db-scope.json', {'replaced_only': {old_line: new_line}, 'first_section_code_only': True,
        'kept_parent_canonical_estimate_source': keep, 'other_sections_unchanged': True,
        'open_child': OPEN})
    save('graph-count-evidence.json', common | {'before': before['counts'] | {'open_frontier': 17, 'direct_closed_children': 38},
        'after': counts, 'new_mathematical_nodes': ids, 'new_definition_id': contract['definition_id'],
        'actual_new_reduction': added, 'new_dependency_pairs': [[PARENT, name] for name in sorted(CHILDREN)],
        'old_mathematical_nodes_statuses_types_and_reductions_preserved': True})
    rss = [row['peak_rss_bytes'] for row in records if row['peak_rss_bytes'] is not None]
    save('unit-ci-summary.json', common | {'records': records,
        'succeeded': sum(row['status'] == 'succeeded' for row in records),
        'failed_or_other_terminal': sum(row['status'] != 'succeeded' for row in records),
        'peak_rss_bytes': max(rss) if rss else None, 'missing_resource_values': 'unknown, not zero'})
    save('integration.json', common | {'input_head': read('git-input-state.json')['head'],
        'owned_sources': validation['owned_source_hashes'], 'unchanged_coord_source': {COORD: coord_hash},
        'source_ledger': 'source-consumer.json', 'original_parent_type_preserved': True,
        'status': 'Exact three-child conductor split accepted; two child proofs accepted and one exact child remains Open'})
    # The explicit root-reviewed list controls registry hashes and review
    # candidates. The finalizer never stages files or modifies the Git index.
    unit_files = sorted(set(approved) | FINAL_OUTPUTS)
    files = sorted({str((w / path).relative_to(r)) for path in own} |
        {str(document.relative_to(r)), str(registry_path.relative_to(r))} |
        {str((b / name).relative_to(r)) for name in unit_files})
    assert str((w / COORD).relative_to(r)) not in files
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
    candidates = common | {
        'review_only': True, 'git_index_mutated': False,
        'unit_evidence_allowlist': 'unit-evidence-allowlist.json',
        'unit_evidence_allowlist_sha256': sha(b / 'unit-evidence-allowlist.json'),
        'owned_sources': {str((w / path).relative_to(r)): sha(w / path) for path in own},
        'unit_files': {str((b / name).relative_to(r)): sha(b / name) for name in unit_files},
        'metadata_files': {str(path.relative_to(r)): sha(path) for path in [document, registry_path]},
        'candidate_files': {relative: sha(r / relative) for relative in files},
        'root_must_review_before_staging': True}
    # This review packet excludes its own hash and is not entered into registry
    # files. The root agent may review and stage it separately.
    save('staging-candidates.json', candidates)
    subprocess.run(['git', 'diff', '--check'], cwd=r, check=True)
    final_index = index_entries()
    assert final_index == original_index, 'Git index changed during finalization'
    final_staged = {path.decode() for path in git('diff', '--cached', '--name-only', '-z').split(b'\0') if path}
    assert final_staged == original_staged, 'Staged paths changed during finalization'
    assert all(sha(r / relative) == registry['files'][relative] for relative in files if r / relative != registry_path)
    assert sha(w / COORD) == coord_hash
    print(json.dumps(common | {'audited_allowlist': len(files), 'definition_nodes_added': 1,
        'direct_proofs_accepted': 2, 'parent_submission': result['id'], 'git_index_mutated': False,
        'staging_candidates': str(b / 'staging-candidates.json'),
        'owned_sources': candidates['owned_sources'], 'metadata_files': candidates['metadata_files']}), flush=True)


if __name__ == '__main__':
    main()
