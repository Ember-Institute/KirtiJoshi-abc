"""Finalize accepted divisor-degree-height evidence; never compile or publish.

Import performs no writes. Only the main agent may run main(), after all receipts,
independent reviews and complete platform readbacks exist.
"""
from pathlib import Path
from datetime import datetime, timezone
import hashlib
import importlib.util
import json
import math
import re
import subprocess
import sys

b = Path('/home/admin-wsl/Coq/abc/prove2me_workspace/.local/adaptation/divisor-degree-height-sourceproof-20261114')
spec = importlib.util.spec_from_file_location('divisor_height_delivery', b / 'delivery.py')
unit = importlib.util.module_from_spec(spec)
spec.loader.exec_module(unit)
r, w, read, save, sha = unit.r, unit.w, unit.read, unit.save, unit.sha
sys.path.insert(0, str(w / '.local/adaptation/northcott-sourceproof-20261114'))
from delivery_common import graph_summary

TARGET = 'AbcAdaptation.Tripod.Fermat.Proper.divisorDegreeHeightComparison'
TARGET_ID = 'b1f9a8be-a8d9-4361-b36c-32a33c9d5819'
CANONICAL = 'AbcAdaptation.Tripod.Fermat.canonicalEstimate'
ROOT = 'abc.goal.lt_constant_mul_fix'
TAG = 'prove-divisorDegreeHeightComparison'
CHECKS = 'Solutions/Checks_FermatDivisorDegreeHeightComparison.lean'
STANDARD = {'propext', 'Classical.choice', 'Quot.sound'}
TERMINAL = {'succeeded', 'failed', 'timeout', 'oom_killed', 'cancelled', 'interrupted', 'scheduler_error'}
KNOWN_IDS = {
    'riemannRochFiniteDimensional': 'a6fcc25b-32d0-4414-97aa-f0e02d9ab853',
    'riemannRochDimensionUpperBound': '90a6f1ba-385c-4416-91f1-b6e764774c0d',
    'riemannRochEventuallyLinear': 'ad423628-d8a1-4e5e-8a80-0950952bedaf',
    'polarPresentationExists': 'a08420b7-ec58-483b-a8b9-69cbbedc4767',
    'functionZeroPoleDegrees': '316012c3-e7da-48f6-bb43-16975306ad8d',
    'riemannBasisPowerLowerBound': '21a196a2-8bae-42ed-b899-dbad329e4529',
    'riemannPolarApproximation': '2d0f447c-1931-48a0-b068-3031623bbd3a',
}


def git(*args):
    return subprocess.check_output(['git', *args], cwd=r)


def index_entries():
    entries = {}
    for entry in git('ls-files', '--stage', '-z').split(b'\0'):
        if entry:
            metadata, path = entry.split(b'\t', 1)
            entries.setdefault(path.decode(), []).append(metadata)
    return entries


def input_hashes(receipt, paths):
    recorded = receipt['request']['worktree_manifest']['input_hashes']
    assert all(recorded[path] == sha(w / path) for path in paths)


def ci_records():
    """Retain every terminal attempt, including both original zsmul failures."""
    records, seen = [], {}
    paths = sorted(b.rglob('*-result.json'))
    paths += [unit.prior / (Path(path).stem.removeprefix('Source_') + suffix + '-result.json')
              for path in unit.old_helpers for suffix in ['-leaf', '-artifact']]
    for path in paths:
        z = json.loads(path.read_text())
        if not all(key in z for key in ['job_id', 'request', 'result', 'resources']):
            continue
        if z['job_id'] in seen:
            assert seen[z['job_id']] == z, ('Conflicting receipt copies', path.name)
            continue
        seen[z['job_id']] = z
        q, rs, resources = z['request'], z['result'], z['resources']
        assert z['status'] in TERMINAL, ('Nonterminal CI receipt', path.name, z['status'])
        assert q['workspace'] == str(w) and q['exclusive'] is True
        assert q['language'] == 'lean'
        assert rs['snapshot']['workspace_mode'] == 'exclusive_worktree'
        assert rs['snapshot']['snapshot_id'] is None
        params = q['parameters']
        source = params.get('source') or params['args'][0]
        arguments = [source] if 'source' in params else params['args']
        assert rs['actual_arguments'] == ['lean', *arguments]
        assert q['target'] == ('file' if 'source' in params else 'module')
        manifest = q['worktree_manifest']
        current_hash = sha(w / source)
        if z['status'] == 'succeeded':
            assert rs['exit_code'] == 0
            # Historical successful attempts may predate a recorded source
            # repair. expected_evidence binds every required final job to the
            # current source; this inventory retains the older input honestly.
            if path.parent == unit.prior:
                assert manifest['source_sha256'] == current_hash
            assert 'sorryAx' not in rs.get('stdout', '') + rs.get('stderr', '')
            if q['task_type'] == 'review':
                assert rs['review']['passed'] is True
        cpu, user, system = [resources.get(key) for key in
                             ['cpu_time_seconds', 'cpu_user_seconds', 'cpu_system_seconds']]
        if None not in [cpu, user, system]:
            assert math.isclose(cpu, user + system, abs_tol=0.1)
        rss = resources.get('peak_rss_bytes')
        if q['task_type'] == 'leaf':
            assert rss is not None, ('Missing physical leaf RSS', path.name)
        assert rss is None or rss <= 16 * 1024 ** 3, ('Physical RSS exceeds 16 GiB', path.name)
        records.append({
            'job_id': z['job_id'], 'status': z['status'], 'receipt': str(path.relative_to(w)),
            'receipt_sha256': sha(path), 'reused_unchanged_old_helper': path.parent == unit.prior,
            'task_type': q['task_type'], 'source': source,
            'source_sha256': manifest['source_sha256'], 'current_source_sha256': current_hash,
            'source_matches_current': manifest['source_sha256'] == current_hash,
            'input_head': manifest['head'], 'actual_arguments': rs['actual_arguments'],
            'workspace_mode': rs['snapshot']['workspace_mode'], 'snapshot_id': None,
            'exit_code': rs['exit_code'],
            'diagnostics': rs.get('diagnostics') or ((rs.get('stdout', '') + rs.get('stderr', ''))
                                                   if z['status'] != 'succeeded' else None),
            **{key: resources.get(key) for key in ['wall_time_seconds', 'cpu_time_seconds',
                'cpu_user_seconds', 'cpu_system_seconds', 'peak_rss_bytes', 'peak_pss_bytes']},
            'resource_source': resources.get('source'), 'degraded': resources.get('degraded')})
    assert records
    by_id = {row['job_id']: row for row in records}
    for repair_name in ['zsmul-api-repair.json', 'zsmul-definitional-repair.json']:
        repair = read(repair_name)
        original = by_id[repair['failure_job']]
        assert original['status'] == 'failed' and repair['signature_changed'] is False
        assert original['source'] == 'Solutions/Source_FermatPositiveDegreePolar.lean'
        assert original['peak_rss_bytes'] == repair['peak_rss_bytes']
        assert math.isclose(original['wall_time_seconds'], repair['measured_wall_seconds'], abs_tol=0.1)
    return records


def expected_evidence():
    names = [
        'delivery-validation.json', 'decl_graph.jsonl', 'syntax-boundaries.json',
        'all-module-axioms.json', 'final-readbacks.json', 'compiler-readback-type-review.json',
        'reused-compiler-readback-type-review.json', 'solution-type-axioms.json',
        'solution-source-closure.json', 'root-graph-before.json', 'root-graph-after.json',
        'root-frontier-before.json', 'root-frontier-after.json', 'registry-before.json',
        'source-consumer.json', 'consumer-config.json', 'platform-before-parent.json',
        'platform-after-parent.json', 'platform-after-root.json', 'parent-metadata-patch-request.json',
        'pending-db-before.md', 'pending-db-after.md', 'pending-db-scope.json',
        'plan-checkbox-boundary-audit.json', 'git-input-state.json', 'independent-delivery-review.json',
        'imported-platform-theorems.json', 'platform-imports-revalidated.json',
        'actual-platform-reduction.json', 'zsmul-api-repair.json', 'zsmul-definitional-repair.json',
        *['platform-existing-' + short + '.json' for short in KNOWN_IDS],
        *[TAG + suffix for suffix in ['-verify-result.json', '-verify-request.json',
                                     '-verify-submit.json', '-solution.lean']]]
    assert all((b / name).is_file() for name in names), 'Required final evidence is missing'
    assert unit.target == TARGET and unit.checks == CHECKS
    assert len(unit.old_helpers) == 8 and len(unit.new_helpers) == 4
    assert unit.helpers == unit.old_helpers + unit.new_helpers
    own = unit.new_helpers + [unit.source, CHECKS]
    assert len(own) == len(set(own)) == 6
    validation = read('delivery-validation.json')
    assert validation['passed'] is True
    assert validation['owned_source_hashes'] == {path: sha(w / path) for path in own}
    assert validation['reused_source_hashes'] == {path: sha(w / path) for path in unit.old_helpers}
    assert validation['original_platform_type_equal'] is True
    assert validation['new_platform_nodes'] == [] and validation['new_open_debt'] == 0
    assert validation['readbacks'] == 145
    assert validation['reused_exact_source_type_binder_audits'] == 121
    assert validation['fresh_binder_audits'] == 23
    jobs = []
    for path in unit.new_helpers + [unit.source]:
        tag = Path(path).stem.removeprefix('Source_')
        jobs += [unit.checked(tag + '-leaf', path), unit.checked(tag + '-artifact', path, artifact=True)]
    config = read('consumer-config.json')
    assert config['ci_tag'] == 'consumer-review' and config['review'] is True
    assert config['parent_still_open_expected'] is True
    assert config['actual_consumer'] == unit.pre + 'canonicalEstimate_of_belyi_children'
    assert config['source_path'] == 'Definitions/Def_FermatCanonicalBelyiComposition.lean'
    assert config['source_sha256'] == sha(w / config['source_path'])
    checks = [
        ('closed-axioms-review', CHECKS, True),
        ('source-graph-leaf', unit.u + 'ExtractDegreeHeightGraph.lean', False),
        ('syntax-leaf', unit.u + 'ExtractDegreeHeightSyntax.lean', False),
        ('all-constants-review', unit.u + 'AuditAllConstants.lean', True),
        ('direct-solution-leaf', unit.sol, False),
        ('solution-type-axioms-review', unit.u + 'AuditSolution.lean', True),
        ('production-gates-review', unit.u + 'ProductionGates.lean', True),
        (config['ci_tag'], config['source'], True)]
    for tag, source, review in checks:
        jobs.append(unit.checked(tag, source, review=review))
    assert validation['consumer_source_sha256'] == sha(w / config['source'])
    assert config['parent_id'] == '7037c68a-1315-46ef-91df-2fae1b9d7b0b'
    assert config['parent_name'] == CANONICAL
    consumer_code = (w / config['source']).read_text()
    assert 'canonicalEstimate_of_belyi_children' in consumer_code
    assert 'hDegree hCanonical hHeight divisorDegreeHeightComparison hDifferent hConductor' in consumer_code
    gate_code = (b / 'ProductionGates.lean').read_text()
    assert {line[7:] for line in gate_code.splitlines() if line.startswith('import ')} == {
        'ArithmeticTeichmullerSpaces.Prologue.Audit.ImportAudit',
        'ArithmeticTeichmullerSpaces.Act1Scene1',
        'ArithmeticTeichmullerSpaces.Prologue.Audit.AxiomAudit'}
    input_hashes(jobs[-1], [config['source_path'], unit.source])
    for tag in ['source-graph-leaf', 'syntax-leaf', 'all-constants-review']:
        input_hashes(read(tag + '-result.json'), unit.helpers + [unit.source])
    input_hashes(read('production-gates-review-result.json'), unit.helpers + [unit.source, CHECKS])
    assert {row['job_id'] for row in jobs} <= set(validation['compiler_checks'])
    compiled_bindings(validation)
    return validation, own


def compiled_bindings(validation):
    graph = unit.graph()
    by_name = {row['name']: row for row in graph}
    assert len(by_name) == len(graph)
    rows = read('final-readbacks.json')['declarations']
    bound = {row['declaration']: row for row in rows}
    assert len(rows) == len(bound) == 145 and TARGET in bound
    for name, row in bound.items():
        compiler = by_name[name]
        assert row['compiler_type'] == compiler['elaboratedType']
        assert row['source_sha256'] == sha(w / row['path'])
        assert compiler['module'] == unit.module(row['path'])
        assert row['compiler_parser_span'] == unit.syntax(row['path'], row['userName'])
        assert all(isinstance(row[lang], str) and row[lang].strip() for lang in ['en', 'zh_Hans', 'ja'])
    old_bound = {name: row for name, row in bound.items() if row['path'] in unit.old_helpers}
    new_bound = {name: row for name, row in bound.items() if row['path'] in unit.new_helpers}
    assert len(old_bound) == 121 and len(new_bound) == 23
    assert set(bound) == set(old_bound) | set(new_bound) | {TARGET}
    reused = read('reused-compiler-readback-type-review.json')
    assert reused['passed'] is True and reused['current_graph_sha256'] == sha(b / 'decl_graph.jsonl')
    assert reused['source_audit_sha256'] == sha(unit.prior / 'compiler-readback-type-review.json')
    assert reused['original_packet_sha256'] == sha(unit.prior / 'final-readbacks.json')
    assert len(reused['declarations']) == 121
    assert {row['compiler_name'] for row in reused['declarations']} == set(old_bound)
    binder = read('compiler-readback-type-review.json')
    assert binder['passed'] is True and binder['compiler_evidence']['graph_sha256'] == sha(b / 'decl_graph.jsonl')
    assert {row['path']: row['sha256'] for row in binder['original_packets']} == {
        'blind-readbacks-source.json': sha(b / 'blind-readbacks-source.json')}
    assert len(binder['declarations']) == 23
    assert {row['compiler_name'] for row in binder['declarations']} == set(new_bound)
    for row in reused['declarations'] + binder['declarations']:
        actual = bound[row['compiler_name']]
        assert row['passed'] is True and row['compiler_type'] == actual['compiler_type']
        assert row['current_source']['sha256'] == actual['source_sha256']
        correction = row.get('corrected_trilingual_statement')
        if correction:
            assert all(actual[lang] == correction[lang] for lang in ['en', 'zh_Hans', 'ja'])
    old_audit = json.loads((unit.prior / 'compiler-readback-type-review.json').read_text())
    prior_audits = {row['compiler_name']: row for row in old_audit['declarations']}
    for row in reused['declarations']:
        previous = prior_audits[row['reused_compiler_name']]
        assert previous['passed'] is True and previous['compiler_type'] == row['compiler_type']
        assert previous['current_source']['sha256'] == row['current_source']['sha256']
    for path in unit.helpers + [unit.source]:
        parsed = [row for row in read('syntax-boundaries.json') if row['file'] == path]
        covered = [row for row in rows if row['path'] == path]
        assert len(parsed) == len(covered), ('Incomplete declaration readback', path)
        assert {row['nameText'] for row in parsed} == {row['userName'].split('.')[-1] for row in covered}
    axioms = read('all-module-axioms.json')
    audited = {row['name']: row for row in axioms}
    owned_modules = {unit.module(path) for path in unit.helpers + [unit.source]}
    assert {row['name'] for row in graph if row['module'] in owned_modules} <= set(audited)
    assert all(set(row['axioms']) <= STANDARD for row in axioms)
    audit = read('solution-type-axioms.json')
    assert audit['original_type_equal'] is True and set(audit['axioms']) == STANDARD
    solution_hash = sha(w / unit.sol)
    review = read('independent-delivery-review.json')
    assert review['passed'] is True and review['solution_sha256'] == solution_hash
    assert review['source_ledger_passed'] is True and review['all_new_outputs_have_actual_consumers'] is True
    assert review['source_ledger_sha256'] == sha(r / 'ArithmeticTeichmullerSpaces/SOURCE_LEDGER.md')
    assert validation['independent_delivery_review_sha256'] == sha(b / 'independent-delivery-review.json')
    close = read('solution-source-closure.json')
    assert close['source'] == unit.sol and close['source_sha256'] == solution_hash
    assert close['graph_sha256'] == sha(b / 'decl_graph.jsonl')
    assert close['parser_sha256'] == sha(b / 'syntax-boundaries.json')
    assert close['source_hashes'] == {path: sha(w / path) for path in unit.helpers + [unit.source]}
    code = (w / unit.sol).read_text()
    actual_imports = [name for line in code.splitlines() if line.startswith('import ') for name in line[7:].split()]
    assert actual_imports and all(name.startswith(('Definitions.', 'Mathlib.', 'Theorems.')) for name in actual_imports)
    assert unit.module(unit.source) not in actual_imports
    assert close['imports'] == ['import ' + name for name in actual_imports]
    assert close['platform_theorem_imports'] == ['import ' + name for name in actual_imports if name.startswith('Theorems.')]
    direct_theorems = {'riemannRochFiniteDimensional', 'riemannRochDimensionUpperBound',
                       'riemannRochEventuallyLinear', 'polarPresentationExists', 'functionZeroPoleDegrees'}
    required_imports = {'Theorems.Thm_' + (unit.pre + short).replace('.', '_') for short in direct_theorems}
    assert required_imports <= set(actual_imports)
    assert not re.search(r'\b(sorry|admit|axiom|unsafe)\b', code)
    assert close['new_nodes'] == [] and close['new_open_debt'] == 0
    source = read('source-consumer.json')
    declarations = source['declarations']
    assert len(declarations) == len({row['name'] for row in declarations})
    # The root agent populates this ledger from the current compiler graph. Its
    # names may be private compiler names; every authored helper must be present.
    assert {row['name'] for row in graph if row['module'] in {unit.module(p) for p in unit.helpers}
            and row['startLine'] > 0} == {row['name'] for row in declarations}


def platform_graph():
    before, after = [graph_summary(read(name)) for name in ['root-graph-before.json', 'root-graph-after.json']]
    assert set(before['mathematical']) == set(after['mathematical']), 'Mathematical node IDs changed'
    old = {row['theorem_name']: row for row in before['mathematical'].values()}
    now = {row['theorem_name']: row for row in after['mathematical'].values()}
    assert len(old) == len(before['mathematical']) and set(old) == set(now)
    assert {name for name in old if old[name]['status'] != now[name]['status']} == {TARGET}
    assert old[TARGET]['status'] == 'Open' and now[TARGET]['status'] == 'Proved'
    assert old[TARGET]['theorem_id'] == now[TARGET]['theorem_id'] == TARGET_ID
    assert all(old[name]['theorem_id'] == now[name]['theorem_id'] and
               old[name]['formal_statement'] == now[name]['formal_statement'] for name in old)
    assert old[ROOT]['status'] == now[ROOT]['status'] == 'Open'
    assert old[CANONICAL]['status'] == now[CANONICAL]['status'] == 'Open'
    known = {}
    for short, ident in KNOWN_IDS.items():
        name = unit.pre + short
        payload = read('platform-existing-' + short + '.json')
        assert payload['theorem_id'] == ident and payload['theorem_name'] == name
        assert payload['status'] == old[name]['status'] == now[name]['status'] == 'Proved'
        assert old[name]['theorem_id'] == now[name]['theorem_id'] == ident
        assert payload['formal_statement'] == old[name]['formal_statement'] == now[name]['formal_statement']
        assert payload['visibility'] == 'private' and payload['mathlib_rev'] == unit.ENV
        assert payload.get('deprecated_at') is None and payload.get('deprecated_by') is None
        known[ident] = {'id': ident, 'name': name, 'status': 'Proved'}
    imports = read('imported-platform-theorems.json')['theorems']
    assert imports == unit.imported_platform_theorems()
    assert len(imports) == len({row['id'] for row in imports})
    assert all(row['id'] in known and row['name'] == known[row['id']]['name'] for row in imports)
    revalidated = read('platform-imports-revalidated.json')
    assert revalidated['passed'] is True
    assert len(revalidated['theorems']) == len(imports)
    assert {row['id'] for row in revalidated['theorems']} == {row['id'] for row in imports}
    for row in revalidated['theorems']:
        assert row['id'] in known and row['name'] == known[row['id']]['name']
        assert row['status'] == 'Proved' and row['visibility'] == 'private' and row['mathlib_rev'] == unit.ENV
    result, request, submitted = [read(TAG + suffix) for suffix in
                                 ['-verify-result.json', '-verify-request.json', '-verify-submit.json']]
    assert read('target-id.json')['id'] == TARGET_ID
    assert result['status'] == 'ACCEPTED' and result['id'] == submitted['submission_id']
    assert result['theorem_id'] == request['theorem_id'] == TARGET_ID
    assert request['proof_type'] == 'prove' and request['file'] == unit.sol
    assert request['source_sha256'] == sha(w / unit.sol)
    assert (b / (TAG + '-solution.lean')).read_bytes() == (w / unit.sol).read_bytes()
    prior = {row['submission_id']: row for row in before['reductions']}
    current = {row['submission_id']: row for row in after['reductions']}
    assert len(prior) == len(before['reductions']) and len(current) == len(after['reductions'])
    assert set(current) - set(prior) == {result['id']} and set(prior) <= set(current)
    actual = read('actual-platform-reduction.json')
    assert actual['submission_id'] == result['id'] and actual['status'] == 'ACCEPTED'
    raw_after = read('root-graph-after.json')
    sketch = [row for row in raw_after['nodes'] if row['node_type'] == 'sketch' and row['submission_id'] == result['id']]
    assert len(sketch) == 1 and sketch[0]['node_id'] == actual['reduction_id']
    assert sketch[0]['parent_theorem_id'] == TARGET_ID and sketch[0]['status'] == 'ACCEPTED'
    mathematical_ids = set(after['mathematical'])
    child_ids = {edge['source'] for edge in raw_after['edges']
                 if edge['target'] == actual['reduction_id'] and edge['kind'] == 'sketch' and edge['source'] in mathematical_ids}
    assert child_ids and child_ids <= set(known), 'Unexpected or unproved mathematical dependency'
    children = actual['children']
    assert len(children) == len({row['id'] for row in children})
    assert set(child_ids) == {row['id'] for row in children}
    assert all(row == known[row['id']] for row in children)
    dependencies = sorted(known[ident]['name'] for ident in child_ids)
    assert current[result['id']] == {'parent': TARGET, 'children': dependencies,
                                     'submission_id': result['id'], 'status': 'ACCEPTED'}
    promoted = []
    for ident, previous in prior.items():
        actual_previous = current[ident]
        assert previous | {'status': actual_previous['status']} == actual_previous
        if previous['status'] != actual_previous['status']:
            assert previous['status'] == 'SKETCH_ACCEPTED' and actual_previous['status'] == 'ACCEPTED'
            assert all(now[name]['status'] == 'Proved' for name in actual_previous['children'])
            promoted.append(ident)
    added_pairs = {(TARGET, name) for name in dependencies}
    assert after['dependency_pairs'] - before['dependency_pairs'] == added_pairs
    assert not before['dependency_pairs'] - after['dependency_pairs']
    assert before['counts'] == {'accepted_reductions': 33, 'published_children': 78, 'dependency_edges': 91}
    assert after['counts'] == {'accepted_reductions': 34, 'published_children': 78,
                               'dependency_edges': 91 + len(dependencies)}
    state = read('platform-after-parent.json')
    assert state['theorem_id'] == TARGET_ID and state['theorem_name'] == TARGET
    assert state['formal_statement'] == read('platform-before-parent.json')['formal_statement'] == old[TARGET]['formal_statement']
    assert state['status'] == 'Proved' and state['visibility'] == 'private' and state['mathlib_rev'] == unit.ENV
    patch = read('parent-metadata-patch-request.json')
    assert set(patch) == {'natural_language_statement', 'source'}
    assert all(state[key] == value for key, value in patch.items())
    root = read('platform-after-root.json')
    assert root['theorem_id'] == unit.ROOT and root['theorem_name'] == ROOT and root['status'] == 'Open'
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
    return before, after, now, result, current[result['id']], children, promoted, bf, af, expected


def main():
    validation, own = expected_evidence()
    before, after, now, result, added, children, promoted, bf, af, expected = platform_graph()
    records = ci_records()
    registry_path = w / '.local/adaptation/platform-node-registry.json'
    registry = json.loads(registry_path.read_text())
    assert registry == read('registry-before.json'), 'Registry changed concurrently'
    assert sorted(registry['edges'], key=lambda edge: edge['submission_id']) == sorted(before['reductions'], key=lambda edge: edge['submission_id'])
    direct = {row['name']: row for row in registry['direct_closed_proofs']}
    assert len(direct) == len(registry['direct_closed_proofs']) == 37 and TARGET not in direct
    proof = {'name': TARGET, 'submission_id': result['id'], 'status': 'ACCEPTED',
             'existing_proved_dependencies': sorted(row['name'] for row in children),
             'existing_proved_dependency_ids': {row['name']: row['id'] for row in children},
             'classification': 'Direct accepted source proof; existing private Proved theorem dependencies recorded by actual API graph'}
    direct[TARGET] = proof
    assert all(now[name]['status'] == 'Proved' for name in direct)
    counts = after['counts'] | {'open_frontier': af['total'], 'direct_closed_children': len(direct)}
    assert counts == {'accepted_reductions': 34, 'published_children': 78,
                      'dependency_edges': 91 + len(children), 'open_frontier': 17,
                      'direct_closed_children': 38}
    document = r / 'docs/Prove2Me适配状态.md'
    original, updated = [(b / name).read_text() for name in ['pending-db-before.md', 'pending-db-after.md']]
    assert document.read_text() == original, 'Pending database changed concurrently'
    prefix = '- `Heights@721496ca4c158e511d25d8ccf6bfe8503eda73c1/Heights/Curve/DivisorHeight.lean:'
    removed = [prefix + line + '`\n' for line in ['112', '263']]
    candidate = original
    for line in removed:
        assert candidate.count(line) == 1
        candidate = candidate.replace(line, '', 1)
    assert updated == candidate, 'Only the two exact pending rows may be deleted; blank lines must be preserved'
    assert read('pending-db-scope.json')['removed_only'] == [line.rstrip('\n') for line in removed]
    boundary = read('plan-checkbox-boundary-audit.json')
    assert sha(r / boundary['plan']) == boundary['sha256']
    assert boundary['newly_complete_broad_checkboxes'] == [] and boundary['boundary_changed'] is False
    assert boundary['Fermat_route_preserved'] is True and boundary['deprecations'] == []
    unchanged_old = {path: sha(w / path) for path in unit.old_helpers}
    baseline_old = {str(Path(row['path']).relative_to(w)): row['sha256']
                    for row in read('draft-source-ledger.json')['existing_local_inputs']
                    if str(row['path']).startswith(str(w) + '/') and str(Path(row['path']).relative_to(w)) in unit.old_helpers}
    assert unchanged_old == baseline_old
    original_index = index_entries()
    original_staged = {path.decode() for path in git('diff', '--cached', '--name-only', '-z').split(b'\0') if path}
    assert not git('ls-files', '-u'), 'Resolve pre-existing index conflicts before finalization'
    # The delivery preflight writes only current validation and imported-theorem
    # evidence. All guards above run before these writes. No compile/API call.
    unit.preflight()
    assert read('delivery-validation.json')['owned_source_hashes'] == validation['owned_source_hashes']
    assert unchanged_old == {path: sha(w / path) for path in unit.old_helpers}
    registry.update(
        edges=sorted(after['reductions'], key=lambda edge: (edge['parent'], edge['submission_id'])),
        direct_closed_proofs=sorted(direct.values(), key=lambda row: row['name']), graph_counts=counts,
        accepted_platform_reductions=counts['accepted_reductions'], dependency_edges=counts['dependency_edges'],
        open_frontier=sorted(expected), local_open_children_below_root=af['total'],
        published_open_children_below_root=af['total'], platform_statuses={name: row['status'] for name, row in now.items()},
        mathematical_root_proved=False, recorded_at=datetime.now(timezone.utc).isoformat())
    common = {'closed_proof': proof, 'graph_counts': counts, 'new_nodes': [], 'new_open_debt': 0,
              'new_reductions': [added], 'new_dependencies': children,
              'Fermat_route_preserved': True, 'deprecations': [], 'automatically_closed_parents': []}
    registry['divisor_degree_height_sourceproof_unit'] = common | {
        'source': str(b.relative_to(w)), 'original_type_preserved': True,
        'arbitrary_supplied_presentations_and_real_scalar_preserved': True,
        'production_boundary_changed': False, 'canonicalEstimate': 'Open'}
    source = read('source-consumer.json')
    for declaration in source['declarations']:
        if 'status' in declaration:
            declaration['draft_status_at_receipt'] = declaration.pop('status')
        declaration['proof_status'] = 'Local source module and exhaustive axiom audit passed; exact target ACCEPTED. Helper is not a separate platform theorem node.'
        declaration['platform_solution_inlined'] = declaration['needed_by_target_or_instance_roots']
    source.update(status='exclusive_local_audits_passed_and_platform_ACCEPTED', compiled=True,
                  platform_status='Proved', canonicalEstimate='Open', **common)
    save('source-consumer.json', source)
    save('graph-count-evidence.json', common | {
        'before': before['counts'] | {'open_frontier': bf['total'], 'direct_closed_children': 37},
        'after': counts, 'mathematical_node_ids_unchanged': True,
        'existing_reductions_preserved': True, 'promoted_existing_reduction_submissions': promoted,
        'added_reductions': [added], 'added_dependency_pairs': [[TARGET, row['name']] for row in children],
        'changed_statuses': [TARGET], 'root': 'Open', 'canonicalEstimate': 'Open'})
    rss = [row['peak_rss_bytes'] for row in records if row['peak_rss_bytes'] is not None]
    save('unit-ci-summary.json', common | {'records': records,
        'succeeded': sum(row['status'] == 'succeeded' for row in records),
        'failed_or_other_terminal': sum(row['status'] != 'succeeded' for row in records),
        'peak_rss_bytes': max(rss) if rss else None, 'missing_resource_values': 'unknown, not zero',
        'root': 'Open', 'canonicalEstimate': 'Open'})
    save('integration.json', common | {'input_head': read('git-input-state.json')['head'],
        'owned_sources': validation['owned_source_hashes'], 'unchanged_old_helpers': unchanged_old,
        'source_ledger': 'source-consumer.json',
        'status': 'Exact original divisorDegreeHeightComparison Proved; canonicalEstimate and root remain Open',
        'original_target_type_preserved': True, 'production_boundary_changed': False,
        'root': 'Open', 'canonicalEstimate': 'Open'})
    # Explicit individual paths only: six owned sources, this unit's regular
    # files, the registry and the exact pending database. No directory git add.
    files = sorted({str((w / path).relative_to(r)) for path in own} |
                   {str(document.relative_to(r)), str(registry_path.relative_to(r))} |
                   {str(path.relative_to(r)) for path in b.rglob('*')
                    if path.is_file() and '__pycache__' not in path.parts and path.suffix != '.pyc'})
    assert not ({str((w / path).relative_to(r)) for path in unit.old_helpers} & set(files))
    assert all(not (r / path).is_symlink() and (r / path).resolve().is_relative_to(r.resolve()) for path in files)
    assert set(own) == set(read('delivery-validation.json')['owned_source_hashes'])
    registry_relative = str(registry_path.relative_to(r))
    registry['files'].pop(registry_relative, None)
    for relative in files:
        path = r / relative
        if path != registry_path:
            registry['files'][relative] = hashlib.sha256(updated.encode()).hexdigest() if path == document else sha(path)
    registry['files'] = dict(sorted(registry['files'].items()))
    registry_bytes = (json.dumps(registry, ensure_ascii=False, indent=2) + '\n').encode()
    credentials = json.loads((w / 'credentials.json').read_text())
    secrets = [value.encode() for key, value in credentials.items()
               if key in ['api_key', 'access_token', 'refresh_token', 'token'] and isinstance(value, str) and len(value) > 15]
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
    subprocess.run(['git', 'diff', '--check'], cwd=r, check=True)
    subprocess.run(['git', 'add', '-f', '--', *files], cwd=r, check=True)
    subprocess.run(['git', 'diff', '--cached', '--check', '--', *files], cwd=r, check=True)
    final_index = index_entries()
    assert {path: value for path, value in original_index.items() if path not in files} == {
        path: value for path, value in final_index.items() if path not in files}, 'Unrelated index entries changed'
    final_staged = {path.decode() for path in git('diff', '--cached', '--name-only', '-z').split(b'\0') if path}
    assert final_staged - original_staged <= set(files), 'A file outside the allowlist was newly staged'
    assert all(sha(r / relative) == registry['files'][relative] for relative in files if r / relative != registry_path)
    assert unchanged_old == {path: sha(w / path) for path in unit.old_helpers}
    print(json.dumps({'audited_allowlist': len(files), 'graph_counts': counts, 'target': 'Proved',
                      'root': 'Open', 'canonicalEstimate': 'Open', 'new_nodes': [],
                      'actual_proved_dependencies': children, 'automatically_closed_parents': []}), flush=True)


if __name__ == '__main__':
    main()
