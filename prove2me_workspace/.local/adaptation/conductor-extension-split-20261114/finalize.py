"""Finalize the exact conductor-extension split; no CI, API or Git mutations.

Only the main agent executes main after terminal receipts and platform readbacks.
Import does not write. All unit files require the root agent's explicit allowlist.
"""
from pathlib import Path
from datetime import datetime, timezone
import hashlib
import importlib.util
import json
import math
import subprocess

b = Path('/home/admin-wsl/Coq/abc/prove2me_workspace/.local/adaptation/conductor-extension-split-20261114')
spec = importlib.util.spec_from_file_location('conductor_extension_delivery', b / 'delivery.py')
unit = importlib.util.module_from_spec(spec)
spec.loader.exec_module(unit)
r, w, read, save, sha = unit.r, unit.w, unit.read, unit.save, unit.sha
PRE = 'AbcAdaptation.Tripod.Fermat.Proper.'
PARENT = PRE + 'belyiActualFieldConductorExtension'
PARENT_ID = '2383cd37-cc7e-49bd-afc6-838a919d2ce3'
CHILDREN = [PRE + 'belyiActualFieldLocalConductorComparison', PRE + 'belyiActualFieldDifferentAccounting']
DEFINITION_NAMES = ['FermatBelyiConductorExtensionFinitePlaces', 'FermatBelyiConductorExtensionChildren']
ADAPTER = 'Solutions/Source_FermatBelyiConductorExtensionAdapters.lean'
CHECKS = 'Solutions/Checks_FermatBelyiConductorExtensionReduction.lean'
CLOSED_CHECKS = 'Solutions/Checks_FermatBelyiConductorExtensionClosed.lean'
CANONICAL = 'AbcAdaptation.Tripod.Fermat.canonicalEstimate'
ROOT = 'abc.goal.lt_constant_mul_fix'
STANDARD = {'propext', 'Classical.choice', 'Quot.sound'}
TERMINAL = {'succeeded', 'failed', 'timeout', 'oom_killed', 'cancelled', 'interrupted', 'scheduler_error'}
FINAL_OUTPUTS = {'source-consumer.json', 'pending-db-scope.json',
                 'graph-count-evidence.json', 'unit-ci-summary.json', 'integration.json'}
BEFORE = {'accepted_reductions': 35, 'published_children': 81, 'dependency_edges': 99,
          'open_frontier': 17, 'direct_closed_children': 40}
AFTER = {'accepted_reductions': 36, 'published_children': 83, 'dependency_edges': 101,
         'open_frontier': 18, 'direct_closed_children': 40}


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


def retained_definitions(before, after, published_ids, approved):
    old = {row['theorem_id']: row for row in before['nodes']
           if row['node_type'] == 'theorem' and row['status'] == 'Definition'}
    new = {row['theorem_id']: row for row in after['nodes']
           if row['node_type'] == 'theorem' and row['status'] == 'Definition'}
    assert set(new) - set(old) == set(published_ids)
    common, missing = set(old) & set(new), set(old) - set(new)
    for ident in common:
        assert all(new[ident][key] == old[ident][key] for key in
                   ['theorem_id', 'theorem_name', 'status', 'formal_statement', 'definition'])
        assert not new[ident].get('deprecated_at') and not new[ident].get('deprecated_by')
        for key in ['visibility', 'mathlib_rev']:
            if key in old[ident] or key in new[ident]:
                assert new[ident].get(key) == old[ident].get(key)
    evidence = {'all_old_definitions_retained': True, 'visible_old_ids': sorted(common),
                'graph_hidden_old_ids': sorted(missing), 'new_definition_ids': sorted(published_ids)}
    if missing:
        filename = 'definition-retention-readbacks.json'
        assert filename in approved, 'Actual Definition GET evidence must be approved'
        rows = read(filename)['definitions']
        details = {row['theorem_id']: row for row in rows}
        assert len(details) == len(rows) and set(details) == missing
        for ident, detail in details.items():
            previous = old[ident]
            assert all(detail[key] == previous[key] for key in
                       ['theorem_id', 'theorem_name', 'status', 'formal_statement'])
            assert detail['status'] == 'Definition' and detail['visibility'] == 'private'
            assert detail['mathlib_rev'] == previous['mathlib_rev'] == unit.ENV
            codes = [detail[key] for key in ['definition', 'definitions']
                     if isinstance(detail.get(key), str) and detail[key]]
            assert codes and all(code.encode() == previous['definition'].encode() for code in codes)
            assert not detail.get('deprecated_at') and not detail.get('deprecated_by')
            assert not detail.get('deprecated', False) and not detail.get('is_deprecated', False)
        evidence.update(readbacks=filename, readbacks_sha256=sha(b / filename))
    return new, evidence


def pending_readback_terms(approved):
    filename = 'pending-readback-terms.json'
    assert filename in approved, 'Pending terminology inventory must be explicitly approved'
    inventory = read(filename)
    entries = inventory['entries']
    by_name = {row['name']: row for row in entries}
    assert len(by_name) == len(entries)
    marker = '【译名待定：DIFFERENT-IDEAL】'
    term = 'different ideal → ' + marker
    readbacks = read('final-readbacks.json')['declarations']
    actual = {row['declaration'] for row in readbacks if marker in row['zh_Hans']}
    assert set(by_name) == actual, 'Pending terms must exactly cover actual final Chinese readback placeholders'
    for row in entries:
        assert row['terms'] == [term] and row['user_answer_pending'] is True
        assert row['candidate_translations'] == ['不同理想', '差理想']
        assert row['name'] and not any(character in row['name'] for character in ['`', '\n', '\r'])
    # Each remaining marker is registered; compiler/binder alignment does not
    # imply a finalized translation for that term.
    for row in readbacks:
        assert ('【译名待定：' in row['zh_Hans']) == (row['declaration'] in actual)
        if row['declaration'] in actual:
            assert row['zh_Hans'].count('【译名待定：') == row['zh_Hans'].count(marker)
    if entries:
        assert inventory['question_asked'] is True
        lookup = inventory['lookup_evidence']
        assert lookup == 'terminology-lookup.json' and lookup in approved
        assert read(lookup), 'Keep actual terminology lookup evidence'
    lines = ['- `' + row['name'] + '`：`' + term + '`' for row in entries]
    evidence = {'inventory': filename, 'inventory_sha256': sha(b / filename),
        'pending_declarations': sorted(actual), 'pending_count': len(actual),
        'mathematical_readback_alignment_passed': True,
        'terminology_complete': not entries, 'section_four_added_lines': lines}
    return lines, evidence


def terminology_metadata(definitions, approved):
    filename = 'terminology-resolution.json'
    if not (b / filename).is_file():
        return None, {}, {'user_resolution_present': False}
    assert filename in approved
    resolution = read(filename)
    assert resolution['term_id'] == 'TERM-007' and resolution['term'] == 'different ideal'
    assert resolution['placeholder'] == '【译名待定：DIFFERENT-IDEAL】'
    assert resolution['translation'] == '不同理想' and resolution['user_approval']['confirmed'] is True
    assert resolution['user_approval']['statement'] and resolution['user_approval']['source']
    marker, translation = resolution['placeholder'], resolution['translation']
    declared = set(resolution['declarations'])
    assert len(declared) == len(resolution['declarations'])
    rows = read('final-readbacks.json')['declarations']
    superseded = {row['declaration'] for row in rows if 'superseded_pending_translation' in row}
    assert superseded == declared
    for row in rows:
        assert marker not in row['zh_Hans']
        if row['declaration'] in declared:
            previous = row['superseded_pending_translation']
            assert marker in previous and row['zh_Hans'] == previous.replace(marker, translation)
            assert row['terminology_resolution'] == filename
    expected_ids = read('published-definition-ids.json') | read('published-child-ids.json') | {PARENT: PARENT_ID}
    assert set(expected_ids) == set(DEFINITION_NAMES + CHILDREN + [PARENT])
    synced, file_hashes = {}, {}
    for sync_file in resolution['metadata_sync_files']:
        assert sync_file in approved
        sync = read(sync_file)
        assert sync['complete'] is True and sync['no_new_submission'] is True and sync['no_lean_change'] is True
        assert sync['immutable_hashes_before'] == sync['immutable_hashes_after']
        for name, digest in sync['immutable_hashes_after'].items():
            assert name in approved and sha(b / name) == digest
        for record in sync['records']:
            name, ident = record['name'], record['id']
            assert name in expected_ids and expected_ids[name] == ident and ident not in synced
            before, after, patch = record['before'], record['after'], record['patch']
            assert before['theorem_id'] == after['theorem_id'] == ident
            assert before['theorem_name'] == after['theorem_name'] == name
            assert set(patch) == {'natural_language_statement'}
            assert patch['natural_language_statement'] == before['natural_language_statement'].replace(marker, translation)
            assert after['natural_language_statement'] == patch['natural_language_statement']
            assert set(before) == set(after)
            assert all(before[key] == after[key] for key in before if key not in {'natural_language_statement', 'updated_at'})
            assert after['visibility'] == 'private' and after['mathlib_rev'] == unit.ENV
            assert after['status'] == ('Definition' if name in DEFINITION_NAMES else 'Open')
            if marker in before['natural_language_statement']:
                assert record['response'] is not None, 'Changed metadata requires a saved PATCH response'
            intent_name = 'terminology-metadata-intent-' + ident + '.json'
            assert intent_name in approved
            assert read(intent_name) == {key: record[key] for key in ['id', 'name', 'before', 'patch']}
            synced[ident] = record
        submission = sync['submission']
        if submission is not None:
            ident = read(unit.parent_verify_tag + '-verify-submit.json')['submission_id']
            assert submission['id'] == ident
            before, after, patch = submission['before'], submission['after'], submission['patch']
            original = read(unit.parent_verify_tag + '-verification-requested.json')['explanation']
            assert before['theorem_id'] == after['theorem_id'] == PARENT_ID
            assert before['status'] == after['status'] == 'SKETCH_ACCEPTED'
            assert patch == {'explanation': original.replace(marker, translation)}
            assert before['explanation'] in [original, patch['explanation']]
            assert after['explanation'] == patch['explanation']
            assert set(before) == set(after)
            assert all(before[key] == after[key] for key in before if key not in {'explanation', 'updated_at'})
            if before['explanation'] != after['explanation']:
                assert submission['response'] is not None
        file_hashes[sync_file] = sha(b / sync_file)
    assert set(synced) == set(expected_ids.values()), 'All five published records require exact terminology readbacks'
    return resolution, synced, {'user_resolution_present': True, 'resolution_sha256': sha(b / filename),
        'approved_translation': translation, 'resolved_declarations': sorted(declared),
        'metadata_sync_files': file_hashes, 'historical_publication_and_proof_bytes_preserved': True}


def final_metadata(original, historical_prose, resolution, synced):
    """Use genuine post-PATCH readbacks while preserving historical payloads."""
    if resolution is None:
        assert original['natural_language_statement'] == historical_prose
        return original
    record = synced[original['theorem_id']]
    before, after = record['before'], record['after']
    assert all(original[key] == before[key] for key in original
               if key not in {'natural_language_statement', 'updated_at'})
    expected = historical_prose.replace(resolution['placeholder'], resolution['translation'])
    assert original['natural_language_statement'] in [historical_prose, expected]
    assert before['natural_language_statement'] in [historical_prose, expected]
    assert after['natural_language_statement'] == expected
    return after


def expected_evidence(approved):
    prepared = unit.preflight()
    validation, jobs = prepared['validation'], prepared['required_jobs']
    assert unit.parent == PARENT and unit.PARENT_ID == PARENT_ID and unit.children == CHILDREN
    definitions = unit.definitions
    assert [row['name'] for row in definitions] == DEFINITION_NAMES
    assert all(row['source'] == 'Definitions/Def_' + row['name'] + '.lean' for row in definitions)
    core = {row['source'] for row in definitions} | {ADAPTER, CHECKS} | {
            theorem_path(name) for name in CHILDREN + [PARENT]}
    own = list(prepared['owned_sources'])
    assert len(own) == len(set(own)) and core <= set(own)
    assert set(own) in [core, core | {CLOSED_CHECKS}] and set(own) == set(unit.own)
    assert validation['passed'] is True
    assert validation['owned_source_hashes'] == {path: sha(w / path) for path in own}
    assert {row['job_id'] for row in jobs} == set(validation['compiler_checks'])
    assert set(prepared['required_evidence']) <= set(approved) | FINAL_OUTPUTS
    assert all((b / name).is_file() for name in prepared['required_evidence'])
    graph = unit.graph()
    by_name = {row['name']: row for row in graph}
    assert len(by_name) == len(graph)
    fresh_paths = {row['source'] for row in definitions} | {ADAPTER} | {
                  theorem_path(name) for name in CHILDREN + [PARENT]}
    authored = {row['name'] for row in graph if row['module'] in {
                path[:-5].replace('/', '.') for path in fresh_paths} and row['startLine'] > 0}
    rows = read('final-readbacks.json')['declarations']
    bound = {row['declaration']: row for row in rows}
    assert len(rows) == len(bound) == validation['readbacks']
    # The parser and compiler graph determine the final count after repairs.
    assert {row['declaration'] for row in rows if row['path'] in fresh_paths} == authored
    for name, row in bound.items():
        assert row['compiler_type'] == by_name[name]['elaboratedType']
        assert row['module'] == by_name[name]['module']
        assert row['source_sha256'] == sha(w / row['path'])
        assert all(isinstance(row[lang], str) and row[lang].strip() for lang in ['en', 'zh_Hans', 'ja'])
    binder = read('compiler-readback-type-review.json')
    assert binder['passed'] is True
    assert binder['compiler_evidence']['graph_sha256'] == sha(b / 'decl_graph.jsonl')
    assert len(binder['declarations']) == validation['fresh_compiler_binder_reviews']
    audited_names = {row['compiler_name'] for row in binder['declarations']}
    assert len(audited_names) == len(binder['declarations']) and audited_names == authored
    for row in binder['declarations']:
        actual = bound[row['compiler_name']]
        assert row['passed'] is True and row['compiler_type'] == actual['compiler_type']
        assert row['current_source']['sha256'] == actual['source_sha256']
        if row.get('corrected_trilingual_statement'):
            corrected = dict(row['corrected_trilingual_statement'])
            if (b / 'terminology-resolution.json').is_file():
                resolution = read('terminology-resolution.json')
                assert resolution['user_approval']['confirmed'] is True
                assert resolution['placeholder'] == '【译名待定：DIFFERENT-IDEAL】' and resolution['translation'] == '不同理想'
                corrected['zh_Hans'] = corrected['zh_Hans'].replace(resolution['placeholder'], resolution['translation'])
            assert all(actual[key] == corrected[key] for key in ['en', 'zh_Hans', 'ja'])
    axioms = read('all-module-axioms.json')
    open_modules = {theorem_path(name)[:-5].replace('/', '.') for name in CHILDREN + [PARENT]}
    fresh_modules = {path[:-5].replace('/', '.') for path in fresh_paths}
    expected_constants = {row['name'] for row in graph if row['module'] in fresh_modules}
    audit_by_name = {row['name']: row for row in axioms}
    assert expected_constants <= set(audit_by_name)
    for name in expected_constants:
        row = audit_by_name[name]
        permitted = by_name[name]['module'] in open_modules
        assert set(row['axioms']) <= STANDARD | ({'sorryAx'} if permitted else set())
        if name in set(CHILDREN + [PARENT]):
            assert 'sorryAx' in row['axioms']
    reached, todo = set(), [PARENT]
    while todo:
        name = todo.pop()
        if name in reached:
            continue
        reached.add(name)
        if name in by_name:
            todo += by_name[name]['typeDeps'] + by_name[name]['valueDeps']
    assert authored <= reached, 'Every authored output must have an actual consumer'
    ledger = read('source-consumer.json')
    ledger_names = {row['declaration'] for row in ledger['declarations']}
    assert len(ledger_names) == len(ledger['declarations']) and authored <= ledger_names <= reached
    review = read('independent-delivery-review.json')
    assert review['passed'] is True and review['source_ledger_passed'] is True
    assert review['all_new_outputs_have_actual_consumers'] is True
    assert review['source_ledger_sha256'] == sha(r / 'ArithmeticTeichmullerSpaces/SOURCE_LEDGER.md')
    return validation, own, jobs, definitions


def platform_graph(definitions, approved, resolution, synced):
    # There are no new direct proofs. The established summary preserves every
    # existing reduction and requires every sketch's actual mathematical edges.
    raw_before, raw_after = read('root-graph-before.json'), read('root-graph-after.json')
    before = unit.summary_without_direct_proof_nodes(raw_before, set())
    after = unit.summary_without_direct_proof_nodes(raw_after, set())
    old = {row['theorem_name']: row for row in before['mathematical'].values()}
    now = {row['theorem_name']: row for row in after['mathematical'].values()}
    ids = read('published-child-ids.json')
    assert set(ids) == set(CHILDREN) and len(set(ids.values())) == 2
    assert set(now) == set(old) | set(CHILDREN)
    assert set(after['mathematical']) == set(before['mathematical']) | set(ids.values())
    for name, previous in old.items():
        assert all(now[name][key] == previous[key] for key in ['theorem_id', 'status', 'formal_statement'])
    assert now[PARENT]['theorem_id'] == PARENT_ID == read('target-id.json')['id']
    assert all(now[name]['status'] == 'Open' for name in CHILDREN + [PARENT, CANONICAL, ROOT])
    assert all(now[name]['theorem_id'] == ids[name] for name in CHILDREN)
    parent_tag = unit.parent_verify_tag
    result, request, submitted = [read(parent_tag + suffix) for suffix in
        ['-verify-result.json', '-verify-request.json', '-verify-submit.json']]
    assert result['status'] == 'SKETCH_ACCEPTED' and result['id'] == submitted['submission_id']
    assert result['theorem_id'] == request['theorem_id'] == PARENT_ID
    assert request['proof_type'] == 'prove' and request['file'] == unit.sol
    assert request['source_sha256'] == sha(w / unit.sol)
    assert (b / (parent_tag + '-solution.lean')).read_bytes() == (w / unit.sol).read_bytes()
    assert read(parent_tag + '-verification-requested.json') == request
    previous = {row['submission_id']: row for row in before['reductions']}
    current = {row['submission_id']: row for row in after['reductions']}
    assert len(previous) == len(before['reductions']) and len(current) == len(after['reductions'])
    assert all(current[key] == value for key, value in previous.items())
    assert set(current) - set(previous) == {result['id']}
    added = current[result['id']]
    assert added == {'parent': PARENT, 'children': sorted(CHILDREN),
                     'submission_id': result['id'], 'status': 'SKETCH_ACCEPTED'}
    assert before['dependency_pairs'] <= after['dependency_pairs']
    assert after['dependency_pairs'] - before['dependency_pairs'] == {(PARENT, name) for name in CHILDREN}
    for summary, expected in [(before, BEFORE), (after, AFTER)]:
        assert summary['counts'] == {key: expected[key] for key in
            ['accepted_reductions', 'published_children', 'dependency_edges']}
    sketches = [row for row in raw_after['nodes'] if row['node_type'] == 'sketch' and row['submission_id'] == result['id']]
    assert len(sketches) == 1 and sketches[0]['parent_theorem_id'] == PARENT_ID
    actual = {edge['source'] for edge in raw_after['edges'] if edge['kind'] == 'sketch'
        and edge['target'] == sketches[0]['node_id'] and edge['source'] in after['mathematical']}
    assert actual == set(ids.values())
    published(unit.children_payload_tag, '/submit-problem', set(ids.values()))
    items = read(unit.children_payload_tag + '-payload.json')['problems']
    assert len(items) == 2 and {row['theorem_name'] for row in items} == set(CHILDREN)
    for item in items:
        state = read('platform-after-' + item['theorem_name'].removeprefix(PRE) + '.json')
        state = final_metadata(state, item['natural_language_statement'], resolution, synced)
        assert state['theorem_id'] == ids[item['theorem_name']] and state['status'] == 'Open'
        assert all(state[key] == item[key] for key in ['formal_statement', 'preamble', 'source'])
        assert state['visibility'] == 'private' and state['mathlib_rev'] == unit.ENV
        assert not state.get('deprecated_at') and not state.get('deprecated_by')
    new_ids = {}
    for definition in definitions:
        detail = read(definition['readback'])
        payload = read(definition['publish_tag'] + '-payload.json')
        detail = final_metadata(detail, payload['natural_language_statement'], resolution, synced)
        ident = detail['theorem_id']
        assert ident not in new_ids.values() and detail['theorem_name'] == definition['name']
        new_ids[definition['name']] = ident
        published(definition['publish_tag'], '/submit-definition', {ident})
        assert payload['definition_name'] == definition['name']
        assert detail['source'] == payload['source']
        code = (w / definition['source']).read_bytes()
        assert payload['definition'].encode() == code
        assert detail['status'] == 'Definition' and detail['visibility'] == 'private' and detail['mathlib_rev'] == unit.ENV
        codes = [detail[key] for key in ['definition', 'definitions']
                 if isinstance(detail.get(key), str) and detail[key]]
        assert codes and all(text.encode() == code for text in codes)
        assert not detail.get('deprecated_at') and not detail.get('deprecated_by')
    assert read('published-definition-ids.json') == new_ids
    visible_defs, retention = retained_definitions(raw_before, raw_after, set(new_ids.values()), approved)
    for definition in definitions:
        assert visible_defs[new_ids[definition['name']]]['definition'].encode() == (w / definition['source']).read_bytes()
    parent = read('platform-after-parent.json')
    patch = read('parent-metadata-patch-request.json')
    parent = final_metadata(parent, patch['natural_language_statement'], resolution, synced)
    assert parent['theorem_id'] == PARENT_ID and parent['status'] == 'Open'
    assert parent['formal_statement'] == read('platform-before-parent.json')['formal_statement'] == old[PARENT]['formal_statement']
    assert parent['preamble'] == read('platform-before-parent.json')['preamble']
    assert set(patch) == {'natural_language_statement', 'source'} and parent['source'] == patch['source']
    bf, af = read('root-frontier-before.json'), read('root-frontier-after.json')
    for frontier, nodes in [(bf, old), (af, now)]:
        rows = frontier['open_leaves']
        assert frontier['all_pages_fetched'] is True
        assert len(rows) == frontier['total'] == len({row['theorem_id'] for row in rows})
        assert all(nodes[row['theorem_name']]['status'] == 'Open' and
                   nodes[row['theorem_name']]['theorem_id'] == row['theorem_id'] for row in rows)
    expected = {row['theorem_name'] for row in bf['open_leaves']} - {PARENT} | set(CHILDREN)
    assert {row['theorem_name'] for row in af['open_leaves']} == expected
    assert bf['total'] == 17 and af['total'] == 18
    return before, after, now, ids, new_ids, result, added, expected, retention


def main():
    original_index = index_entries()
    original_staged = {path.decode() for path in git('diff', '--cached', '--name-only', '-z').split(b'\0') if path}
    assert not git('ls-files', '-u'), 'Resolve index conflicts before finalization'
    approved = approved_unit_files()
    validation, own, jobs, definitions = expected_evidence(approved)
    resolution, synced, resolution_evidence = terminology_metadata(definitions, approved)
    before, after, now, ids, definition_ids, result, added, expected, retention = platform_graph(definitions, approved, resolution, synced)
    records = ci_records(jobs, approved)
    registry_path = w / '.local/adaptation/platform-node-registry.json'
    registry = json.loads(registry_path.read_text())
    assert registry == read('registry-before.json'), 'Registry changed concurrently'
    assert registry['graph_counts'] == BEFORE
    assert sorted(registry['edges'], key=lambda row: row['submission_id']) == sorted(before['reductions'], key=lambda row: row['submission_id'])
    direct = registry['direct_closed_proofs']
    assert len(direct) == len({row['name'] for row in direct}) == 40
    assert all(now[row['name']]['status'] == 'Proved' for row in direct)
    counts = after['counts'] | {'open_frontier': 18, 'direct_closed_children': len(direct)}
    assert counts == AFTER
    document = r / 'docs/Prove2Me适配状态.md'
    original, updated = [(b / name).read_text() for name in ['pending-db-before.md', 'pending-db-after.md']]
    assert document.read_text() == original, 'Pending database changed concurrently'
    revision = 'Heights@721496ca4c158e511d25d8ccf6bfe8503eda73c1/Heights/Different/'
    old_line = '- `' + revision + 'Conductor.lean:170`'
    new_lines = ['- `' + revision + suffix + '`' for suffix in
                 ['Conductor.lean:104', 'NumberField.lean:228', 'NumberField.lean:256']]
    first, remainder = original.split('\n## 2.', 1)
    assert first.count(old_line + '\n') == 1 and all(line not in first for line in new_lines)
    candidate = first.replace(old_line + '\n', ''.join(line + '\n' for line in new_lines), 1)
    pending_lines, terminology = pending_readback_terms(approved)
    section_four = '\n## 4. 未完成自然语言读回的证明义务\n'
    assert remainder.count(section_four) == 1
    sections_two_three, previous_four = remainder.split(section_four, 1)
    # The existing section-four contents stay verbatim. This unit appends only
    # exact name/term rows, without narrative or mathematical status claims.
    appendix = ('\n' if not (section_four + previous_four).endswith('\n\n') else '')
    appendix += ''.join(line + '\n' for line in pending_lines)
    if not pending_lines:
        appendix = ''
    exact = candidate + '\n## 2.' + sections_two_three + section_four + previous_four + appendix
    assert updated == exact, 'Only the approved source split and exact pending terminology rows may change'
    keep = '- `Genl@ea2846c877d1e16d8f0b911a5fed07f5ee69eaaf/Genl/Curves/BelyiDescent.lean:248`'
    assert keep in updated
    assert updated.split('\n## 2.', 1)[1].split(section_four, 1)[0] == sections_two_three
    boundary = read('plan-checkbox-boundary-audit.json')
    assert sha(r / boundary['plan']) == boundary['sha256']
    assert boundary['newly_complete_broad_checkboxes'] == [] and boundary['boundary_changed'] is False
    assert boundary['Fermat_route_preserved'] is True and boundary['deprecations'] == []
    common = {'graph_counts': counts, 'children': ids, 'both_children_open': True,
        'parent': 'Open', 'canonicalEstimate': 'Open', 'root': 'Open', 'new_direct_proofs': [],
        'Fermat_route_preserved': True, 'production_boundary_changed': False, 'deprecations': [],
        'definition_ids': definition_ids, 'definition_retention': retention,
        'natural_language_readback_terms': terminology, 'terminology_resolution': resolution_evidence}
    registry.update(edges=sorted(after['reductions'], key=lambda row: (row['parent'], row['submission_id'])),
        published_nodes=sorted([{'name': row['theorem_name'], 'id': ident}
            for ident, row in after['mathematical'].items() if ident != unit.ROOT], key=lambda row: row['name']),
        graph_counts=counts, accepted_platform_reductions=36, dependency_edges=101,
        open_frontier=sorted(expected), local_open_children_below_root=18,
        published_open_children_below_root=18, mathematical_root_proved=False,
        platform_statuses={name: row['status'] for name, row in now.items()},
        recorded_at=datetime.now(timezone.utc).isoformat())
    assert registry['direct_closed_proofs'] == read('registry-before.json')['direct_closed_proofs']
    registry['conductor_extension_split_unit'] = common | {'source': str(b.relative_to(w)),
        'exact_original_parent_type_preserved': True, 'submission_id': result['id'],
        'no_new_assumptions_beyond_exact_two_open_children': True}
    source = read('source-consumer.json')
    source.update(common, status='exclusive_local_audits_passed_exact_two_child_SKETCH_ACCEPTED',
        platform_submission=result['id'],
        current_proof_debt_scope='The exact local-conductor comparison and different-accounting children remain Open. Their conductor-extension parent, canonicalEstimate and root remain Open.')
    save('source-consumer.json', source)
    save('pending-db-scope.json', {'removed_only': old_line, 'added_only': new_lines,
        'first_section_code_only': True, 'kept_parent_canonical_estimate_source': keep,
        'sections_two_three_unchanged': True, 'previous_section_four_unchanged': True,
        'section_four_appended_only': pending_lines, 'both_children_open': CHILDREN,
        'natural_language_readback_terms': terminology})
    save('graph-count-evidence.json', common | {'before': BEFORE, 'after': AFTER,
        'new_mathematical_nodes': ids, 'actual_new_reduction': added,
        'new_dependency_pairs': [[PARENT, name] for name in sorted(CHILDREN)],
        'old_mathematical_nodes_statuses_types_and_reductions_preserved': True})
    rss = [row['peak_rss_bytes'] for row in records if row['peak_rss_bytes'] is not None]
    save('unit-ci-summary.json', common | {'records': records,
        'succeeded': sum(row['status'] == 'succeeded' for row in records),
        'failed_or_other_terminal': sum(row['status'] != 'succeeded' for row in records),
        'peak_rss_bytes': max(rss) if rss else None, 'missing_resource_values': 'unknown, not zero'})
    save('integration.json', common | {'input_head': read('git-input-state.json')['head'],
        'owned_sources': validation['owned_source_hashes'], 'source_ledger': 'source-consumer.json',
        'original_parent_type_preserved': True,
        'status': 'Exact two-child conductor-extension split accepted; both arithmetic children remain Open'})
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
    print(json.dumps(common | {'audited_allowlist': len(files), 'definition_nodes_added': 2,
        'parent_submission': result['id'], 'git_index_mutated': False,
        'staging_candidates': str(b / 'staging-candidates.json'),
        'owned_sources': candidates['owned_sources'], 'metadata_files': candidates['metadata_files']}), flush=True)


if __name__ == '__main__':
    main()
