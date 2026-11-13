"""Draft publisher. Run only after the main agent accepts compiler and readback evidence."""
from pathlib import Path
import importlib.util
import json
import time
import urllib.error
import urllib.request
import uuid

from graph_completion import fetch_complete_math_graph
from delivery_common import (
    ANCESTORS, EVIDENCE, ENV, MODULES, PIN, PREFIX, ROOT_ID, ROOT_NAME, TARGETS, WORKSPACE,
    ancestor_metadata, compare_graphs, graph_summary, preflight, read, readback_compiler_bindings, readback_prose, save, sha, solution_path,
)


def fetch_frontier(api, stage):
    leaves, offset, total = [], 0, None
    while True:
        page = api.request('/theorems/' + ROOT_ID + '/open-leaves?limit=50&offset=' + str(offset))
        save('root-frontier-' + stage + '-page-' + str(offset) + '.json', page)
        total = page['total'] if total is None else total
        assert page['total'] == total, 'Frontier changed during pagination; resume after graph propagation settles'
        leaves.extend(page['open_leaves'])
        offset += len(page['open_leaves'])
        if offset >= total:
            break
        assert page['open_leaves']
    assert len(leaves) == total == len({leaf['theorem_id'] for leaf in leaves})
    value = {'open_leaves': leaves, 'total': total, 'all_pages_fetched': True}
    save('root-frontier-' + stage + '.json', value)
    return value


def observe_theorem(api, ident, name):
    value = api.request('/theorems/' + ident)
    assert value['theorem_id'] == ident and value['theorem_name'] == name
    assert value['visibility'] == 'private' and value['mathlib_rev'] == ENV
    return value


def bind_intent(name, payload):
    path = EVIDENCE / name
    if path.exists():
        assert read(name) == payload, ('Request/evidence changed; reconcile before continuing', name)
    else:
        save(name, payload)


def publish_definition(api, tag, payload):
    intent = {'endpoint': '/submit-definition', 'payload': payload}
    if (EVIDENCE / (tag + '-submit.json')).exists():
        assert read(tag + '-payload.json') == payload
        assert read(tag + '-publication-requested.json') == intent
        submitted = read(tag + '-submit.json')
    else:
        assert not (EVIDENCE / (tag + '-publication-requested.json')).exists(), 'Reconcile publication intent without receipt; do not repeat POST'
        save(tag + '-payload.json', payload)
        save(tag + '-publication-requested.json', intent)
        submitted = api.request('/submit-definition', payload, 'POST')
        save(tag + '-submit.json', submitted)
    assert not submitted.get('errors'), submitted.get('errors')
    jobs = submitted.get('jobs') or [{'job_id': submitted['job_id']}]
    assert len(jobs) == 1
    for job in jobs:
        while True:
            result = api.request('/publish-jobs/' + job['job_id'])
            save(tag + '-' + job['job_id'] + '-result.json', result)
            if result['status'] in ['PUBLISHED', 'FAILED', 'ERROR']:
                break
            time.sleep(5)
        assert result['id'] == job['job_id'] and result['status'] == 'PUBLISHED'
        assert result['visibility'] == 'private'
    return result


def verify_existing(api, tag, name, target, explanation):
    relative = solution_path(name)
    code = (WORKSPACE / relative).read_bytes()
    assert b'sorry' not in code and b'admit' not in code
    if name == TARGETS[2]:
        regular = read('platform-after-' + TARGETS[0] + '.json')
        closed = observe_theorem(api, regular['theorem_id'], PREFIX + TARGETS[0])
        assert closed['status'] == 'Proved'
        regular_result = read('prove-' + TARGETS[0] + '-verify-result.json')
        assert regular_result['status'] == 'ACCEPTED' and regular_result['theorem_id'] == closed['theorem_id']
        save('published-child-context.json', [closed])
    own = observe_theorem(api, target, PREFIX + name)
    assert own['formal_statement'] == read('platform-before-' + name + '.json')['formal_statement']
    expected = {'theorem_id': target, 'proof_type': 'prove', 'file': relative,
                'source_sha256': sha(WORKSPACE / relative), 'explanation': explanation}
    submit_path = EVIDENCE / (tag + '-verify-submit.json')
    if submit_path.exists():
        assert read(tag + '-verify-request.json') == expected
        assert read(tag + '-verification-requested.json') == expected
        assert (EVIDENCE / (tag + '-solution.lean')).read_bytes() == code
        submitted = read(tag + '-verify-submit.json')
    else:
        assert not (EVIDENCE / (tag + '-verification-requested.json')).exists(), 'Reconcile verification intent without receipt; do not repeat POST'
        save(tag + '-verify-request.json', expected)
        (EVIDENCE / (tag + '-solution.lean')).write_bytes(code)
        save(tag + '-verification-requested.json', expected)
        boundary = 'p2m-' + uuid.uuid4().hex
        parts = []
        for key, value in [('theorem_id', target), ('proof_type', 'prove'), ('explanation', explanation)]:
            parts.append(('--' + boundary + '\r\nContent-Disposition: form-data; name="' + key + '"\r\n\r\n' + value + '\r\n').encode())
        parts.extend([('--' + boundary + '\r\nContent-Disposition: form-data; name="file"; filename="solution.lean"\r\nContent-Type: text/plain; charset=utf-8\r\n\r\n').encode() + code + b'\r\n',
                      ('--' + boundary + '--\r\n').encode()])
        credentials = json.loads((WORKSPACE / 'credentials.json').read_text())
        request = urllib.request.Request(api.base + '/verify', data=b''.join(parts), headers={
            'Authorization': 'Bearer ' + credentials['access_token'], 'Accept': 'application/json',
            'Content-Type': 'multipart/form-data; boundary=' + boundary}, method='POST')
        try:
            with api.opener.open(request, timeout=45) as response:
                submitted = json.load(response)
        except urllib.error.HTTPError as error:
            raise RuntimeError('Verification HTTP ' + str(error.code)) from None
        save(tag + '-verify-submit.json', submitted)
    ident = submitted['submission_id']
    while True:
        result = api.request('/verify?submission_id=' + ident)
        save(tag + '-verify-result.json', result)
        if result['status'] != 'PENDING':
            break
        time.sleep(5)
    assert result['status'] == 'ACCEPTED' and result['id'] == ident and result['theorem_id'] == target
    return result


def patch_metadata(api, name, target, natural, source):
    tag = 'metadata-' + name
    payload = {'natural_language_statement': natural, 'source': source}
    expected = {'endpoint': '/theorems/' + target, 'method': 'PATCH', 'payload': payload}
    current = observe_theorem(api, target, PREFIX + name)
    baseline = read('platform-before-' + name + '.json')
    assert current['formal_statement'] == baseline['formal_statement']
    assert current['status'] == 'Proved'
    if not (EVIDENCE / (tag + '-before.json')).exists():
        save(tag + '-before.json', current)
    bind_intent(tag + '-patch-request.json', expected)
    if not (EVIDENCE / (tag + '-patch-response.json')).exists():
        if all(current.get(key) == value for key, value in payload.items()):
            # A prior PATCH response can be lost. The exact desired state safely reconciles it.
            save(tag + '-patch-response.json', {'reconciled_from_exact_readback': True, 'theorem_id': target, 'observed': current})
        else:
            response = api.request('/theorems/' + target, payload, 'PATCH')
            save(tag + '-patch-response.json', response)
    after = observe_theorem(api, target, PREFIX + name)
    assert after['formal_statement'] == baseline['formal_statement'] and after['status'] == 'Proved'
    assert all(after.get(key) == value for key, value in payload.items())
    save(tag + '-after.json', after)
    save('platform-after-' + name + '.json', after)


def settle_graph(api, ids):
    baseline = graph_summary(read('root-graph-before.json'))
    old = {n['theorem_name']: n for n in baseline['mathematical'].values()}
    eligible = {name for name, n in old.items() if n['status'] == 'Proved'} | set(ids)
    while True:
        expanded = eligible | {e['parent'] for e in baseline['reductions'] if set(e['children']) <= eligible}
        if expanded == eligible:
            break
        eligible = expanded
    assert ROOT_NAME not in eligible, 'This unit must leave the mathematical root unproved'
    expected_ancestors = eligible - {name for name, n in old.items() if n['status'] == 'Proved'} - set(ids)
    # Read-only polling gives server propagation time. No adjacent status is set by this script.
    for attempt in range(13):
        graph = fetch_complete_math_graph(api, ROOT_ID, save, 'root-graph-settle-' + str(attempt))
        nodes = {n['theorem_name']: n for n in graph_summary(graph)['mathematical'].values()}
        assert nodes[ROOT_NAME]['status'] != 'Proved'
        pending = sorted(name for name in expected_ancestors | set(ids) if nodes[name]['status'] != 'Proved')
        save('graph-propagation.json', {'attempt': attempt, 'expected_from_existing_accepted_sketches': sorted(expected_ancestors), 'pending': pending})
        if not pending:
            save('root-graph-after.json', graph)
            return graph
        if attempt < 12:
            time.sleep(5)
    raise RuntimeError('Ancestor propagation is pending. Resume with saved submissions; do not resubmit or set statuses.')


def main():
    validation, ids, rows = preflight()
    graph_rows = [json.loads(line) for line in (EVIDENCE / 'decl_graph.jsonl').read_text().splitlines() if line.strip()]
    save('readback-compiler-bindings.json', readback_compiler_bindings(rows, graph_rows))
    spec = importlib.util.spec_from_file_location('p2m_api', WORKSPACE / '.local/abc-item/api.py')
    api = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(api)
    # Root may supply these baselines before running the publisher. Never overwrite them.
    if not (EVIDENCE / 'root-graph-before.json').exists():
        save('root-graph-before.json', fetch_complete_math_graph(api, ROOT_ID, save, 'root-graph-before'))
    if not (EVIDENCE / 'root-frontier-before.json').exists():
        fetch_frontier(api, 'before')
    if not (EVIDENCE / 'registry-before.json').exists():
        save('registry-before.json', json.loads((WORKSPACE / '.local/adaptation/platform-node-registry.json').read_text()))
    for name in TARGETS:
        before_path = EVIDENCE / ('platform-before-' + name + '.json')
        if not before_path.exists():
            save(before_path.name, observe_theorem(api, ids[PREFIX + name], PREFIX + name))
        before = read(before_path.name)
        assert before['theorem_id'] == ids[PREFIX + name] and before['theorem_name'] == PREFIX + name
        assert before['status'] == 'Open' and before['visibility'] == 'private' and before['mathlib_rev'] == ENV
    quote = (EVIDENCE / 'mochizuki-quotation.md').read_text().strip()
    assert quote
    bind_intent('delivery-intent.json', {'files': {name: sha(EVIDENCE / name) for name in [
        'sourceproof-validation.json', 'final-readbacks.json', 'mochizuki-quotation.md',
        'source-consumer.json', 'source-ledger-link.json']}, 'target_ids': ids})
    common = (
        'Shinichi Mochizuki, Noncritical Belyi Maps, Theorem 2.5, '
        'https://www.kurims.kyoto-u.ac.jp/~motizuki/Noncritical%20Belyi%20Maps.pdf . '
        'The checked original English quotation gives the geometric context. '
        'The exact order and inverse-index facts are proved by the independently adapted Apache-2.0 Belyi source at ' + PIN + ': '
        'CurveField/NoncriticalBasic.lean::ord_aeval_eq and '
        'CurveField/NoncriticalElem.lean::ord_aeval_of_notMem, exists_ramIdx_eq_mul_inv, inv_spec. '
        'The actual function field, every place, every algebraic point embedding, complete residue fields, '
        'strong induction, reverse polynomial and zero/unit/pole cases are retained. '
        'The exact existing Lean statement is unchanged. No new mathematical child or assumption is introduced. '
        'The mathematical root remains unproved. '
    )
    module = MODULES[0]
    relative = 'Definitions/Def_' + module + '.lean'
    selected = [row for row in rows if row['path'] == relative]
    assert len(selected) == 2
    publish_definition(api, 'def-' + module, {
        'definition_name': module, 'definition_title': module + ' — actual residue and order source helpers',
        'definition': (WORKSPACE / relative).read_text(),
        'natural_language_statement': quote + '\n\n' + readback_prose(selected),
        'source': common + 'Both residue/order helpers have immediate consumers in the regular and pole proofs.',
        'env': ENV, 'private': True, 'tags': ['abc-conjecture', 'arithmetic-geometry'],
    })
    for name in TARGETS:
        selected = [row for row in rows if row['declaration'] == PREFIX + name]
        assert len(selected) == 1
        natural = quote + '\n\n' + readback_prose(selected)
        explanation_rows = [row for row in rows if row['path'].endswith('_' + name + '.lean')]
        explanation = quote + '\n\n' + readback_prose(explanation_rows) + '\n\n' + common
        verify_existing(api, 'prove-' + name, name, ids[PREFIX + name], explanation)
        patch_metadata(api, name, ids[PREFIX + name], natural, common)
    after = settle_graph(api, ids)
    observed = {node['theorem_name']: node for node in graph_summary(after)['mathematical'].values()}
    for name in ANCESTORS:
        node = observed[PREFIX + name]
        if node['status'] == 'Proved':
            baseline = read('platform-before-' + name + '.json')
            natural, source = ancestor_metadata(name, baseline)
            patch_metadata(api, name, node['theorem_id'], natural, source)
    save('root-graph-after.json', fetch_complete_math_graph(api, ROOT_ID, save, 'root-graph-after'))
    after = read('root-graph-after.json')
    frontier = fetch_frontier(api, 'after')
    _, accepted_graph, _, changes = compare_graphs(read('root-graph-before.json'), after, ids, read('root-frontier-before.json'), frontier)
    save('observed-status-changes.json', changes)
    save('added-existing-child-dependency.json', accepted_graph['added_existing_child_dependency'])
    print(json.dumps({'definition': 'PUBLISHED', 'existing_direct_proofs': TARGETS,
                      'observed_status_changes': changes,
                      'added_existing_child_dependency': accepted_graph['added_existing_child_dependency'],
                      'mathematical_root_proved': False}, ensure_ascii=False), flush=True)


if __name__ == '__main__':
    main()
