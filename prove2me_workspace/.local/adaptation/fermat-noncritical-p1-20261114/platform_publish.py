from graph_completion import fetch_complete_math_graph
from pathlib import Path
import ast
import hashlib
import importlib.util
import json
import time
import urllib.error
import urllib.request
import uuid

from delivery_common import (
    CHILDREN, ENV, EVIDENCE, MODULES, PARENTS, PREFIX, ROOT_ID,
    UNIT_REL, WORKSPACE, preflight, read, readback_prose, save, sha,
)

w, b, pre, ROOT = WORKSPACE, EVIDENCE, PREFIX, ROOT_ID
validation, items, existing_ids = preflight()
spec = importlib.util.spec_from_file_location('p2m_api', w / '.local/abc-item/api.py')
api = importlib.util.module_from_spec(spec)
spec.loader.exec_module(api)

# Reuse only the established publication and verification protocol functions.
protocol = (w / '.local/adaptation/platform-tripod-20261113/executed-platform-publish.py').read_text()
for node in ast.parse(protocol).body:
    if isinstance(node, ast.FunctionDef) and node.name in ['publish', 'verify']:
        exec(compile(ast.Module(body=[node], type_ignores=[]), '<established-platform-protocol>', 'exec'), globals())
original_publish, original_verify = publish, verify


def publish(tag, endpoint, payload):
    submitted = b / (tag + '-submit.json')
    if submitted.exists():
        assert read(tag + '-payload.json') == payload, ('Cached publication payload differs', tag)
    else:
        # A transport failure after POST needs reconciliation, not another POST.
        intent = b / (tag + '-publication-requested.json')
        assert not intent.exists(), ('Prior publication has no saved receipt; reconcile that request before retrying', tag)
        save(intent.name, {'endpoint': endpoint, 'payload_sha256': hashlib.sha256(
            json.dumps(payload, sort_keys=True, ensure_ascii=False).encode()).hexdigest()})
    results = original_publish(tag, endpoint, payload)
    assert all(result['status'] == 'PUBLISHED' and result['visibility'] == 'private' for result in results), tag
    return results


def verify(tag, target, file, explanation, expected):
    if (b / (tag + '-verify-submit.json')).exists():
        previous = read(tag + '-verify-request.json')
        assert previous == {'theorem_id': target, 'proof_type': 'prove', 'file': file,
                            'source_sha256': sha(w / file), 'explanation': explanation}, tag
        assert (b / (tag + '-solution.lean')).read_bytes() == (w / file).read_bytes(), tag
    else:
        intent = b / (tag + '-verification-requested.json')
        assert not intent.exists(), ('Prior verification has no saved receipt; reconcile that request before retrying', tag)
        save(intent.name, {'theorem_id': target, 'source_sha256': sha(w / file)})
    result = original_verify(tag, target, file, explanation)
    submitted = read(tag + '-verify-submit.json')
    assert result['status'] == expected, (tag, result['status'])
    assert result['id'] == submitted['submission_id'] and result['theorem_id'] == target, tag
    return result


rows = read('readbacks-final.json')['declarations']
quote = (b / 'mochizuki-quotation.md').read_text().strip()
assert quote
paper_quotes = {entry['id']: entry for entry in read('p1-mochizuki-quotes.json')['quotations']}
def source_quote(name):
    key = {'noncriticalP1Normalize':'P1-NORMALIZE', 'noncriticalP1Rational':'P1-RATIONAL', 'noncriticalP1Minpoly':'P1-MINPOLY-DESCENT'}.get(name, 'P1-THEOREM-COMBINATION')
    entry = paper_quotes[key]
    text = entry['sourceparagraph']
    pages = ', '.join(str(page) for page in entry['printed_pages'])
    return '> ' + text + '\n\n— Shinichi Mochizuki, *Noncritical Belyi Maps*, ' + entry['location'] + ', printed p. ' + pages + '.'
common = (
    'Shinichi Mochizuki, Noncritical Belyi Maps (May 2004), section 2, '
    'Lemmas 2.1–2.4 and the P¹ case of Theorem 2.5, '
    'https://www.kurims.kyoto-u.ac.jp/~motizuki/Noncritical%20Belyi%20Maps.pdf . '
    'The checked quotation records the source context. The paper uses reduced degrees and its own constants; the precise degree/count continuation contracts and fixed constant 9 belong to the pinned Lean implementation. This unit adapts the concrete '
    'Belyi/NoncriticalP1 definitions, reduction contracts and nested induction from '
    'lana-agents/belyi at 9ce4d3f793d3bc831f2fc7214b7dbad90ea012d8, pinned by '
    'refer/iut/lake-manifest.json. Source files retain their Apache-2.0 headers and '
    'author notices. The three source '
    'reduction steps remain Open. This is a decomposition of the unchanged parent, '
    'not direct proof closure. No Belyi, Heights, Iut, or Genl runtime dependency is added. '
)
sources = {
    'FermatNoncriticalP1Reduction': 'Belyi/NoncriticalP1/ElemMap.lean, Analytic.lean and Reduction.lean: actual rational-point inclusion, all-Qbar Galois stability, minpoly degree, finite branch set with actual infinity, actual complex algebra embedding, and the three concrete noncritical-Belyi conditions. The existing rational ElemMap constructors, evaluation and ramification functions are reused unchanged. Definitions import no Open theorem.',
    'noncriticalP1Normalize': 'Exact Reduction.normalize_step contract modulo namespace and transparent conjunction: a concrete elementary map normalizes the rational distinguished point to 9 and the finite algebraic branch points to the unit disc; Galois stability, every degree upper bound and top-degree count bounds are retained. Its continuation preserves all three actual noncritical-Belyi conditions. Source mathematical proof remains Open.',
    'noncriticalP1Rational': 'Exact Reduction.rational_step contract modulo namespace and transparent conjunction: branch points in the unit disc with minpoly degree at most one admit an actual rational elementary-map list noncritical at 9. Infinity and every ramified source point remain covered. Source mathematical proof remains Open.',
    'noncriticalP1Minpoly': 'Exact Reduction.minpoly_step contract modulo namespace and transparent conjunction: for d at least 2 and an actual degree-d point, preserve full Galois stability and degree bounds while reducing the top-degree count upper bound from n+1 to n; return a rational point excluded from the new branch set and a concrete precomposition continuation preserving all three conditions. Source mathematical proof remains Open.',
    'noncriticalP1Zero': 'Main.core_key nested induction, exists_isNoncriticalBelyi_withInf and the some-0 branch of exists_isNoncriticalBelyi. The outer degree bound decreases when its top-degree fiber is empty; otherwise the inner count bound decreases through the minpoly step. eraseNone, full Galois-stability transfer, infinity inclusion and restriction to the original S preserve the exact existing parent type. Only the three explicit Open children supply mathematical debt; no direct closure is claimed.',
}

def fetch_frontier(stage):
    leaves, offset, total = [], 0, None
    while True:
        page = api.request('/theorems/' + ROOT + '/open-leaves?limit=50&offset=' + str(offset))
        save('root-frontier-' + stage + '-page-' + str(offset) + '.json', page)
        if total is None:
            total = page['total']
        assert page['total'] == total, 'Open frontier changed during pagination'
        leaves.extend(page['open_leaves'])
        offset += len(page['open_leaves'])
        if offset >= total:
            break
        assert page['open_leaves']
    assert len(leaves) == total and len({leaf['theorem_id'] for leaf in leaves}) == total
    result = {'open_leaves': leaves, 'total': total, 'all_pages_fetched': True}
    save('root-frontier-' + stage + '.json', result)
    return result


# Keep the first baseline stable across a replay of a completed or interrupted run.
if not (b / 'root-graph-before.json').exists():
    save('root-graph-before.json', fetch_complete_math_graph(api, ROOT, save, 'root-graph-before'))
if not (b / 'root-frontier-before.json').exists():
    fetch_frontier('before')
if not (b / 'registry-before.json').exists():
    save('registry-before.json', json.loads((w / '.local/adaptation/platform-node-registry.json').read_text()))
for name in PARENTS:
    before = api.request('/theorems/' + existing_ids[pre + name])
    assert before['theorem_name'] == pre + name and before['visibility'] == 'private' and before['mathlib_rev'] == ENV
    if not (b / ('platform-before-' + name + '.json')).exists():
        save('platform-before-' + name + '.json', before)

for module in MODULES:
    relative = 'Definitions/Def_' + module + '.lean'
    selected = [row for row in rows if Path(row['path']).name == Path(relative).name]
    publish('def-' + module, '/submit-definition', {
        'definition_name': module,
        'definition_title': module + ' — concrete P¹ noncritical reduction definitions',
        'definition': (w / relative).read_text(),
        'natural_language_statement': source_quote(module) + '\n\n' + readback_prose(selected),
        'source': common + sources[module], 'env': ENV, 'private': True,
        'tags': ['abc-conjecture', 'arithmetic-geometry'],
    })

titles = {
    'noncriticalP1Normalize': 'Normalize actual P¹ branch points with degree and count bounds',
    'noncriticalP1Rational': 'Construct a concrete noncritical P¹ list for rational branch points',
    'noncriticalP1Minpoly': 'Reduce the actual P¹ top-degree count by a minimal polynomial',
}

for item in items:
    name = item['theorem_name'].removeprefix(pre)
    selected = [row for row in rows if row['declaration'] == pre + name]
    assert len(selected) == 1
    item.update(theorem_title=titles[name], natural_language_statement=source_quote(name) + '\n\n' + readback_prose(selected),
                source=common + sources[name], tags=['abc-conjecture', 'arithmetic-geometry'])
results = publish('p1-children', '/submit-problem', {'problems': items, 'env': ENV, 'private': True})
assert len(results) == len(CHILDREN)
ids = {result['theorem_name']: result['theorem_id'] for result in results}
assert set(ids) == {pre + name for name in CHILDREN}
assert len(set(ids.values())) == len(CHILDREN)
save('published-child-ids.json', ids)

for name, expected, tag in [('noncriticalP1Zero', 'SKETCH_ACCEPTED', 'reduce-noncriticalP1Zero')]:
    # The compiler-span Solution carries both private helper bodies before the public target.
    # Their source readbacks describe actual consumers; they are not separate platform nodes.
    helper_names = ['core_key', 'exists_isNoncriticalBelyi_withInf', name]
    parent_file = 'Thm_' + (pre + name).replace('.', '_') + '.lean'
    selected = [row for row in rows if Path(row['path']).name == parent_file
                and row['declaration'].rsplit('.', 1)[-1] in helper_names]
    assert len(selected) == 3
    by_short_name = {row['declaration'].rsplit('.', 1)[-1]: row for row in selected}
    assert set(by_short_name) == set(helper_names)
    selected = [by_short_name[helper] for helper in helper_names]
    explanation = source_quote(name) + '\n\n' + readback_prose(selected) + '\n\n' + common + sources[name]
    verify(tag, existing_ids[pre + name], UNIT_REL + 'Solution_' + name + '.lean', explanation, expected)

for name in CHILDREN + PARENTS:
    target = (ids if name in CHILDREN else existing_ids)[pre + name]
    after = api.request('/theorems/' + target)
    assert after['theorem_name'] == pre + name and after['visibility'] == 'private' and after['mathlib_rev'] == ENV
    assert after['status'] == 'Open', (name, after['status'])
    save('platform-after-' + name + '.json', after)
    print('node-status', name, after['status'], flush=True)
save('root-graph-after.json', fetch_complete_math_graph(api, ROOT, save, 'root-graph-after'))
save('graph-noncriticalP1Zero.json', api.request('/theorems/' + existing_ids[pre + 'noncriticalP1Zero'] + '/graph?depth=2'))
frontier_after = fetch_frontier('after')
frontier = {leaf['theorem_name'] for leaf in frontier_after['open_leaves']}
frontier_before = {leaf['theorem_name'] for leaf in read('root-frontier-before.json')['open_leaves']}
assert frontier == (frontier_before - {pre + name for name in PARENTS}) | {pre + name for name in CHILDREN}
print('Three Open P¹ source-step children published; noncriticalP1Zero SKETCH_ACCEPTED; no direct proof closure.', flush=True)
