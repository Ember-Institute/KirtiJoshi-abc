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
    CHILDREN, ENV, EVIDENCE, MODULES, PARENTS, PREFIX, READBACK_EXTRAS, ROOT_ID,
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
assert len(rows) == 27 and len({row['declaration'] for row in rows}) == 27
assert {PREFIX + name for name in CHILDREN + PARENTS} | set(READBACK_EXTRAS) <= {row['declaration'] for row in rows}
readback_prose(rows)  # Require all three languages for every normalized row.
quote = (b / 'mochizuki-quotation.md').read_text().strip()
assert quote
common = (
    'Shinichi Mochizuki, Noncritical Belyi Maps (May 2004), Theorem 2.5, '
    'https://www.kurims.kyoto-u.ac.jp/~motizuki/Noncritical%20Belyi%20Maps.pdf . '
    'The checked original quotation supplies geometric context. Exact order, '
    'residue/minpoly, inversion, polynomial and rational Mobius identities are '
    'adapted from lana-agents/belyi at 9ce4d3f793d3bc831f2fc7214b7dbad90ea012d8, '
    'pinned in refer/iut/lake-manifest.json. Source copyright, Apache-2.0 release '
    'headers and author notices are retained; no bundled license-text claim is made. '
    'Three actual order/inverse-index mathematical leaves remain Open. '
    'The existing single-elementary-map parent keeps its exact type and all '
    'actual residue embeddings. No Belyi, Heights, Iut or Genl runtime import is added. '
)
sources = {
    'FermatNoncriticalElementarySource': 'Belyi/CurveField/Point.lean eval_mul, eval_congr and eval_inv; NoncriticalBasic.lean eval_aeval and order/value expansions; NoncriticalElem.lean separable-composition root multiplicity, polynomial transcendence, degree-one ramification, inversion point/value proof and affine/inverse/affine Mobius decompositions; NoncriticalP1/ElemMap.lean actual point-map computation lemmas and the derivative criterion used only for degree-one root multiplicity. Its 21 source declarations use the existing actual carrier, normalized order, full residue fields and every residue embedding. inv_spec_of_ramIdx is conditional only on the exact actual inverse-index child equality. Definitions imports no Open theorem. The existing eval_zero has its genuine source consumer in generic eval_inv, then the inverse value proof and the actual non-affine Mobius parent branch.',
    'noncriticalPolynomialOrderAtRegularPoint': 'Belyi/CurveField/NoncriticalBasic.lean ord_aeval_eq. For every actual transcendental function regular at any full algebraic point and every nonzero rational polynomial, prove actual normalized order equals the actual ramification index times mapped-polynomial root multiplicity at the actual residue embedding. All quantifiers and full residue fields are retained. This exact mathematical boundary remains Open.',
    'noncriticalPolynomialOrderAtPole': 'Belyi/CurveField/NoncriticalElem.lean ord_aeval_of_notMem. At every actual pole of a transcendental function and for every nonzero rational polynomial, including constants, prove actual normalized order of the polynomial evaluation equals its natural degree times the function order. This exact mathematical boundary remains Open.',
    'noncriticalInverseRamification': 'Belyi/CurveField/NoncriticalElem.lean inv_spec second conjunct. For every actual transcendental function and every full algebraic point, prove actual inverse ramification index equals the original actual index. Pointwise zero, regular-unit and pole cases remain within this child. No abstract inversion law or additional nonzero-value premise is supplied. This exact mathematical boundary remains Open.',
    'noncriticalElementaryCompositionRamification': 'Belyi/CurveField/NoncriticalElem.lean poly_spec, mob_spec and applyK_spec constructor assembly. The actual polynomial regular branch uses the full residue-field minimal polynomial, separability and exact root multiplicity; the pole branch uses actual negative order. Both rational Mobius cases are retained, with nonzero determinant and actual affine/inverse/affine decomposition when c is nonzero. Intermediate transcendence proofs are retained. The source parent preserves its exact value/transcendence/ramification-product statement, with dependencies exactly the three Open order/inverse-index children. Source helper poly_spec and mob_spec are part of the full checked Solution closure, not extra mathematical platform nodes.',
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
    assert len(selected) == 21
    publish('def-' + module, '/submit-definition', {
        'definition_name': module,
        'definition_title': module + ' — actual elementary-map source helpers',
        'definition': (w / relative).read_text(),
        'natural_language_statement': quote + '\n\n' + readback_prose(selected),
        'source': common + sources[module], 'env': ENV, 'private': True,
        'tags': ['abc-conjecture', 'arithmetic-geometry'],
    })

titles = {
    'noncriticalPolynomialOrderAtRegularPoint': 'Actual polynomial order at every regular algebraic point',
    'noncriticalPolynomialOrderAtPole': 'Actual polynomial order at every pole',
    'noncriticalInverseRamification': 'Actual ramification index is invariant under inversion',
}

for item in items:
    name = item['theorem_name'].removeprefix(pre)
    selected = [row for row in rows if row['declaration'] == pre + name]
    assert len(selected) == 1
    item.update(theorem_title=titles[name], natural_language_statement=quote + '\n\n' + readback_prose(selected),
                source=common + sources[name], tags=['abc-conjecture', 'arithmetic-geometry'])
results = publish('elementary-children', '/submit-problem', {'problems': items, 'env': ENV, 'private': True})
assert len(results) == len(CHILDREN)
ids = {result['theorem_name']: result['theorem_id'] for result in results}
assert set(ids) == {pre + name for name in CHILDREN}
assert len(set(ids.values())) == len(CHILDREN)
save('published-child-ids.json', ids)

for name, expected, tag in [('noncriticalElementaryCompositionRamification', 'SKETCH_ACCEPTED', 'reduce-noncriticalElementaryCompositionRamification')]:
    selected = [row for row in rows if row['declaration'] in [pre + name] + READBACK_EXTRAS]
    assert len(selected) == 3
    explanation = quote + '\n\n' + readback_prose(selected) + '\n\n' + common + sources[name]
    verify(tag, existing_ids[pre + name], UNIT_REL + 'Solution_' + name + '.lean', explanation, expected)

for name in CHILDREN + PARENTS:
    target = (ids if name in CHILDREN else existing_ids)[pre + name]
    after = api.request('/theorems/' + target)
    assert after['theorem_name'] == pre + name and after['visibility'] == 'private' and after['mathlib_rev'] == ENV
    assert after['status'] == 'Open', (name, after['status'])
    save('platform-after-' + name + '.json', after)
    print('node-status', name, after['status'], flush=True)
save('root-graph-after.json', fetch_complete_math_graph(api, ROOT, save, 'root-graph-after'))
save('graph-noncriticalElementaryCompositionRamification.json', api.request('/theorems/' + existing_ids[pre + 'noncriticalElementaryCompositionRamification'] + '/graph?depth=2'))
frontier_after = fetch_frontier('after')
frontier = {leaf['theorem_name'] for leaf in frontier_after['open_leaves']}
frontier_before = {leaf['theorem_name'] for leaf in read('root-frontier-before.json')['open_leaves']}
assert frontier == (frontier_before - {pre + name for name in PARENTS}) | {pre + name for name in CHILDREN}
print('Three actual order/inverse-index Open children published; noncriticalElementaryCompositionRamification SKETCH_ACCEPTED; no direct proof closure.', flush=True)
