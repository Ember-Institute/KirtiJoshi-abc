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
common = (
    'Shinichi Mochizuki, Noncritical Belyi Maps (May 2004), Theorem 2.5 and its proof, '
    'printed pp.5–6, https://www.kurims.kyoto-u.ac.jp/~motizuki/Noncritical%20Belyi%20Maps.pdf . '
    'The checked quotation gives the geometric context. The exact independent Lean definitions and '
    'source-proof adaptations use the Apache-2.0 Belyi project at '
    '9ce4d3f793d3bc831f2fc7214b7dbad90ea012d8, pinned by refer/iut; source notices are retained. '
    'No Belyi, Iut, or Genl runtime dependency is added. '
)
sources = {
    'FermatNoncriticalFunctions': 'Belyi/CurveField/Point.lean:172–181; BelyiRelation.lean:35; NoncriticalBasic.lean values and ramIdx_of_ord_pos; NoncriticalP1/ElemMap.lean. Actual full residue fields and all their embeddings, actual rational elementary maps, and direct cusp finite support.',
    'FermatNoncriticalSimpleZeros': 'Belyi/CurveField/Noncritical.lean:44–67 and :98–125. Enlarge the requested actual place set, realize a reduced pole divisor through the already proved Riemann inputs, and invert the function to obtain actual simple zeros.',
    'FermatNoncriticalComposition': 'Belyi/CurveField/Noncritical.lean:126–171. Combine actual simple zeros, a finite all-embedding branch-value set, the rational P1 construction, and the all-place composition chain rule. The three unresolved inputs are explicit theorem children, not Definition assumptions.',
    'noncriticalRamificationFinite': 'Belyi/CurveField/NoncriticalFinite.lean:181–188, finite_setOf_one_lt_ramIdx. The proof for arbitrary supplied nonconstant functions remains Open: local derivations and finitely many chart generators must supply the finite ramification locus.',
    'noncriticalCompositionRamification': 'Belyi/CurveField/NoncriticalBasic.lean, ramIdx_pos; NoncriticalElem.lean:310–344, applyK_spec and compK_spec. Positivity, transcendence preservation, actual values and ramification multiplication for all elementary composites remain Open.',
    'noncriticalP1Zero': 'Belyi/NoncriticalP1/Main.lean, exists_isNoncriticalBelyi at tau=some 0. The actual rational Mobius/polynomial construction for a finite Galois-stable projective-line set remains Open; source rational and minimal-polynomial inductions are still required.',
    'cuspsFinite': 'Belyi/CurveField/BelyiRelation.lean:35, finite_belyiCusps. The actual cusp set is contained in the union of the finite support of ord(phi) and the positive-order support of phi-1. This source proof closes the existing theorem directly without an Open mathematical child.',
    'noncriticalSelection': 'Belyi/CurveField/Noncritical.lean:98–171. The proved Riemann construction supplies a function with simple zeros on a finite superset of the requested places. The three explicit Open children supply finite branch values, the composition chain rule and the rational P1 list; their composition gives the actual selected function. This is a conditional reduction and does not close the parent mathematically.',
}

# Keep the first baseline stable across a replay of a completed or interrupted run.
if not (b / 'root-graph-before.json').exists():
    save('root-graph-before.json', api.request('/theorems/' + ROOT + '/graph?depth=10'))
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
        'definition_title': module + ' — actual noncritical function constructions',
        'definition': (w / relative).read_text(),
        'natural_language_statement': quote + '\n\n' + readback_prose(selected),
        'source': common + sources[module], 'env': ENV, 'private': True,
        'tags': ['abc-conjecture', 'arithmetic-geometry'],
    })

titles = {
    'noncriticalRamificationFinite': 'Finite ramification locus of every actual nonconstant function',
    'noncriticalCompositionRamification': 'Actual values and ramification under rational elementary composition',
    'noncriticalP1Zero': 'Rational elementary noncritical construction on P1 avoiding zero',
}
for item in items:
    name = item['theorem_name'].removeprefix(pre)
    selected = [row for row in rows if row['declaration'] == pre + name]
    assert len(selected) == 1
    item.update(theorem_title=titles[name], natural_language_statement=quote + '\n\n' + readback_prose(selected),
                source=common + sources[name], tags=['abc-conjecture', 'arithmetic-geometry'])
results = publish('noncritical-children', '/submit-problem', {'problems': items, 'env': ENV, 'private': True})
assert len(results) == len(CHILDREN)
ids = {result['theorem_name']: result['theorem_id'] for result in results}
assert set(ids) == {pre + name for name in CHILDREN}
assert len(set(ids.values())) == len(CHILDREN)
save('published-child-ids.json', ids)

for name, expected, tag in [('cuspsFinite', 'ACCEPTED', 'prove-cuspsFinite'),
                             ('noncriticalSelection', 'SKETCH_ACCEPTED', 'reduce-noncriticalSelection')]:
    selected = [row for row in rows if row['declaration'] == pre + name]
    assert len(selected) == 1
    explanation = quote + '\n\n' + readback_prose(selected) + '\n\n' + common + sources[name]
    verify(tag, existing_ids[pre + name], UNIT_REL + 'Solution_' + name + '.lean', explanation, expected)

for name in CHILDREN + PARENTS:
    target = (ids if name in CHILDREN else existing_ids)[pre + name]
    after = api.request('/theorems/' + target)
    assert after['theorem_name'] == pre + name and after['visibility'] == 'private' and after['mathlib_rev'] == ENV
    assert after['status'] == ('Proved' if name == 'cuspsFinite' else 'Open'), (name, after['status'])
    save('platform-after-' + name + '.json', after)
    print('node-status', name, after['status'], flush=True)
save('root-graph-after.json', api.request('/theorems/' + ROOT + '/graph?depth=10'))
save('graph-noncriticalSelection.json', api.request('/theorems/' + existing_ids[pre + 'noncriticalSelection'] + '/graph?depth=2'))
leaves, offset, total = [], 0, None
while True:
    page = api.request('/theorems/' + ROOT + '/open-leaves?limit=50&offset=' + str(offset))
    save('root-frontier-page-' + str(offset) + '.json', page)
    if total is None:
        total = page['total']
    assert page['total'] == total, 'Open frontier changed during pagination'
    leaves.extend(page['open_leaves'])
    offset += len(page['open_leaves'])
    if offset >= total:
        break
    assert page['open_leaves']
assert len(leaves) == total and len({leaf['theorem_id'] for leaf in leaves}) == total
frontier = {leaf['theorem_name'] for leaf in leaves}
assert {pre + name for name in CHILDREN} <= frontier
assert not {pre + name for name in PARENTS} & frontier
save('root-frontier-after.json', {'open_leaves': leaves, 'total': total, 'all_pages_fetched': True})
print('Three Open children published; cuspsFinite ACCEPTED; noncriticalSelection SKETCH_ACCEPTED.', flush=True)
