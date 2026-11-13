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
assert len(rows) == 9 and len({row['declaration'] for row in rows}) == 9
quote = (b / 'mochizuki-quotation.md').read_text().strip()
assert quote
common = (
    'Shinichi Mochizuki, Noncritical Belyi Maps (May 2004), Theorem 2.5, printed pp.5–6, https://www.kurims.kyoto-u.ac.jp/~motizuki/Noncritical%20Belyi%20Maps.pdf . The checked original quotation gives the noncritical-map geometric context; it does not assert these exact derivative implementations or local obstruction contracts. Pinned Lean source: lana-agents/belyi at '
    '9ce4d3f793d3bc831f2fc7214b7dbad90ea012d8, from '
    'refer/iut/lake-manifest.json. The concrete derivation construction comes from '
    'Belyi/CurveDeriv/Basic.lean; the two reduction contracts and finite-union '
    'combination come from Belyi/CurveField/NoncriticalFinite.lean. '
    'Source files retain their Apache-2.0 headers and author notices. The local '
    'derivative obstruction and finite derivative-failure locus remain Open. '
    'The parent reduction preserves the exact existing theorem type and all actual '
    'valuative places. No Belyi, Heights, Iut, or Genl runtime dependency is added. '
)
sources = {
    'FermatCurveDerivationEtale': 'CurveDeriv/Basic.lean Derivation.extendOfFormallyEtale. For the original compatible R/S/T algebra tower, extend an actual R-derivation S→T through the inverse formally-etale Kähler base-change equivalence. This is the source concrete construction, with the universal differential and no supplied extension law.',
    'FermatCurveDerivationPolynomial': 'CurveDeriv/Basic.lean coe_algEquivOfTranscendental, aeval_algEquivOfTranscendental_symm, polyDeriv and formallyEtale_adjoin. Transport actual Polynomial.derivative through the transcendental polynomial-adjoin equivalence, evaluate it in the original field, and reuse the exact source localization/separable-extension proof. The canonical rational algebra, actual adjoin and scalar tower are retained.',
    'FermatCurveDerivationBasic': 'CurveDeriv/Basic.lean derivAlong. The actual derivative extends polyDeriv when the supplied function is transcendental and the original field is algebraic over its rational simple intermediate field, with the exact source zero fallback otherwise. The original model and transcendence hypotheses ensure the intended branch in the child contexts. This construction supplies both child predicates; no free derivation or law record is introduced.',
    'noncriticalRegularRamifiedDerivNotMem': 'CurveField/NoncriticalFinite.lean exists_derivAlong_notMem, adapted to the existing actual Model and ramIdx. At any actual proper place containing the arbitrary transcendental function ψ with actual ramification index greater than one, some element of that same local ring has actual derivAlong ψ outside the local ring. This is a local witness theorem, with no finite-set conclusion or additional residue/coordinate restriction. Its source derivative-order and chain-rule proof remains Open.',
    'noncriticalDerivativeBadPlacesFinite': 'CurveField/NoncriticalFinite.lean finite_setOf_derivAlong_notMem. For the arbitrary supplied transcendental function ψ, the exact locus of all actual places containing ψ where some local element has actual derivative outside the local ring is finite. Its predicate has no ramIdx condition. The source finite chart-generator/localization proof remains Open; finiteness and derivative laws are not additional inputs.',
    'noncriticalRamificationFinite': 'CurveField/NoncriticalFinite.lean finite_setOf_one_lt_ramIdx. Reuse the existing finite pole locus and the Open finite derivative-failure locus. Every ramified place is a pole or, by the Open local obstruction child, a regular derivative-failure place. The finite-union/subset combination is the source proof and preserves the unchanged parent signature. Both Open children remain mathematical debt; this unit adds no direct proof closure.',
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
        'definition_title': module + ' — actual curve derivation construction',
        'definition': (w / relative).read_text(),
        'natural_language_statement': quote + '\n\n' + readback_prose(selected),
        'source': common + sources[module], 'env': ENV, 'private': True,
        'tags': ['abc-conjecture', 'arithmetic-geometry'],
    })

titles = {
    'noncriticalRegularRamifiedDerivNotMem': 'Actual derivation fails to preserve a regular ramified local ring',
    'noncriticalDerivativeBadPlacesFinite': 'Finitely many actual local rings fail preservation by the derivative',
}

for item in items:
    name = item['theorem_name'].removeprefix(pre)
    selected = [row for row in rows if row['declaration'] == pre + name]
    assert len(selected) == 1
    item.update(theorem_title=titles[name], natural_language_statement=quote + '\n\n' + readback_prose(selected),
                source=common + sources[name], tags=['abc-conjecture', 'arithmetic-geometry'])
results = publish('finite-children', '/submit-problem', {'problems': items, 'env': ENV, 'private': True})
assert len(results) == len(CHILDREN)
ids = {result['theorem_name']: result['theorem_id'] for result in results}
assert set(ids) == {pre + name for name in CHILDREN}
assert len(set(ids.values())) == len(CHILDREN)
save('published-child-ids.json', ids)

for name, expected, tag in [('noncriticalRamificationFinite', 'SKETCH_ACCEPTED', 'reduce-noncriticalRamificationFinite')]:
    selected = [row for row in rows if row['declaration'] == pre + name]
    assert len(selected) == 1
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
save('graph-noncriticalRamificationFinite.json', api.request('/theorems/' + existing_ids[pre + 'noncriticalRamificationFinite'] + '/graph?depth=2'))
frontier_after = fetch_frontier('after')
frontier = {leaf['theorem_name'] for leaf in frontier_after['open_leaves']}
frontier_before = {leaf['theorem_name'] for leaf in read('root-frontier-before.json')['open_leaves']}
assert frontier == (frontier_before - {pre + name for name in PARENTS}) | {pre + name for name in CHILDREN}
print('Two Open actual-derivative children published; noncriticalRamificationFinite SKETCH_ACCEPTED; no direct proof closure.', flush=True)
