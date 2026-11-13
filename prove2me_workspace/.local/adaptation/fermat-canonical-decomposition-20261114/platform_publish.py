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
    'Shinichi Mochizuki, Noncritical Belyi Maps (May 2004), proof of Theorem 2.5, '
    'printed p.6, https://www.kurims.kyoto-u.ac.jp/~motizuki/Noncritical%20Belyi%20Maps.pdf . '
    'The checked quotation gives geometric context for divisors and sections. Existing divisor-support '
    'and divisor-degree components independently reuse the Apache-2.0 Belyi project at '
    '9ce4d3f793d3bc831f2fc7214b7dbad90ea012d8 and the tuple-divisor convention in Heights at '
    '721496ca4c158e511d25d8ccf6bfe8503eda73c1, pinned by refer/iut; source notices are retained. '
    'The concrete Fermat coordinate-pole equality is a new Open specialization. Neither the quotation '
    'nor either pinned project is claimed to supply its proof. No Belyi, Heights, Iut, or Genl runtime dependency is added. '
)
sources = {
    'FermatInfinityDivisorFiniteSupport': 'Belyi/CurveField/ZerosPoles.lean and Divisor.lean, existing finite coordinate nonzero-order supports and Finsupp construction; Heights/Curve/TupleHeight.lean, the A_[1,u,v] coefficient convention. The actual max(pole_u,pole_v) coefficient has finite support on all proper places. No coordinate-pole equality, Fermat equation, fiber degree, canonical existence or adjunction is used.',
    'FermatCanonicalCoordinatePoleComposition': 'Belyi/CurveField/Degree.lean and Divisor.lean, already checked actual fiber-degree and divisor-degree laws. Conditional on the precise all-place equality of the fixed coordinate poles, the supplied H equals the actual polar divisor of u and has residue-degree-weighted degree N. Summing the original supplied J.coefficient and using principal degree zero gives the canonical degree. These conditional compositions supply neither the coordinate equality nor canonical/adjunction existence.',
    'coordinatePoleMultiplicity_eq': 'New Open Fermat specialization in the current project: for the fixed actual Model with 0<N, the actual normalized pole multiplicities of u and v agree at every proper place. It includes regular places, zero-coordinate cases and infinity. No proof is attributed to Belyi, Heights or the paper. The earlier unapproved common-pole proof is excluded from this delivery.',
    'infinityDivisorExists': 'Existing Belyi/CurveField/ZerosPoles.lean and Divisor.lean finite-support results, with the Heights/Curve/TupleHeight.lean coefficient convention. Construct the exact max(pole_u,pole_v) Finsupp over the union of the existing finite coordinate supports, then supply the unchanged InfinityDivisorData contract. This directly closes the existing theorem without an Open mathematical child.',
    'canonicalDivisorDegree': 'Conditional composition of existing actual Belyi/CurveField/Degree.lean and Divisor.lean laws with the one explicit Open coordinatePoleMultiplicity_eq child and the original actual PlaneAdjunctionData J. The unchanged parent signature retains M, hDVR, 3<N, hRF, K, H and J. This accepted reduction does not prove the coordinate equality, canonical divisor existence or plane adjunction existence.',
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
        'definition_title': module + ' — actual divisor support and conditional degree composition',
        'definition': (w / relative).read_text(),
        'natural_language_statement': quote + '\n\n' + readback_prose(selected),
        'source': common + sources[module], 'env': ENV, 'private': True,
        'tags': ['abc-conjecture', 'arithmetic-geometry'],
    })

titles = {'coordinatePoleMultiplicity_eq': 'Equal actual pole multiplicities of the fixed Fermat coordinates'}

for item in items:
    name = item['theorem_name'].removeprefix(pre)
    selected = [row for row in rows if row['declaration'] == pre + name]
    assert len(selected) == 1
    item.update(theorem_title=titles[name], natural_language_statement=quote + '\n\n' + readback_prose(selected),
                source=common + sources[name], tags=['abc-conjecture', 'arithmetic-geometry'])
results = publish('canonical-children', '/submit-problem', {'problems': items, 'env': ENV, 'private': True})
assert len(results) == len(CHILDREN)
ids = {result['theorem_name']: result['theorem_id'] for result in results}
assert set(ids) == {pre + name for name in CHILDREN}
assert len(set(ids.values())) == len(CHILDREN)
save('published-child-ids.json', ids)

for name, expected, tag in [('infinityDivisorExists', 'ACCEPTED', 'prove-infinityDivisorExists'),
                             ('canonicalDivisorDegree', 'SKETCH_ACCEPTED', 'reduce-canonicalDivisorDegree')]:
    selected = [row for row in rows if row['declaration'] == pre + name]
    assert len(selected) == 1
    explanation = quote + '\n\n' + readback_prose(selected) + '\n\n' + common + sources[name]
    verify(tag, existing_ids[pre + name], UNIT_REL + 'Solution_' + name + '.lean', explanation, expected)

for name in CHILDREN + PARENTS:
    target = (ids if name in CHILDREN else existing_ids)[pre + name]
    after = api.request('/theorems/' + target)
    assert after['theorem_name'] == pre + name and after['visibility'] == 'private' and after['mathlib_rev'] == ENV
    assert after['status'] == ('Proved' if name == 'infinityDivisorExists' else 'Open'), (name, after['status'])
    save('platform-after-' + name + '.json', after)
    print('node-status', name, after['status'], flush=True)
save('root-graph-after.json', api.request('/theorems/' + ROOT + '/graph?depth=10'))
save('graph-canonicalDivisorDegree.json', api.request('/theorems/' + existing_ids[pre + 'canonicalDivisorDegree'] + '/graph?depth=2'))
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
print('One Open coordinate-pole child published; infinityDivisorExists ACCEPTED; canonicalDivisorDegree SKETCH_ACCEPTED.', flush=True)
