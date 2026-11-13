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
assert len(rows) == 7 and len({row['declaration'] for row in rows}) == 7
quote = (b / 'mochizuki-quotation.md').read_text().strip()
assert quote
common = (
    'Shinichi Mochizuki, Noncritical Belyi Maps (May 2004), Theorem 2.5, '
    'https://www.kurims.kyoto-u.ac.jp/~motizuki/Noncritical%20Belyi%20Maps.pdf . '
    'The checked original quotation supplies geometric context for noncritical maps. '
    'The exact residue/minpoly indices, elementary-map value and ramification '
    'identities, and list induction come from the pinned Lean implementation: '
    'lana-agents/belyi at 9ce4d3f793d3bc831f2fc7214b7dbad90ea012d8, from '
    'refer/iut/lake-manifest.json. Source files retain their Apache-2.0 headers '
    'and author notices. The actual single-elementary-map composition theorem '
    'remains Open; the parent combines source positivity and list induction. '
    'The parent keeps its exact existing type and all actual residue embeddings. '
    'No Belyi, Heights, Iut, or Genl runtime dependency is added. '
)
sources = {
    'FermatNoncriticalRamificationPositive': 'Belyi/CurveField/NoncriticalBasic.lean ramIdx_pos, CurveField/RamIdx.lean residue_aeval and isIntegral_residue, and the elementary aeval_mem proof from CurveDeriv/Local.lean. Four concrete residue/polynomial helpers supply source positivity of the existing actual index at every place. The regular branch uses the full residue-field minimal polynomial and the pole branch uses negative normalized order. The construction uses no derivative carrier and imports no Open theorem.',
    'noncriticalElementaryCompositionRamification': 'Belyi/CurveField/NoncriticalElem.lean applyK_spec. For any actual QbarPoint embedding and one existing rational Möbius map with nonzero determinant or positive-degree rational polynomial, prove transcendence of the actual composed function, its exact point-value formula, and the actual multiplicative ramification-index formula. The integer cast of the existing elementary natural index is retained. The source polynomial/inversion/Möbius proof remains Open; no free map or chain-rule law is supplied.',
    'noncriticalCompositionRamification': 'Belyi/CurveField/NoncriticalBasic.lean ramIdx_pos and NoncriticalElem.lean compK_spec. The first parent conjunct uses source positivity at every place. The second uses list induction generalizing the actual input function, applies the one explicit elementary child at the head, then uses the induction hypothesis on that actual composed function. Existing compK/evalComp/ramIdxComp recursion and multiplication reassociation preserve the exact all-points parent statement. The one elementary child remains mathematical debt; this unit adds no direct proof closure.',
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
        'definition_title': module + ' — actual residue ramification positivity',
        'definition': (w / relative).read_text(),
        'natural_language_statement': quote + '\n\n' + readback_prose(selected),
        'source': common + sources[module], 'env': ENV, 'private': True,
        'tags': ['abc-conjecture', 'arithmetic-geometry'],
    })

titles = {
    'noncriticalElementaryCompositionRamification': 'Actual values and ramification under one rational elementary map',
}

for item in items:
    name = item['theorem_name'].removeprefix(pre)
    selected = [row for row in rows if row['declaration'] == pre + name]
    assert len(selected) == 1
    item.update(theorem_title=titles[name], natural_language_statement=quote + '\n\n' + readback_prose(selected),
                source=common + sources[name], tags=['abc-conjecture', 'arithmetic-geometry'])
results = publish('composition-children', '/submit-problem', {'problems': items, 'env': ENV, 'private': True})
assert len(results) == len(CHILDREN)
ids = {result['theorem_name']: result['theorem_id'] for result in results}
assert set(ids) == {pre + name for name in CHILDREN}
assert len(set(ids.values())) == len(CHILDREN)
save('published-child-ids.json', ids)

for name, expected, tag in [('noncriticalCompositionRamification', 'SKETCH_ACCEPTED', 'reduce-noncriticalCompositionRamification')]:
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
save('graph-noncriticalCompositionRamification.json', api.request('/theorems/' + existing_ids[pre + 'noncriticalCompositionRamification'] + '/graph?depth=2'))
frontier_after = fetch_frontier('after')
frontier = {leaf['theorem_name'] for leaf in frontier_after['open_leaves']}
frontier_before = {leaf['theorem_name'] for leaf in read('root-frontier-before.json')['open_leaves']}
assert frontier == (frontier_before - {pre + name for name in PARENTS}) | {pre + name for name in CHILDREN}
print('One Open elementary-composition child published; noncriticalCompositionRamification SKETCH_ACCEPTED; no direct proof closure.', flush=True)
