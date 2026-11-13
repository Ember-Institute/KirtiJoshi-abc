"""DRAFT: run only after root integrates and accepts all scheduled CI/readbacks."""
from pathlib import Path
import ast
import hashlib
import importlib.util
import json
import time
import urllib.error
import urllib.request
import uuid

from graph_completion import fetch_complete_math_graph
from delivery_common import (
    EVIDENCE, ENV, MODULES, PARENT, PREFIX, ROOT_ID, TARGET, WORKSPACE,
    preflight, read, readback_prose, save, sha, solution_path,
)

w, b, pre = WORKSPACE, EVIDENCE, PREFIX


def fetch_frontier(api, stage):
    leaves, offset, total = [], 0, None
    while True:
        page = api.request('/theorems/' + ROOT_ID + '/open-leaves?limit=50&offset=' + str(offset))
        save('root-frontier-' + stage + '-page-' + str(offset) + '.json', page)
        total = page['total'] if total is None else total
        assert page['total'] == total, 'Frontier changed during pagination'
        leaves.extend(page['open_leaves'])
        offset += len(page['open_leaves'])
        if offset >= total:
            break
        assert page['open_leaves']
    assert len(leaves) == total == len({leaf['theorem_id'] for leaf in leaves})
    out = {'open_leaves': leaves, 'total': total, 'all_pages_fetched': True}
    save('root-frontier-' + stage + '.json', out)
    return out


def main():
    validation, ids, rows = preflight()
    spec = importlib.util.spec_from_file_location('p2m_api', w / '.local/abc-item/api.py')
    api = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(api)
    globals()['api'] = api
    # Reuse exactly the established transport protocol, with stronger request replay binding.
    protocol = (w / '.local/adaptation/platform-tripod-20261113/executed-platform-publish.py').read_text()
    for node in ast.parse(protocol).body:
        if isinstance(node, ast.FunctionDef) and node.name in ['publish', 'verify']:
            exec(compile(ast.Module(body=[node], type_ignores=[]), '<established-platform-protocol>', 'exec'), globals())
    original_publish, original_verify = globals()['publish'], globals()['verify']

    def publish_definition(tag, payload):
        endpoint = '/submit-definition'
        if (b / (tag + '-submit.json')).exists():
            assert read(tag + '-payload.json') == payload, ('Cached request differs', tag)
        else:
            intent = tag + '-publication-requested.json'
            assert not (b / intent).exists(), ('Reconcile prior request without saved receipt', tag)
            save(intent, {'endpoint': endpoint, 'payload_sha256': hashlib.sha256(
                json.dumps(payload, sort_keys=True, ensure_ascii=False).encode()).hexdigest()})
        results = original_publish(tag, endpoint, payload)
        assert len(results) == 1
        assert results[0]['status'] == 'PUBLISHED' and results[0]['visibility'] == 'private'
        return results

    def verify_existing(tag, target, explanation):
        relative = solution_path()
        expected = {'theorem_id': target, 'proof_type': 'prove', 'file': relative,
                    'source_sha256': sha(w / relative), 'explanation': explanation}
        if (b / (tag + '-verify-submit.json')).exists():
            assert read(tag + '-verify-request.json') == expected, tag
            assert (b / (tag + '-solution.lean')).read_bytes() == (w / relative).read_bytes(), tag
        else:
            intent = tag + '-verification-requested.json'
            assert not (b / intent).exists(), ('Reconcile prior verification without saved receipt', tag)
            save(intent, expected)
        result = original_verify(tag, target, relative, explanation)
        submitted = read(tag + '-verify-submit.json')
        assert result['status'] == 'ACCEPTED', result['status']
        assert result['id'] == submitted['submission_id'] and result['theorem_id'] == target
        return result

    quote = (b / 'mochizuki-quotation.md').read_text().strip()
    assert quote
    common = (
        'Shinichi Mochizuki, Noncritical Belyi Maps, Theorem 2.5, '
        'https://www.kurims.kyoto-u.ac.jp/~motizuki/Noncritical%20Belyi%20Maps.pdf . '
        'The checked original English quotation provides geometric context. '
        'The exact derivative finiteness fact is proved by the independently adapted '
        'Apache-2.0 Belyi source at 9ce4d3f793d3bc831f2fc7214b7dbad90ea012d8: '
        'CurveDeriv/Basic.lean, CurveDeriv/Local.lean, and '
        'CurveField/NoncriticalFinite.lean::finite_setOf_derivAlong_notMem. '
        'The actual derivAlong, full place carrier, finite module generators, '
        'integral closure, and localization denominator are retained. '
        'No new mathematical child or assumption is introduced. '
        'No Belyi, Heights, Iut or Genl runtime import is added. '
    )
    # Baselines survive a replay; never replace them with post-submission observations.
    if not (b / 'root-graph-before.json').exists():
        save('root-graph-before.json', fetch_complete_math_graph(api, ROOT_ID, save, 'root-graph-before'))
    if not (b / 'root-frontier-before.json').exists():
        fetch_frontier(api, 'before')
    if not (b / 'registry-before.json').exists():
        save('registry-before.json', json.loads((w / '.local/adaptation/platform-node-registry.json').read_text()))
    for name in [TARGET, PARENT]:
        target = ids[pre + TARGET] if name == TARGET else next(
            node['theorem_id'] for node in read('root-graph-before.json')['nodes']
            if node.get('theorem_name') == pre + PARENT)
        before = api.request('/theorems/' + target)
        assert before['theorem_name'] == pre + name and before['visibility'] == 'private' and before['mathlib_rev'] == ENV
        if not (b / ('platform-before-' + name + '.json')).exists():
            save('platform-before-' + name + '.json', before)

    sources = {
        'FermatCurveDerivationAdjoin': 'Six complete source helpers for the actual formally etale extension, polynomial derivative, evaluation and valuation-subring membership. Each has a concrete consumer in actual derivAlong membership.',
        'FermatCurveDerivationLocalization': 'Two complete source blocks: span induction for actual integral-closure generators and localization at the actual chart prime, including the denominator inverse in the original valuation subring.',
    }
    for module in MODULES:
        relative = 'Definitions/Def_' + module + '.lean'
        selected = [row for row in rows if Path(row['path']).name == Path(relative).name]
        assert len(selected) == (6 if module.endswith('Adjoin') else 2)
        publish_definition('def-' + module, {
            'definition_name': module, 'definition_title': module + ' — actual derivative source helpers',
            'definition': (w / relative).read_text(),
            'natural_language_statement': quote + '\n\n' + readback_prose(selected),
            'source': common + sources[module], 'env': ENV, 'private': True,
            'tags': ['abc-conjecture', 'arithmetic-geometry'],
        })
    selected = [row for row in rows if row['declaration'] == pre + TARGET]
    explanation = quote + '\n\n' + readback_prose(selected) + '\n\n' + common + (
        'Take the finite generating set of the actual chart module. The union of '
        'pole sets of its actual derivatives is finite. Outside that union, '
        'span induction gives derivative membership on the chart. Actual '
        'localization and the quotient rule extend membership to the entire local '
        'valuation ring, contradicting the bad-place witness. The exact existing '
        'statement is preserved; the Solution closure has no Open mathematical child. '
        'The consuming noncriticalRamificationFinite remains Open because its '
        'other local obstruction child remains Open. The mathematical root remains Open.'
    )
    verify_existing('prove-' + TARGET, ids[pre + TARGET], explanation)
    for name in [TARGET, PARENT]:
        target = read('platform-before-' + name + '.json')['theorem_id']
        after = api.request('/theorems/' + target)
        assert after['theorem_name'] == pre + name and after['visibility'] == 'private' and after['mathlib_rev'] == ENV
        assert after['status'] == ('Proved' if name == TARGET else 'Open'), (name, after['status'])
        save('platform-after-' + name + '.json', after)
    save('root-graph-after.json', fetch_complete_math_graph(api, ROOT_ID, save, 'root-graph-after'))
    frontier = fetch_frontier(api, 'after')
    before = read('root-frontier-before.json')
    assert {leaf['theorem_id'] for leaf in frontier['open_leaves']} == {
        leaf['theorem_id'] for leaf in before['open_leaves']} - {ids[pre + TARGET]}
    assert frontier['total'] == before['total'] - 1
    print('Two private Definitions PUBLISHED; existing derivative-finiteness proof ACCEPTED. No new child or reduction.', flush=True)


if __name__ == '__main__':
    main()
