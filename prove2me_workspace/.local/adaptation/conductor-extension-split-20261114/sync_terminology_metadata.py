"""Root-only existing-record metadata PATCH; never POST, compile, or edit proofs."""
from pathlib import Path
import hashlib
import importlib.util
import json
import math
from term_resolver import MARKER, approved_text, approval

w = Path('/home/admin-wsl/Coq/abc/prove2me_workspace')
b = w / '.local/adaptation/conductor-extension-split-20261114'
ENV = '0df444a360eaa60ab8c11dca51a86af692955474'
PARENT = '2383cd37-cc7e-49bd-afc6-838a919d2ce3'


def read(name):
    return json.loads((b / name).read_text())


def save(name, value):
    (b / name).write_text(json.dumps(value, ensure_ascii=False, indent=2) + '\n')


def immutable_hashes():
    paths = [p for p in b.iterdir() if p.is_file() and (
        p.name == 'blind-readbacks-source.json' or p.name.endswith('-payload.json') or
        p.name.endswith('-publication-requested.json') or p.name.endswith('-verification-requested.json') or
        p.name.endswith('-verify-request.json') or p.name.endswith('-solution.lean') or
        p.name.startswith('Solution_') and p.suffix == '.lean')]
    return {p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}


def submission(api, ident):
    page = 1
    while True:
        response = api.request('/submissions?page=' + str(page))
        found = [z for z in response['submissions'] if z.get('id', z.get('submission_id')) == ident]
        if found:
            assert len(found) == 1
            return found[0]
        assert page < math.ceil(response['total'] / 100), 'Original submission absent from complete API history'
        page += 1


def unchanged(before, after, mutable):
    assert set(before) == set(after)
    for key in before:
        if key not in mutable:
            assert before[key] == after[key], ('Unexpected metadata mutation', key)


def main():
    approval(b)
    locked = immutable_hashes()
    spec = importlib.util.spec_from_file_location('api', w / '.local/abc-item/api.py')
    api = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(api)
    assert api.base == 'https://prove2.me/api/v1'
    ids = read('published-definition-ids.json') | read('published-child-ids.json')
    ids['AbcAdaptation.Tripod.Fermat.Proper.belyiActualFieldConductorExtension'] = PARENT
    assert len(ids) == len(set(ids.values())) == 5
    records = []
    for name, ident in ids.items():
        before = api.request('/theorems/' + ident)
        assert before['theorem_id'] == ident and before['theorem_name'] == name
        assert before['visibility'] == 'private' and before['mathlib_rev'] == ENV
        patch = {'natural_language_statement': approved_text(before['natural_language_statement'])}
        intent = {'id': ident, 'name': name, 'before': before, 'patch': patch}
        save('terminology-metadata-intent-' + ident + '.json', intent)
        response = api.request('/theorems/' + ident, patch, 'PATCH') if MARKER in before['natural_language_statement'] else None
        after = api.request('/theorems/' + ident)
        unchanged(before, after, {'natural_language_statement', 'updated_at'})
        assert after['natural_language_statement'] == patch['natural_language_statement']
        assert MARKER not in after['natural_language_statement']
        records.append(intent | {'response': response, 'after': after})
        save('terminology-metadata-sync.json', {'records': records, 'submission': None,
             'immutable_hashes_before': locked, 'complete': False})
    ident = read('reduce-parent-verify-submit.json')['submission_id']
    original = read('reduce-parent-verification-requested.json')['explanation']
    explanation = None
    if MARKER in original:
        before = submission(api, ident)
        assert before['theorem_id'] == PARENT and before['status'] == 'SKETCH_ACCEPTED'
        patch = {'explanation': approved_text(original)}
        assert before['explanation'] in [original, patch['explanation']]
        save('terminology-submission-intent.json', {'id': ident, 'before': before, 'patch': patch})
        response = api.request('/submissions/' + ident, patch, 'PATCH') if before['explanation'] != patch['explanation'] else None
        after = submission(api, ident)
        unchanged(before, after, {'explanation', 'updated_at'})
        assert after['explanation'] == patch['explanation'] and MARKER not in after['explanation']
        explanation = {'id': ident, 'before': before, 'patch': patch, 'response': response, 'after': after}
    assert immutable_hashes() == locked
    save('terminology-metadata-sync.json', {'records': records, 'submission': explanation,
        'immutable_hashes_before': locked, 'immutable_hashes_after': immutable_hashes(),
        'complete': True, 'no_new_submission': True, 'no_lean_change': True})


if __name__ == '__main__':
    main()
