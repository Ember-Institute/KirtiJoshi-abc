"""Offline draft for this two-child unit. Importing this module calls no API.
The root supplies final compiler-derived payloads, solutions, and explanations.
Call the three public functions only after the root's unit gates have passed.
"""
from pathlib import Path
import ast
import hashlib
import json
import time
import urllib.error
import urllib.request
import uuid

WORKSPACE = Path('/home/admin-wsl/Coq/abc/prove2me_workspace')
EVIDENCE = WORKSPACE / '.local/adaptation/fermat-noncritical-rational-split-20261115'
ENV = '0df444a360eaa60ab8c11dca51a86af692955474'
PREFIX = 'AbcAdaptation.Tripod.Fermat.Proper.'
DEGREE = PREFIX + 'noncriticalP1DegreeOneRational'
BRANCH = PREFIX + 'noncriticalP1RationalBranchSet'
PARENT = '24731147-737a-4074-862f-65dc4af5cdd6'
PROTOCOL = WORKSPACE / '.local/adaptation/platform-tripod-20261113/executed-platform-publish.py'


def _read(path):
    return json.loads(Path(path).read_text())


def _sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def _no_exact_self_import(code, own):
    target = 'Theorems.Thm_' + own['theorem_name'].replace('.', '_')
    imports = [word for line in code.decode('utf-8').splitlines()
               if line.lstrip().startswith('import ') for word in line.split()[1:]]
    return target not in imports


def _bound_protocol(api, binding_path):
    binding = _read(binding_path)
    assert binding['workspace'] == str(WORKSPACE)
    assert binding['evidence'] == str(EVIDENCE) and binding['env'] == ENV
    # These hashes bind root-supplied exact final inputs; no type is guessed here.
    for path, digest in binding['input_sha256'].items():
        assert _sha(path) == digest, ('Changed final input', path)
    assert binding['compiler_types'] in binding['input_sha256']
    assert binding['payloads'] in binding['input_sha256']
    _read(binding['compiler_types'])  # Format remains the root's compiler oracle format.
    payload = _read(binding['payloads'])
    assert payload['env'] == ENV and payload['private'] is True
    assert {p['theorem_name'] for p in payload['problems']} == {DEGREE, BRANCH}
    assert len(payload['problems']) == 2
    EVIDENCE.mkdir(parents=True, exist_ok=True)

    def save(name, data):
        (EVIDENCE / name).write_text(json.dumps(data, ensure_ascii=False, indent=2) + '\n')

    namespace = dict(w=WORKSPACE, b=EVIDENCE, api=api, ENV=ENV, save=save,
        json=json, hashlib=hashlib, time=time, urllib=urllib, uuid=uuid,
        _no_exact_self_import=_no_exact_self_import)
    functions = []
    expected_guard = ast.parse("assert ('import Theorems.Thm_'+own['theorem_name'].replace('.','_')).encode() not in code").body[0]
    replacements = 0
    for node in ast.parse(PROTOCOL.read_text()).body:
        if not isinstance(node, ast.FunctionDef) or node.name not in ['publish', 'verify']:
            continue
        if node.name == 'verify':
            for check in ast.walk(node):
                if isinstance(check, ast.Assert) and ast.dump(check.test) == ast.dump(expected_guard.test):
                    # Parent name is a prefix of BranchSet: use exact import tokens.
                    check.test = ast.Call(func=ast.Name(id='_no_exact_self_import', ctx=ast.Load()),
                        args=[ast.Name(id='code', ctx=ast.Load()), ast.Name(id='own', ctx=ast.Load())], keywords=[])
                    replacements += 1
        functions.append(node)
    assert {n.name for n in functions} == {'publish', 'verify'} and replacements == 1
    module = ast.fix_missing_locations(ast.Module(body=functions, type_ignores=[]))
    exec(compile(module, '<existing-publish-verify-protocol-only>', 'exec'), namespace)
    return binding, payload, namespace, save


def publish_children(api, binding_path):
    binding, payload, protocol, save = _bound_protocol(api, binding_path)
    tag = 'rational-p1-children'
    prior = EVIDENCE / (tag + '-payload.json')
    if prior.exists():
        assert _read(prior) == payload, 'Changed cached publication payload'
    intent = EVIDENCE / (tag + '-publication-requested.json')
    if not (EVIDENCE / (tag + '-submit.json')).exists():
        assert not intent.exists(), 'Reconcile prior POST without receipt before retrying'
        save(intent.name, {'endpoint': '/submit-problem', 'payload_sha256': _sha(binding['payloads'])})
    results = protocol['publish'](tag, '/submit-problem', payload)
    assert len(results) == 2
    assert all(r['status'] == 'PUBLISHED' and r['visibility'] == 'private' for r in results)
    ids = {r['theorem_name']: r['theorem_id'] for r in results}
    assert set(ids) == {DEGREE, BRANCH}
    save('published-child-ids.json', ids)
    return ids


def _verify(api, binding_path, key, target, expected):
    binding, _, protocol, save = _bound_protocol(api, binding_path)
    file = binding['solutions'][key]
    full = WORKSPACE / file
    assert str(full) in binding['input_sha256']
    code = full.read_bytes()
    tag = {'degree': 'prove-noncriticalP1DegreeOneRational',
           'parent': 'reduce-noncriticalP1Rational'}[key]
    prior = EVIDENCE / (tag + '-verify-request.json')
    explanation = binding['explanations'][key]
    if prior.exists():
        assert _read(prior) == {'theorem_id': target, 'proof_type': 'prove', 'file': file,
            'source_sha256': _sha(full), 'explanation': explanation}
        assert (EVIDENCE / (tag + '-solution.lean')).read_bytes() == code
    intent = EVIDENCE / (tag + '-verification-requested.json')
    if not (EVIDENCE / (tag + '-verify-submit.json')).exists():
        assert not intent.exists(), 'Reconcile prior verification without receipt before retrying'
        save(intent.name, {'theorem_id': target, 'source_sha256': _sha(full)})
    result = protocol['verify'](tag, target, file, explanation)
    submitted = _read(EVIDENCE / (tag + '-verify-submit.json'))
    assert result['status'] == expected
    assert result['id'] == submitted['submission_id'] and result['theorem_id'] == target
    return result


def verify_degree(api, binding_path, degree_id):
    return _verify(api, binding_path, 'degree', degree_id, 'ACCEPTED')


def reduce_parent(api, binding_path):
    return _verify(api, binding_path, 'parent', PARENT, 'SKETCH_ACCEPTED')
