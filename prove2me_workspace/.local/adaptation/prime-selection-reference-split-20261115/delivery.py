"""Private existing-mission delivery draft. Import and prepare() never call an API.

The main agent supplies the independently reviewed Definition metadata and ready
evidence. This tool does not compile, modify Git, launch/release a mission, send
messages, or update the node registry. See README.md for the ready contract.
"""
from pathlib import Path
import hashlib
import importlib.util
import json
import os
import time
import urllib.request
import uuid

WORKSPACE = Path('/home/admin-wsl/Coq/abc/prove2me_workspace')
UNIT = WORKSPACE / '.local/adaptation/prime-selection-reference-split-20261115'
ENV = '0df444a360eaa60ab8c11dca51a86af692955474'
MISSION = 'eeb5193f-68c0-41d0-9263-4a5ff7c801ee'
ROOT = 'e33ff731-60a7-43ef-87ae-c12aeba23cb5'
CREATOR = '89966734-f388-427a-9ea1-983923ff28a1'
SCOPE = 'detached-source-consumer-preparation-for-existing-private-mission'
DEFINITION = 'AbcAdaptation_Reference_Iut_Implication_PrimeSelection'
ORIGINALS = ['Iut.ChebyshevBound.exists_prime_notMem',
             'Iut.sum_log_primeFactors_le',
             'Iut.LocalHeightData.exists_prime_selection']
NAMES = ['AbcAdaptation.Reference.' + name for name in ORIGINALS]
TITLES = ['A bounded prime outside a finite set',
          'The logarithmic sum of distinct prime factors',
          'A prime adapted to finite local-height data']
GATES = {'new_leaf_modules', 'checks_axioms', 'import_audit', 'act1scene1',
         'axiom_audit', 'wrapped_kernel_type_identity', 'independent_readbacks',
         'definition_readbacks', 'source_ledger_consumers', 'git_diff_check',
         'existing_mission_scope'}


def read(path):
    return json.loads(Path(path).read_text())


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def save(path, value):
    """Flush complete JSON before replacing the prior checkpoint."""
    path = Path(path)
    tmp = path.with_name(path.name + '.tmp')
    with tmp.open('w') as stream:
        json.dump(value, stream, ensure_ascii=False, indent=2)
        stream.write('\n')
        stream.flush()
        os.fsync(stream.fileno())
    tmp.replace(path)


def relative_source(kind, name):
    prefix = {'Theorems': 'Thm_', 'Solutions': 'Sol_', 'Definitions': 'Def_'}[kind]
    return kind + '/' + prefix + name.replace('.', '_') + '.lean'


def trilingual(row):
    return '\n\n'.join('**' + title + '**\n\n' + row[key] for key, title in
        [('en', 'English'), ('zh-Hans', '简体中文'), ('ja', '日本語')])


def prepare(definition_metadata, output):
    """Build a reviewable packet from current files; no API or credentials use."""
    output = Path(output)
    output.mkdir(parents=True, exist_ok=True)
    metadata_path = Path(definition_metadata).resolve()
    metadata = read(metadata_path)
    assert metadata['independent_readback_passed'] is True
    assert all(metadata[key].strip() for key in ['en', 'zh-Hans', 'ja', 'definition_title'])
    ledger = read(UNIT / 'SOURCE_LEDGER.json')
    assert ledger['source_commit'] == '07cb1da58f6d428a670dbb5dd6093d428bcbcdd8'
    context = {row['declaration']: row for row in read(UNIT / 'paper-source-context.en.json')}
    readbacks = {row['declaration']: row for row in
                 read(UNIT / 'source-compiler-reviewed-readbacks.json')['readbacks']}
    code_path = relative_source('Definitions', DEFINITION)
    code = (WORKSPACE / code_path).read_text()
    assert metadata['source_sha256'] == sha(WORKSPACE / code_path)
    definition = {'definition_name': DEFINITION, 'definition_title': metadata['definition_title'],
        'definition': code, 'natural_language_statement': trilingual(metadata),
        'source': metadata['source'], 'env': ENV, 'private': True}
    publications = [{'tag': 'definition', 'endpoint': '/submit-definition', 'payload': definition}]
    sources, verification = {code_path: sha(WORKSPACE / code_path)}, []
    metadata_files = [metadata_path, UNIT / 'SOURCE_LEDGER.json',
        UNIT / 'source-compiler-reviewed-readbacks.json', UNIT / 'paper-source-context.en.json',
        UNIT / 'LICENSE.iut.Apache-2.0']
    for original, name, title in zip(ORIGINALS, NAMES, TITLES):
        payload_path = UNIT / 'payloads' / (name.replace('.', '_') + '.json')
        raw = read(payload_path)
        assert raw['theorem_name'] == name
        theorem, solution = [relative_source(kind, name) for kind in ['Theorems', 'Solutions']]
        assert (WORKSPACE / theorem).read_text().rstrip() == (raw['preamble'] + raw['formal_statement']).rstrip()
        assert (WORKSPACE / solution).read_text() == raw['solution'], ('Stale solution payload', name)
        assert 'Copyright (c) 2026 The iut contributors.' in raw['preamble']
        paper, rb = context[original], readbacks[original]
        quotation = '\n\n'.join('> ' + q['quote'] + '\n\n— IUT IV, p. ' + str(q['printed_page'])
            for q in paper['short_verbatim_quotes'])
        description = (trilingual(rb) + '\n\n**Paper source context (English)**\n\n' +
            paper['source_description_en'] + '\n\n' + paper['code_provenance_note_en'] +
            '\n\n**Short source quotations**\n\n' + quotation)
        rows = [row for row in ledger['theorems'] if row.get('original_name') == original]
        assert len(rows) == 1
        payload = {key: raw[key] for key in ['theorem_name', 'preamble', 'formal_statement']}
        payload.update(theorem_title=title, natural_language_statement=description,
            source=rows[0]['source'], env=ENV, private=True)
        tag = name.replace('.', '_')
        publications.append({'tag': tag, 'endpoint': '/submit-problem', 'payload': payload})
        verification.append({'tag': tag, 'theorem_name': name, 'source': solution})
        sources.update({path: sha(WORKSPACE / path) for path in [theorem, solution]})
        metadata_files.append(payload_path)
    packet = {'schema': 'prime-selection-private-delivery-v1', 'workspace': str(WORKSPACE),
        'mission_id': MISSION, 'root_id': ROOT, 'environment': ENV,
        'scope': SCOPE, 'root_graph_membership': False,
        'canonicalC22Connected': False, 'source_sha256': sources,
        'metadata_sha256': {str(path): sha(path) for path in metadata_files},
        'publications': publications, 'verification': verification}
    save(output / 'packet.json', packet)
    return packet


def preflight(packet_path, ready_path):
    packet, ready = read(packet_path), read(ready_path)
    assert ready['passed'] is True and ready['packet_sha256'] == sha(packet_path)
    assert packet['workspace'] == str(WORKSPACE) and packet['mission_id'] == MISSION
    assert packet['scope'] == SCOPE and packet['root_graph_membership'] is False
    assert packet['environment'] == ENV and packet['canonicalC22Connected'] is False
    assert set(ready['gates']) == GATES and all(value is True for value in ready['gates'].values())
    assert ready['source_sha256'] == packet['source_sha256']
    for path, digest in packet['source_sha256'].items():
        assert sha(WORKSPACE / path) == digest, ('Changed source', path)
    for path, digest in (packet['metadata_sha256'] | ready['evidence_sha256']).items():
        assert sha(path) == digest, ('Changed evidence', path)
    assert ready['ci_receipts']
    for path in ready['ci_receipts']:
        assert str(Path(path)) in ready['evidence_sha256']
        receipt = read(path)
        request, result = receipt['request'], receipt['result']
        assert receipt['status'] == 'succeeded' and result['exit_code'] == 0
        assert request['language'] == 'lean'
        assert request['workspace'] == str(WORKSPACE) and request['exclusive'] is True
        assert result['snapshot']['workspace_mode'] == 'exclusive_worktree'
        assert result['snapshot']['snapshot_id'] is None
        params = request['parameters']
        source = params.get('source') or params['args'][0]
        assert request['worktree_manifest']['source_sha256'] == sha(WORKSPACE / source)
        assert result['actual_arguments'] == ['lean', *([source] if 'source' in params else params['args'])]
        if request['task_type'] == 'review':
            assert result['review']['passed'] is True
    assert set(ready['explanations']) == set(NAMES)
    assert all(all(marker in text for marker in ['**English**', '**简体中文**', '**日本語**'])
               for text in ready['explanations'].values())
    return packet, ready


def load_api():
    spec = importlib.util.spec_from_file_location('p2m_api', WORKSPACE / '.local/abc-item/api.py')
    api = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(api)
    assert api.base == 'https://prove2.me/api/v1'
    return api


def mission_from_listing(listing):
    matches = [row for row in listing['missions'] if row['id'] == MISSION]
    assert len(matches) == 1, 'Expected existing mission missing or duplicated in list'
    mission = matches[0]
    assert mission['visibility'] == 'private' and mission['creator']['id'] == CREATOR
    assert mission['main_theorem']['theorem_id'] == ROOT
    return mission


def mutation(directory, tag, intent, submit):
    """Do not repeat a POST whose outcome was lost. Reconcile its receipt first."""
    path, receipt = directory / (tag + '-intent.json'), directory / (tag + '-submit.json')
    if path.exists():
        assert read(path) == intent, ('Changed request', tag)
        assert receipt.exists(), ('Unknown POST outcome; reconcile original request', tag)
    else:
        assert not receipt.exists()
        save(path, intent)
        save(receipt, submit())  # Persist job_id/submission_id before any poll.
    return read(receipt)


def poll(api, directory, tag, endpoint, successful, pending):
    while True:
        result = api.request(endpoint)
        save(directory / (tag + '-result.json'), result)
        if result['status'] not in pending:
            assert result['status'] in successful, (tag, result)
            return result
        time.sleep(5)


def verify_post(api, target, code, explanation):
    api.request('/me')  # Refresh the established credential loader before multipart use.
    boundary = 'p2m-' + uuid.uuid4().hex
    parts = []
    for key, value in [('theorem_id', target), ('proof_type', 'prove'), ('explanation', explanation)]:
        parts.append(('--' + boundary + '\r\nContent-Disposition: form-data; name="' + key +
                      '"\r\n\r\n' + value + '\r\n').encode())
    parts += [('--' + boundary + '\r\nContent-Disposition: form-data; name="file"; '
        'filename="solution.lean"\r\nContent-Type: text/plain; charset=utf-8\r\n\r\n').encode() + code + b'\r\n',
        ('--' + boundary + '--\r\n').encode()]
    credentials = read(WORKSPACE / 'credentials.json')
    request = urllib.request.Request(api.base + '/verify', data=b''.join(parts), method='POST',
        headers={'Authorization': 'Bearer ' + credentials['access_token'], 'Accept': 'application/json',
                 'Content-Type': 'multipart/form-data; boundary=' + boundary})
    with api.opener.open(request, timeout=45) as response:
        return json.load(response)


def deliver(packet_path, ready_path, directory):
    """Main-agent entry point. Explicit ready evidence is checked before the first API call."""
    packet, ready = preflight(packet_path, ready_path)
    directory = Path(directory)
    directory.mkdir(parents=True, exist_ok=True)
    api = load_api()
    listing = api.request('/missions?q=Arithmetic%20Teichmuller&limit=100')
    save(directory / 'mission-list-readback.json', listing)
    mission = mission_from_listing(listing)
    root = api.request('/theorems/' + ROOT)
    assert root['visibility'] == 'private' and root['mathlib_rev'] == ENV
    save(directory / 'mission-scope.json', {'scope': SCOPE, 'mission': mission,
        'root_graph_membership': False, 'root_id': ROOT, 'environment': ENV})
    before_path = directory / 'root-graph-before.json'
    if not before_path.exists():
        save(before_path, api.request('/theorems/' + ROOT + '/graph'))
    ids = read(directory / 'published-ids.json') if (directory / 'published-ids.json').exists() else {}
    for row in packet['publications']:
        preflight(packet_path, ready_path)
        submitted = mutation(directory, row['tag'], row,
            lambda: api.request(row['endpoint'], row['payload'], 'POST'))
        assert not submitted.get('errors'), submitted
        jobs = submitted.get('jobs') or [{'job_id': submitted['job_id']}]
        assert len(jobs) == 1
        result = poll(api, directory, row['tag'], '/publish-jobs/' + jobs[0]['job_id'],
                      {'PUBLISHED'}, {'PENDING', 'COMPILING'})
        assert result['visibility'] == 'private'
        name = row['payload'].get('theorem_name') or row['payload']['definition_name']
        assert result.get('theorem_name', result.get('definition_name')) == name
        ids[name] = result['theorem_id']
        save(directory / 'published-ids.json', ids)
        endpoint = '/definitions/' if row['endpoint'] == '/submit-definition' else '/theorems/'
        item = api.request(endpoint + ids[name])
        save(directory / (row['tag'] + '-published-item.json'), item)
        assert item['visibility'] == 'private' and item['mathlib_rev'] == ENV
        assert item.get('definition_name', item.get('theorem_name')) == name
    for row in packet['verification']:
        preflight(packet_path, ready_path)
        target, source = ids[row['theorem_name']], WORKSPACE / row['source']
        own = api.request('/theorems/' + target)
        assert own['visibility'] == 'private' and own['mathlib_rev'] == ENV
        assert own['theorem_name'] == row['theorem_name']
        code = source.read_bytes()
        assert ('import Theorems.Thm_' + row['theorem_name'].replace('.', '_')).encode() not in code
        copy = directory / ('verify-' + row['tag'] + '-solution.lean')
        if copy.exists():
            assert copy.read_bytes() == code
        else:
            copy.write_bytes(code)
        explanation = ready['explanations'][row['theorem_name']]
        intent = dict(row, theorem_id=target, source_sha256=sha(source), explanation=explanation)
        submitted = mutation(directory, 'verify-' + row['tag'], intent,
            lambda: verify_post(api, target, code, explanation))
        result = poll(api, directory, 'verify-' + row['tag'],
            '/verify?submission_id=' + submitted['submission_id'], {'ACCEPTED'}, {'PENDING'})
        assert result['id'] == submitted['submission_id'] and result['theorem_id'] == target
    after = api.request('/theorems/' + ROOT + '/graph')
    save(directory / 'root-graph-after.json', after)
    assert read(before_path) == after, 'Unexpected change to the existing mathematical root graph'
    summary = {'published_ids': ids, 'all_three_proofs': 'ACCEPTED', 'mission_id': MISSION,
        'visibility': 'private', 'scope': SCOPE, 'root_graph_membership': False,
        'canonicalC22Connected': False, 'root_graph_unchanged': True}
    save(directory / 'delivery-summary.json', summary)
    return summary
