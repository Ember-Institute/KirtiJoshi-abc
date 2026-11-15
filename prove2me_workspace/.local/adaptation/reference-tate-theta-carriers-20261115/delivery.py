#!/usr/bin/env python3
"""Offline preparation and explicit private delivery of four volume and Tate carrier Definitions.

Import, prepare, and check never load credentials or call an API. Only deliver
and reconcile access the network. This module never compiles or edits Git.
"""
import argparse
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import time
import urllib.parse
import re

WORKSPACE = Path('/home/admin-wsl/Coq/abc/prove2me_workspace')
UNIT = WORKSPACE / '.local/adaptation/reference-tate-theta-carriers-20261115'
ENV = '0df444a360eaa60ab8c11dca51a86af692955474'
MISSION = 'eeb5193f-68c0-41d0-9263-4a5ff7c801ee'
ROOT = 'e33ff731-60a7-43ef-87ae-c12aeba23cb5'
CREATOR = '89966734-f388-427a-9ea1-983923ff28a1'
SCOPE = 'detached-source-consumer-preparation-for-existing-private-mission'
MODULES = ['TateCurvesTheta.TateCurve.JInvariant', 'TateCurvesTheta.TateCurve.Parametrization', 'Iut.Cor312.ThetaData.AdmissiblePrime', 'Iut.Cor312.ThetaData.TateStructure']
NAMES = ['AbcAdaptation_Reference_' + module.replace('.', '_') for module in MODULES]
GATES = {'new_leaf_modules', 'checks_axioms', 'wrapped_kernel_type_identity',
         'new_leaf_artifacts',
         'import_audit', 'act1scene1', 'axiom_audit', 'independent_readbacks',
         'source_ledger_consumers', 'git_diff_check', 'existing_mission_scope'}
CI_GATES = {'new_leaf_modules', 'checks_axioms', 'wrapped_kernel_type_identity',
            'new_leaf_artifacts',
            'import_audit', 'act1scene1', 'axiom_audit'}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def read(path):
    return json.loads(Path(path).read_text(encoding='utf-8'))


def sha(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b''):
            h.update(chunk)
    return h.hexdigest()


def save(path, value):
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(path.name + '.tmp')
    with temporary.open('w', encoding='utf-8') as stream:
        json.dump(value, stream, ensure_ascii=False, indent=2)
        stream.write('\n')
        stream.flush()
        os.fsync(stream.fileno())
    temporary.replace(path)
    fd = os.open(path.parent, os.O_RDONLY)
    try:
        os.fsync(fd)
    finally:
        os.close(fd)


def path_hashes(paths):
    return {str(Path(path).resolve()): sha(path) for path in paths}


def multilingual(row):
    return '\n\n'.join('**' + label + '**\n\n' + row[key] for key, label in
        [('en', 'English'), ('zh-Hans', '简体中文'), ('ja', '日本語')])


def publication_statement(readback, paper):
    """Keep independent formal readback and reviewed English paper context separate."""
    for key in ['source_context_en', 'implementation_scope_en', 'consumer_scope_en', 'publication_markdown']:
        require(isinstance(paper[key], str) and bool(paper[key].strip()), 'Missing final paper field: ' + key)
    require(isinstance(paper['quotation_ids'], list), 'Invalid paper quotation references')
    return ('**Formal-code readback**\n\n' + multilingual(readback) +
            '\n\n**Paper source context (English; separate from the formal-code readback)**\n\n' +
            paper['publication_markdown'] +
            '\n\nThese Definitions are detached source preparation; the consumer paths describe '
            'the original reference graph and do not establish live mission-root membership '
            'or S2-04 completion.')


def validate_independent_readbacks(blind, bundles):
    reviews = blind['independent_reviews']
    require(len(reviews) == 2 and len({r['reviewer_id'] for r in reviews}) == 2,
            'Two distinct actual independent readback contexts are required')
    inputs = {name: row['blindReadback']['sha256'] for name, row in bundles.items()}
    covered = set()
    for review in reviews:
        require(review['passed'] is True and review['fresh_context'] is True and
                review['input_only_formal_code'] is True, 'Independent readback is incomplete')
        require(re.fullmatch(r'gpt-6\.1(?:-[A-Za-z0-9_.]+)?', review['author_model']) is not None,
                'Independent readback must record its actual GPT-6.1 model')
        reviewed = review['input_sha256_by_definition']
        require(bool(reviewed) and set(reviewed) <= set(inputs) and
                all(digest == inputs[name] for name, digest in reviewed.items()),
                'Independent readback is not bound to its actual exact code-only input subset')
        covered.update(reviewed)
        require(sha(review['original_artifact']) == review['original_artifact_sha256'],
                'Independent unmodified original artifact changed')
    require(covered == set(inputs), 'Independent readback contexts do not cover all four exact inputs')
    return {r['reviewer_id']: r for r in reviews}


def prepare(wrapper_report, blind_readbacks, paper_context, source_ledger, output):
    """Package installed exact files and completed blind originals, without an API."""
    report = read(wrapper_report)
    require(report['definitionsBundleCount'] == 4, 'Expected four generated bundles')
    bundles = {b['definitionName']: b for b in report['bundles']}
    require(set(bundles) == set(NAMES), 'Unexpected wrapper bundle set')
    blind = read(blind_readbacks)
    require(blind['passed'] is True, 'Blind readback acceptance is incomplete')
    require(blind['unconfirmed_chinese_terms_preserved'] is True,
            'Actual formal Chinese readback requires review of any unresolved terms')
    rows = {b['definition_name']: b for b in blind['bundles']}
    require(set(rows) == set(NAMES), 'Blind readback bundle set differs')
    reviews = validate_independent_readbacks(blind, bundles)
    context = read(paper_context)
    require(context['schema'] == 'prove2me-reference-foundation-paper-context-v1',
            'Expected final source-only English paper-context schema')
    require('paper_sources' in context and 'quotations' in context, 'Missing final paper sources/quotations')
    papers = {b['module']: b for b in context['bundles']}
    require(set(papers) == set(MODULES), 'Paper-context module set differs')
    metadata_paths = [wrapper_report, blind_readbacks, paper_context, source_ledger]
    publications, sources = [], {}
    for name, module in zip(NAMES, MODULES):
        generated, rb, paper = bundles[name], rows[name], papers[module]
        relative = 'Definitions/Def_' + name + '.lean'
        source = WORKSPACE / relative
        code = source.read_text(encoding='utf-8')
        digest = sha(source)
        require(digest == generated['sha256'] == rb['source_sha256'],
                'Installed/generated/blind-reviewed source differs: ' + name)
        require(Path(generated['path']).read_bytes() == source.read_bytes(), 'Wrapper bytes differ')
        raw_payload = read(generated['payload'])
        require(raw_payload == {'definition_name': name, 'code': code}, 'Generator payload differs')
        require(sha(generated['payload']) == generated['payloadSha256'], 'Generator payload hash differs')
        require(rb['passed'] is True, 'Blind review not accepted: ' + name)
        provenance = rb['provenance']
        require(provenance['fresh_context'] is True and provenance['input_only_formal_code'] is True,
                'Blind review did not use a fresh code-only context')
        require(bool(provenance['author_model'].strip()), 'Missing actual blind author/model')
        require(provenance['reviewer_id'] in reviews and
                provenance['author_model'] == reviews[provenance['reviewer_id']]['author_model'] and
                reviews[provenance['reviewer_id']]['input_sha256_by_definition'].get(name) ==
                    generated['blindReadback']['sha256'],
                'Formal readback author is not an accepted independent GPT-6.1 context')
        require(sha(provenance['original_artifact']) == provenance['original_artifact_sha256'],
                'Blind original changed')
        require(provenance['input_sha256'] == generated['blindReadback']['sha256'],
                'Blind original was not bound to authenticated blind code')
        require(sha(generated['blindReadback']['path']) == provenance['input_sha256'],
                'Blind input changed')
        for key in ['en', 'zh-Hans', 'ja', 'definition_title', 'source']:
            require(isinstance(rb[key], str) and bool(rb[key].strip()), 'Missing reviewed ' + key)
            require('REPLACE_' not in rb[key], 'Placeholder formal readback: ' + key)
        if 'uniformizer' in rb['en'].lower() or 'uniformizer' in code.lower():
            require('【待定译名：uniformizer】' in rb['zh-Hans'],
                    'Unconfirmed Chinese uniformizer term was lost')
        require(len(rb['definition_title']) <= 200, 'Definition title exceeds API limit')
        statement = publication_statement(rb, paper)
        payload = {'definition_name': name, 'definition_title': rb['definition_title'],
                   'definition': code, 'natural_language_statement': statement,
                   'source': rb['source'], 'env': ENV, 'private': True}
        publications.append({'tag': name, 'endpoint': '/submit-definition', 'payload': payload})
        sources[relative] = digest
        metadata_paths.extend([generated['path'], generated['payload'],
                               generated['blindReadback']['path'], provenance['original_artifact']])
    metadata_paths.extend(r['original_artifact'] for r in reviews.values())
    packet = {'schema': 'reference-tate-theta-carriers-private-definitions-delivery-v3', 'workspace': str(WORKSPACE),
              'mission_id': MISSION, 'root_id': ROOT, 'environment': ENV, 'scope': SCOPE,
              'root_graph_membership': False, 'canonicalC22Connected': False,
              'source_sha256': sources, 'metadata_sha256': path_hashes(metadata_paths),
              'publications': publications, 'verification': [], 'publication_post_limit': 4}
    save(Path(output) / 'packet.json', packet)
    return packet


def preflight(packet_path, ready_path):
    packet, ready = read(packet_path), read(ready_path)
    require(ready['passed'] is True and ready['packet_sha256'] == sha(packet_path), 'Ready packet mismatch')
    expected = {'workspace': str(WORKSPACE), 'mission_id': MISSION, 'root_id': ROOT,
                'schema': 'reference-tate-theta-carriers-private-definitions-delivery-v3',
                'environment': ENV, 'scope': SCOPE, 'root_graph_membership': False,
                'canonicalC22Connected': False, 'verification': [], 'publication_post_limit': 4}
    require(all(packet[k] == v for k, v in expected.items()), 'Private existing-mission scope changed')
    require(set(ready['gates']) == GATES and all(v is True for v in ready['gates'].values()),
            'Required delivery gates are incomplete')
    require(ready['source_sha256'] == packet['source_sha256'], 'Ready source set differs')
    require(ready['kernel_coverage'] == {'source': 78, 'resolved': 78, 'named': 76, 'proof': 2,
                'historical_requiredComparedCount': 78}, 'Project78=76+2 coverage changed')
    require(ready['standard_compatibility']['standard_proof_value_resolution_count'] == 2 and
            ready['standard_compatibility']['ring_native_proof_resolution_count'] == 1 and
            ready['standard_compatibility']['original'] == 'NumberField.RingOfIntegers.instHasFiniteQuotients' and
            ready['standard_compatibility']['standalone_target_identity'] is None,
            'Separate exact standard proof count/identity changed')
    adic = ready['adic_source_compatibility']
    require((adic['required_original_record_count'], adic['genuine_original_data_count'],
             adic['genuine_original_proof_body_count'], adic['native_card_pow_proof_count'],
             adic['standard_native_proof_count_including_ring'], adic['unused_original_proof_archive_count']) == (35, 8, 26, 1, 2, 15) and
            [r['job_id'] for r in adic['leaves']] == ['ci-014497-4264b653', 'ci-014507-f12c827f'] and
            all(r['peak_rss_bytes'] is not None and r['peak_rss_bytes'] <= 16 * 1024**3 for r in adic['leaves']),
            'Only the exact two actual low-RSS source DAG leaves can support35/8/26/CardPow1 compatibility')
    require(len(packet['publications']) == 4 and
            [r['tag'] for r in packet['publications']] == NAMES, 'Expected exactly four Definitions')
    require(set(packet['source_sha256']) == {'Definitions/Def_' + n + '.lean' for n in NAMES},
            'Unexpected source set')
    for source, digest in packet['source_sha256'].items():
        require(sha(WORKSPACE / source) == digest, 'Changed source: ' + source)
    for path, digest in list(packet['metadata_sha256'].items()) + list(ready['evidence_sha256'].items()):
        require(sha(path) == digest, 'Changed evidence: ' + path)
    for row in packet['publications']:
        p = row['payload']
        require(row['endpoint'] == '/submit-definition' and p['private'] is True and p['env'] == ENV,
                'Unexpected publication type/environment/privacy')
        require(p['definition_name'] == row['tag'] and
                p['definition'] == (WORKSPACE / ('Definitions/Def_' + row['tag'] + '.lean')).read_text(),
                'Publication is not exact installed source')
    require(set(ready['ci_receipts']) == CI_GATES, 'Missing CI gate receipts')
    for gate, receipt_paths in ready['ci_receipts'].items():
        require(bool(receipt_paths), 'Empty CI gate receipts: ' + gate)
        for path in receipt_paths:
            require(str(Path(path).resolve()) in ready['evidence_sha256'], 'Unhashed CI receipt')
            receipt = read(path)
            request, result = receipt['request'], receipt['result']
            require(isinstance(receipt['job_id'], str) and bool(receipt['job_id']) and
                    receipt['status'] == 'succeeded' and result['exit_code'] == 0, 'CI did not pass')
            require(request['language'] == 'lean' and request['workspace'] == str(WORKSPACE)
                    and request['exclusive'] is True, 'Wrong CI workspace or mode')
            require(result['snapshot']['workspace_mode'] == 'exclusive_worktree' and
                    result['snapshot']['snapshot_id'] is None, 'CI did not use stable exclusive inputs')
            params = request['parameters']
            source = params.get('source') or params['args'][0]
            require(request['worktree_manifest']['source_sha256'] == sha(WORKSPACE / source),
                    'CI source is stale')
            args = [params['source']] if 'source' in params else params['args']
            require(result['actual_arguments'] == ['lean', *args], 'Unexpected compiler arguments')
            resources = receipt['resources']
            require(resources.get('peak_rss_bytes') is not None, 'Missing physical RSS')
            if request['task_type'] == 'leaf':
                require(resources['peak_rss_bytes'] <= 16 * 1024**3, 'Leaf physical RSS exceeds 16 GiB')
            for input_path, digest in request['worktree_manifest'].get('input_hashes', {}).items():
                require(sha(input_path) == digest, 'CI dependency input changed: ' + input_path)
            if request['task_type'] == 'review':
                require(result['review']['passed'] is True, 'CI review failed')
    leaves = [read(p)['request'] for p in ready['ci_receipts']['new_leaf_modules']]
    require(len(leaves) == 4 and {q['parameters'].get('source') for q in leaves
             if q['task_type'] == 'leaf' and q['target'] == 'file'} == set(packet['source_sha256']),
            'Four exact new leaves lack successful leaf receipts')
    artifacts = [read(p)['request'] for p in ready['ci_receipts']['new_leaf_artifacts']]
    require(len(artifacts) == 4, 'Four artifact receipts are required')
    require({q['parameters']['args'][0] for q in artifacts} == set(packet['source_sha256']),
            'Artifact receipt source set differs')
    for q in artifacts:
        source = q['parameters']['args'][0]
        expected_output = '.lake/build/lib/lean/' + source.removesuffix('.lean') + '.olean'
        require(q['task_type'] == 'full' and q['target'] == 'module' and
                q['parameters']['args'] == [source, '-o', expected_output],
                'Artifact receipt is not the exact installed Definition artifact')
    require(ready['axiom_audit']['sorryAx_found'] is False and
            ready['axiom_audit']['unexpected_axioms'] == [], 'Axiom audit not accepted')
    for gate in ['independent_readbacks', 'source_ledger_consumers', 'git_diff_check', 'existing_mission_scope']:
        require(bool(ready['gate_evidence'][gate]), 'Missing evidence for ' + gate)
        require(all(str(Path(p).resolve()) in ready['evidence_sha256'] for p in ready['gate_evidence'][gate]),
                'Unhashed gate evidence: ' + gate)
    return packet


def load_api():
    spec = importlib.util.spec_from_file_location('p2m_api', WORKSPACE / '.local/abc-item/api.py')
    api = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(api)
    require(api.base == 'https://prove2.me/api/v1', 'Unexpected API base')
    return api


def check_scope(api, directory):
    listing = api.request('/missions?q=Arithmetic%20Teichmuller&limit=100')
    save(directory / 'mission-list-readback.json', listing)
    matches = [m for m in listing['missions'] if m['id'] == MISSION]
    require(len(matches) == 1, 'Existing mission missing or duplicated')
    mission = matches[0]
    require(mission['visibility'] == 'private' and mission['creator']['id'] == CREATOR
            and mission['main_theorem']['theorem_id'] == ROOT, 'Existing mission scope differs')
    root = api.request('/theorems/' + ROOT)
    save(directory / 'mission-root-readback.json', root)
    require(root['visibility'] == 'private' and root['mathlib_rev'] == ENV, 'Root scope differs')


def check_job(job, row):
    p = row['payload']
    require(job['kind'] == 'definition' and job['theorem_name'] == p['definition_name'], 'Wrong publish job')
    require(job['visibility'] == 'private' and job['definitions'] == p['definition'], 'Job code/privacy differs')
    for key, remote_key in [('definition_title', 'theorem_title'),
                            ('natural_language_statement', 'natural_language_statement'), ('source', 'source')]:
        require(job[remote_key] == p[key], 'Job metadata differs: ' + key)
    if 'mathlib_rev' in job:
        require(job['mathlib_rev'] == ENV, 'Job environment differs')


def check_definition(api, directory, row, target):
    item = api.request('/definitions/' + urllib.parse.quote(target, safe=''))
    save(directory / (row['tag'] + '-published-item.json'), item)
    require(item['definition_id'] == target and item['visibility'] == 'private'
            and item['mathlib_rev'] == ENV, 'Definition ID/privacy/environment differs')
    for key in ['definition_name', 'definition_title', 'definition', 'natural_language_statement', 'source']:
        require(item[key] == row['payload'][key], 'Exact Definition readback differs: ' + key)
    return item


def poll(api, directory, row, job_id, timeout_seconds):
    deadline = time.monotonic() + timeout_seconds
    while True:
        job = api.request('/publish-jobs/' + urllib.parse.quote(job_id, safe=''))
        save(directory / (row['tag'] + '-result.json'), job)
        require(job['id'] == job_id, 'Wrong original job returned')
        check_job(job, row)
        if job['status'] not in {'PENDING', 'COMPILING'}:
            require(job['status'] == 'PUBLISHED', 'Original job stopped: ' + str(job))
            return job
        require(time.monotonic() < deadline, 'Wait limit reached; resume this original job, do not resubmit')
        time.sleep(min(5, max(0, deadline - time.monotonic())))


def deliver(packet_path, ready_path, directory, timeout_seconds=900):
    packet = preflight(packet_path, ready_path)
    directory = Path(directory)
    require(directory.resolve() == (UNIT / 'delivery-journal').resolve(),
            'Reuse this unit\'s single durable delivery-journal; alternate journals are forbidden')
    directory.mkdir(parents=True, exist_ok=True)
    # An exclusive local invocation lock prevents two callers using the same journal.
    lock = directory / 'delivery.lock'
    import fcntl
    with lock.open('a') as handle:
        fcntl.flock(handle.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
        api = load_api()
        check_scope(api, directory)
        before = directory / 'root-graph-before.json'
        current_graph = api.request('/theorems/' + ROOT + '/graph')
        if before.exists():
            require(read(before) == current_graph, 'Root graph changed since delivery began')
        else:
            save(before, current_graph)
        ids_path = directory / 'published-ids.json'
        ids = read(ids_path) if ids_path.exists() else {}
        require(set(ids) <= set(NAMES), 'Unexpected published IDs in journal')
        # Never create a second journal for the same packet: use this directory on every retry.
        binding = directory / 'packet-binding.json'
        identity = {'packet_sha256': sha(packet_path), 'mission_id': MISSION, 'names': NAMES}
        if binding.exists():
            require(read(binding) == identity, 'Journal belongs to a different packet')
        else:
            save(binding, identity)
        for row in packet['publications']:
            preflight(packet_path, ready_path)
            tag = row['tag']
            intent, submitted = directory / (tag + '-intent.json'), directory / (tag + '-submit.json')
            if intent.exists():
                require(read(intent) == row, 'Changed durable POST intent')
                require(submitted.exists(), 'Unknown POST outcome: run reconcile; do not submit again')
            else:
                require(not submitted.exists(), 'Submit receipt has no intent')
                save(intent, row)  # Durable intent exists BEFORE the only publication POST.
                response = api.request('/submit-definition', row['payload'], 'POST')
                save(submitted, response)  # Persist original job_id before polling.
            response = read(submitted)
            require(bool(response.get('job_id')) and not response.get('errors'), 'Invalid original POST receipt')
            job = poll(api, directory, row, response['job_id'], timeout_seconds)
            target = job['theorem_id']
            if tag in ids:
                require(ids[tag] == target, 'Published ID changed')
            ids[tag] = target
            save(ids_path, ids)  # Preserve the ID even if subsequent GET fails.
            check_definition(api, directory, row, target)
        after = api.request('/theorems/' + ROOT + '/graph')
        save(directory / 'root-graph-after.json', after)
        require(read(before) == after, 'Unexpected root graph change')
        summary = {'published_ids': ids, 'definition_count': 4, 'verification_jobs': 0,
                   'mission_id': MISSION, 'root_id': ROOT, 'environment': ENV, 'visibility': 'private',
                   'scope': SCOPE, 'root_graph_membership': False, 'canonicalC22Connected': False,
                   'root_graph_unchanged': True}
        save(directory / 'delivery-summary.json', summary)
        return summary


def reconcile(packet_path, ready_path, directory, name, job_id):
    """Read a nominated original job and attach only an exact matching receipt.

    Discover the job through GET /publish-jobs?kind=definition, with pagination.
    No search failure authorizes another POST. This function never submits.
    """
    packet = preflight(packet_path, ready_path)
    require(name in NAMES, 'Not one of the four Definitions')
    row = next(r for r in packet['publications'] if r['tag'] == name)
    directory = Path(directory)
    require(directory.resolve() == (UNIT / 'delivery-journal').resolve(),
            'Reconciliation must use the original unit delivery-journal')
    require(read(directory / (name + '-intent.json')) == row, 'Missing/mismatched original POST intent')
    api = load_api()
    check_scope(api, directory)
    job = api.request('/publish-jobs/' + urllib.parse.quote(job_id, safe=''))
    save(directory / (name + '-reconcile-readback.json'), job)
    require(job['id'] == job_id, 'Wrong nominated original job')
    check_job(job, row)
    require(job['status'] == 'PUBLISHED',
            'Wait for original job to publish; environment can only be verified on the exact Definition GET')
    check_definition(api, directory, row, job['theorem_id'])
    receipt = directory / (name + '-submit.json')
    if receipt.exists():
        require(read(receipt)['job_id'] == job_id, 'A different original job is already recorded')
    else:
        save(receipt, {'job_id': job_id, 'definition_name': name, 'status': 'PUBLISHED',
                       'reconciled_exact_readback': True})
    ids_path = directory / 'published-ids.json'
    ids = read(ids_path) if ids_path.exists() else {}
    require(name not in ids or ids[name] == job['theorem_id'], 'Published ID changed')
    ids[name] = job['theorem_id']
    save(ids_path, ids)
    return {'job_id': job_id, 'definition_id': job['theorem_id'], 'exact_reconciliation': True}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest='command', required=True)
    p = commands.add_parser('prepare')
    p.add_argument('--wrapper-report', required=True)
    p.add_argument('--blind-readbacks', required=True)
    p.add_argument('--paper-context', default=str(UNIT / 'paper-context.json'))
    p.add_argument('--source-ledger', required=True)
    p.add_argument('--out', required=True)
    for command in ['check', 'deliver', 'reconcile']:
        p = commands.add_parser(command)
        p.add_argument('--packet', required=True)
        p.add_argument('--ready', required=True)
        if command != 'check':
            p.add_argument('--journal', required=True)
        if command == 'deliver':
            p.add_argument('--wait-seconds', type=int, default=900)
        if command == 'reconcile':
            p.add_argument('--name', choices=NAMES, required=True)
            p.add_argument('--job-id', required=True)
    args = parser.parse_args()
    if args.command == 'prepare':
        result = prepare(args.wrapper_report, args.blind_readbacks, args.paper_context,
                         args.source_ledger, args.out)
        print(json.dumps({'offline': True, 'definitions': len(result['publications'])}))
    elif args.command == 'check':
        preflight(args.packet, args.ready)
        print(json.dumps({'offline': True, 'passed': True}))
    elif args.command == 'reconcile':
        print(json.dumps(reconcile(args.packet, args.ready, args.journal, args.name, args.job_id)))
    else:
        require(args.wait_seconds > 0, 'Wait duration must be positive')
        print(json.dumps(deliver(args.packet, args.ready, args.journal, args.wait_seconds)))


if __name__ == '__main__':
    main()
