"""Independent fourth supplier Definition; offline until explicit deliver(api,...).
This does not publish Corollary22Inputs, ThetaDataExistence, threshold, or one_le_dmod.
"""
from pathlib import Path
import importlib.util
import hashlib
import json

HERE = Path(__file__).resolve().parent
_spec = importlib.util.spec_from_file_location('small_supplier_shared_protocol', HERE / 'publisher.py')
base = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(base)  # Only definitions/constants; no credentials or API.
NAME = 'AbcAdaptation_Reference_Genl_Mathlib_Order_BoundedDiscrepancy'
DECLS = ['AbcAdaptation.Reference.DiscrepancyLE', 'AbcAdaptation.Reference.DiscrepancyEquiv']
SOURCE = base.W / ('Definitions/Def_' + NAME + '.lean')
UNIT = base.A / 'discrepancy-supplier-20261116'
METADATA = UNIT / 'candidate-handoff/discrepancy-metadata.json'
TRILINGUAL = Path('/tmp/p2m-c2-discrepancy-trilingual-v1-20261116/trilingual.json')
PAPER = HERE / 'paper-context.adapter-discrepancy.json'
TITLE = 'Bounded discrepancy relations — 有界差异关系 — 有界差の関係'


def _english_object(row):
    """Render every original English field without rewriting its strings."""
    parts = []
    for key, value in row.items():
        if key == 'name':
            continue
        text = value if isinstance(value, str) else json.dumps(value, ensure_ascii=False, indent=2)
        parts.append('**' + key.replace('_', ' ') + '**\n\n' + text)
    return '\n\n'.join(parts)


def prepare(output=HERE / 'discrepancy-preview', revision_record=None):
    output = base._under_tmp(output)
    translation = base.read(TRILINGUAL)
    frozen = translation['frozen_english']
    base.require(base.sha(frozen['source_path']) == frozen['source_sha256']
                 == base.sha(frozen['byte_exact_copy']), 'Frozen independent English changed')
    original = base.read(frozen['source_path'])
    originals = original['declarations']
    originals = {r['name']: r for r in originals} if isinstance(originals, list) else originals
    selected = {r['name']: r for r in translation['declarations'] if r['name'] in DECLS}
    base.require(set(selected) == set(DECLS), 'Missing two discrepancy readbacks')
    for name, row in selected.items():
        base.require(row['original_en'] == originals[name], 'Frozen English object changed')
        digest = hashlib.sha256(json.dumps(row['original_en'], ensure_ascii=False, sort_keys=True, separators=(',', ':')).encode()).hexdigest()
        base.require(digest == row['original_en_object_sha256_canonical_json'], 'English object hash differs')
        base.require(set(row['readbacks']) == {'zh-Hans', 'ja'}, 'Translation schema differs')
    raw = SOURCE.read_bytes()
    metadata = base.read(METADATA)
    record = base.read(revision_record) if revision_record else None
    if base.sha(SOURCE) != metadata['source']['sha256']:
        base.require(record is not None, 'Changed discrepancy bytes need explicit revision provenance')
        spec = importlib.util.spec_from_file_location('discrepancy_revision', HERE / 'revision_provenance.py')
        revision = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(revision)
        command_map = revision.verify(record, SOURCE, METADATA)
    else:
        base.require(record is None, 'Unchanged source must not claim an applied revision')
        command_map = None
    imports = [w for l in raw.decode().splitlines() if l.startswith('import ') for w in l.split()[1:]]
    base.require(all(n.startswith('Mathlib.') for n in imports), 'Discrepancy adds a project dependency')
    base.require(b'Copyright (c) 2026 Christian Merten.' in raw and b'Apache 2.0 license' in raw, 'Original notice missing')
    first = min(c['outputStart'] for c in metadata['commandMaps'] if c['role'] == 'definition')
    if command_map:
        first = next(c['finalOutputRange'][0] for c in command_map if c['baselineOutputRange'][0] == first)
    natural = '**Formal-code readback**\n\n' + '\n\n'.join('**' + label + '**\n\n' + '\n\n'.join(
        '`' + n + '`\n\n' + (_english_object(selected[n]['original_en']) if lang == 'en' else selected[n]['readbacks'][lang])
        for n in DECLS) for lang, label in [('en', 'English'), ('zh-Hans', '简体中文'), ('ja', '日本語')])
    paper = base.read(PAPER)
    original_paper = paper['sourcePaperArtifact']
    base.require(paper['passed'] is True and base.sha(original_paper['path']) == original_paper['sha256'], 'Paper evidence changed')
    context, = paper['bundles']
    base.require(context['definition_name'] == NAME, 'Wrong paper-context bundle')
    natural += '\n\n**Paper source context (English; separate from formal-code readback)**\n\n' + context['publication_markdown']
    payload = {'definition_name': NAME, 'definition_title': TITLE, 'definition': raw.decode(),
               'natural_language_statement': natural, 'source': context['source'], 'env': base.ENV, 'private': True}
    metadata_hashes = {str(p): base.sha(p) for p in [TRILINGUAL, METADATA, PAPER, Path(frozen['source_path']), Path(original_paper['path'])]}
    if revision_record:
        metadata_hashes[str(Path(revision_record).resolve())] = base.sha(revision_record)
        metadata_hashes[record['baseline']['path']] = record['baseline']['sha256']
    packet = {'schema': 'discrepancy-private-definition-packet/v1', 'workspace': str(base.W),
        'environment': base.ENV, 'visibility': 'private', 'publication_ready': True,
        'publications': [{'tag': NAME, 'endpoint': '/submit-definition', 'payload': payload}],
        'source_sha256': {'Definitions/Def_' + NAME + '.lean': base.sha(SOURCE)},
        'metadata_sha256': metadata_hashes, 'readbacks': selected, 'explicit_revision': record,
        'verification': [], 'post_limit': 1, 'root_graph_membership': False,
        'excluded': ['Iut.Corollary22Inputs', 'Iut.ThetaDataExistence', 'Iut.Corollary22Inputs.threshold', 'one_le_dmod']}
    base.save(output / 'packet.json', packet)
    base.save(output / 'payload.json', payload)
    base.save(output / 'code-decomposition.json', {'preamble': raw[:first].decode(), 'formal_definition': raw[first:].decode(),
        'first_definition_utf8_offset': first, 'originalMetadata': {'path': str(METADATA), 'sha256': base.sha(METADATA)},
        'revision': record, 'notationCommandsRetained': 2})
    return packet


def check(packet_path, ready_path):
    packet, ready = base.read(packet_path), base.read(ready_path)
    base.require(ready['passed'] is True and ready['packet_sha256'] == base.sha(packet_path), 'Root acceptance pending')
    base.require(set(ready['gates']) == base.GATES and all(v is True for v in ready['gates'].values()), 'Root delivery gates pending')
    base.require(packet['schema'] == 'discrepancy-private-definition-packet/v1'
        and packet['workspace'] == str(base.W) and packet['environment'] == base.ENV
        and packet['visibility'] == 'private' and packet['post_limit'] == 1 and packet['verification'] == [], 'Scope changed')
    for p, digest in packet['metadata_sha256'].items():
        base.require(base.sha(p) == digest, 'Metadata changed: ' + p)
    for p, digest in ready['evidence_sha256'].items():
        base.require(base.sha(p) == digest, 'Acceptance evidence changed: ' + p)
    base.require(packet['source_sha256'] == {'Definitions/Def_' + NAME + '.lean': base.sha(SOURCE)}, 'Native source changed')
    row, = packet['publications']
    base.require(row['tag'] == NAME and row['endpoint'] == '/submit-definition'
                 and row['payload']['definition_name'] == NAME and row['payload']['private'] is True
                 and row['payload']['env'] == base.ENV and row['payload']['definition'].encode() == SOURCE.read_bytes(), 'Payload changed')
    binding = ready['source_kernel_identity']
    identity, receipt = base.read(binding['result']), base.read(binding['receipt'])
    base.require(all(p in ready['evidence_sha256'] for p in binding.values()), 'Kernel evidence not hashed')
    base.require(identity['schema'] == 'package-kernel-identity-result/v1' and identity['rootCount'] == 2
                 and identity['comparedRecordCount'] == len(identity['comparisons']) == 2
                 and identity['hasSorryAx'] is False and identity['unresolvedTargetNames'] == []
                 and identity['compatibilitySubstitutions'] == [], 'Actual two-root kernel identity missing')
    base.require({r['target'] for r in identity['comparisons']} == set(DECLS)
                 and all(r['kernelTypeEqual'] is True and r['kernelValueEqual'] is True
                 and r['sourceTargetSignatureBinderInfoPlacementEqual'] is True for r in identity['comparisons']), 'Two exact definitions not compared')
    base.require(receipt['status'] == 'succeeded' and receipt['result']['exit_code'] == 0
                 and receipt['request']['workspace'] == str(base.W), 'Actual kernel receipt did not pass')
    # The existing identity job binds export/config inputs, not native source text.
    # Root must bind a successful native artifact build of these exact source bytes.
    artifact_receipt = ready['native_artifact_receipt']
    base.require(artifact_receipt in ready['evidence_sha256'], 'Native artifact receipt not hashed')
    artifact = base.read(artifact_receipt)
    base.require(artifact['status'] == 'succeeded' and artifact['result']['exit_code'] == 0
                 and artifact['request']['workspace'] == str(base.W)
                 and artifact['request']['worktree_manifest']['source_sha256'] == base.sha(SOURCE), 'Native artifact source binding differs')
    base.require(ready['axiom_audit']['sorryAx_found'] is False and ready['axiom_audit']['unexpected_axioms'] == [], 'Axiom acceptance pending')
    return packet


def deliver(api, packet_path, ready_path, directory, timeout_seconds=900):
    packet = check(packet_path, ready_path)
    directory = Path(directory)
    directory.mkdir(parents=True, exist_ok=True)
    protocol = base._protocol()
    protocol['check_scope'](api, directory)
    row, = packet['publications']
    binding = directory / 'packet-binding.json'
    identity = {'packet_sha256': base.sha(packet_path), 'definition_name': NAME}
    if binding.exists():
        base.require(base.read(binding) == identity, 'Different publication journal')
    else:
        base.save(binding, identity)
    before = api.request('/theorems/' + base.ROOT + '/graph')
    before_path = directory / 'root-graph-before.json'
    if before_path.exists():
        base.require(base.read(before_path) == before, 'Root graph changed since original publication')
    else:
        base.save(before_path, before)
    intent, posted = directory / (NAME + '-intent.json'), directory / (NAME + '-submit.json')
    if intent.exists():
        base.require(base.read(intent) == row and posted.exists(), 'Unknown POST outcome; reconcile original job only')
    else:
        base.require(not posted.exists(), 'Receipt has no original intent')
        base.save(intent, row)
        base.save(posted, api.request('/submit-definition', row['payload'], 'POST'))
    response = base.read(posted)
    base.require(response.get('job_id') and not response.get('errors'), 'Invalid original publication receipt')
    job = protocol['poll'](api, directory, row, response['job_id'], timeout_seconds)
    protocol['check_definition'](api, directory, row, job['theorem_id'])
    after = api.request('/theorems/' + base.ROOT + '/graph')
    base.save(directory / 'root-graph-after.json', after)
    base.require(after == before, 'Definition publication changed root graph')
    base.save(directory / 'published-ids.json', {NAME: job['theorem_id']})
    return job['theorem_id']


def reconcile(api, packet_path, ready_path, directory, job_id):
    """Read one nominated original job; do not issue a publication POST."""
    packet = check(packet_path, ready_path)
    row, = packet['publications']
    directory = Path(directory)
    base.require(base.read(directory / (NAME + '-intent.json')) == row, 'Original intent differs')
    protocol = base._protocol()
    protocol['check_scope'](api, directory)
    job = api.request('/publish-jobs/' + base.urllib.parse.quote(job_id, safe=''))
    base.save(directory / (NAME + '-reconcile-readback.json'), job)
    protocol['check_job'](job, row)
    base.require(job['id'] == job_id and job['status'] == 'PUBLISHED', 'Original job has not published')
    protocol['check_definition'](api, directory, row, job['theorem_id'])
    target = directory / (NAME + '-submit.json')
    if target.exists():
        base.require(base.read(target)['job_id'] == job_id, 'Different original publication job')
    else:
        base.save(target, {'job_id': job_id, 'definition_name': NAME, 'reconciled_exact_readback': True})
    base.save(directory / 'published-ids.json', {NAME: job['theorem_id']})
    return job['theorem_id']
