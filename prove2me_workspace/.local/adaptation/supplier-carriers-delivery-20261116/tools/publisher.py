"""Three Definition bundles only. Import/prepare/check are offline.
Only explicit deliver(api, ...) and reconcile(api, ...) calls use the supplied API.
This file never loads credentials, compiles, invokes Git, or edits the workspace.
"""
from pathlib import Path
import ast
import hashlib
import importlib.util
import json
import os
import time
import urllib.parse

W = Path('/home/admin-wsl/Coq/abc/prove2me_workspace')
A = W / '.local/adaptation'
OUT = Path('/tmp/p2m-small-supplier-publisher-20261116')
ENV = '0df444a360eaa60ab8c11dca51a86af692955474'
ROOT = 'e33ff731-60a7-43ef-87ae-c12aeba23cb5'
MISSION = 'eeb5193f-68c0-41d0-9263-4a5ff7c801ee'
CREATOR = '89966734-f388-427a-9ea1-983923ff28a1'
READBACKS = Path('/tmp/p2m-iut-supplier-trilingual-20261116/trilingual.json')
PROTOCOL = A / 'reference-volume-tate-carriers-20261115/delivery.py'
PRIOR = A / 'prime-selection-reference-split-20261115/platform/final-AbcAdaptation_Reference_Iut_Implication_PrimeSelection.json'
GATES = {'new_leaf_modules', 'checks_axioms', 'source_kernel_identity', 'import_audit',
         'act1scene1', 'axiom_audit', 'independent_readbacks', 'paper_context',
         'source_ledger_consumers', 'git_diff_check', 'existing_mission_scope'}
BUNDLES = [
 {'name': 'AbcAdaptation_Reference_Genl_GeneralPosition_HeightTheory',
  'declarations': ['AbcAdaptation.Reference.Genl.HeightTheory'],
  'title': 'Abstract height theory with fifteen fields — 十五字段抽象高度理论 — 十五フィールドの抽象高さ理論',
  'metadata': A / 'genl-height-supplier-20261116/generated/genl-height-theory-metadata.json',
  'source': 'https://github.com/lana-agents/genl/blob/ea2846c877d1e16d8f0b911a5fed07f5ee69eaaf/Genl/GeneralPosition/HeightTheory.lean#L51-L95'},
 {'name': 'AbcAdaptation_Reference_Iut_Implication_PrimeSelection_HeightParts',
  'declarations': ['AbcAdaptation.Reference.Iut.LocalHeightData.heightEq', 'AbcAdaptation.Reference.Iut.LocalHeightData.heightOther'],
  'title': 'Two parts of the local height sum — 局部高度和的两部分 — 局所高さの和の二つの部分',
  'metadata': A / 'genl-height-supplier-20261116/generated/height-parts-metadata.json',
  'source': 'https://github.com/lana-agents/iut/blob/07cb1da58f6d428a670dbb5dd6093d428bcbcdd8/Iut/Implication/PrimeSelection.lean#L170-L179'},
 {'name': 'AbcAdaptation_Reference_Iut_Implication_Corollary22_NumericInputs',
  'declarations': ['AbcAdaptation.Reference.Iut.epsilonE', 'AbcAdaptation.Reference.Iut.deltaBound'],
  'title': 'Tolerance and degree-bound functions — 容差与次数界函数 — 許容誤差と次数上限の関数',
  'metadata': A / 'main-chain-native-minimal-20261116/source-draft/generated/numeric-metadata.json',
  'source': 'https://github.com/lana-agents/iut/blob/07cb1da58f6d428a670dbb5dd6093d428bcbcdd8/Iut/Implication/Corollary22.lean#L109-L276'}]


def require(ok, message):
    if not ok:
        raise ValueError(message)


def read(path):
    return json.loads(Path(path).read_text())


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


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


def _under_tmp(path):
    p = Path(path).resolve()
    require(p == OUT or OUT in p.parents, 'Output must stay in this task /tmp directory')
    return p


def _formal_readbacks():
    data = read(READBACKS)
    rows = {r['name']: r for r in data['declarations']}
    required = {n for b in BUNDLES for n in b['declarations']}
    require(len(required) == 5 and required <= set(rows), 'Missing one of five formal readbacks')
    frozen = {}
    for original in data['frozen_english_inputs']:
        require(sha(original['path']) == original['sha256'], 'Frozen English original changed')
        ds = read(original['path'])['declarations']
        frozen.update(ds if isinstance(ds, dict) else {r['name']: r['readback'] for r in ds})
    for name in required:
        r = rows[name]
        require(r['readbacks']['en'] == frozen[name], 'Frozen English changed: ' + name)
        require(hashlib.sha256(r['readbacks']['en'].encode()).hexdigest() == r['english_text_sha256'],
                'Frozen English hash differs: ' + name)
        require(all(isinstance(r['readbacks'][k], str) and r['readbacks'][k].strip()
                    for k in ['en', 'zh-Hans', 'ja']), 'Incomplete language row')
    return {n: rows[n] for n in required}


def _bundle_readback(bundle, rows):
    return '\n\n'.join('**' + label + '**\n\n' + '\n\n'.join(
        '`' + n + '`\n\n' + rows[n]['readbacks'][lang] for n in bundle['declarations'])
        for lang, label in [('en', 'English'), ('zh-Hans', '简体中文'), ('ja', '日本語')])


def _native_parts(bundle, code, revision_record=None):
    """Split only at a previously recorded source-AST output command boundary."""
    m = read(bundle['metadata'])
    expected = (m.get('source') or m.get('file'))['sha256']
    live_sha = hashlib.sha256(code).hexdigest()
    revision_commands = None
    if live_sha != expected:
        require(revision_record is not None, 'Changed native source needs explicit original-AST-preserving revision provenance')
        spec = importlib.util.spec_from_file_location('small_supplier_revision', Path(__file__).with_name('revision_provenance.py'))
        revision = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(revision)
        revision_commands = revision.verify(revision_record,
            W / ('Definitions/Def_' + bundle['name'] + '.lean'), bundle['metadata'])
    else:
        require(revision_record is None, 'Baseline file must not pretend to have applied a revision')
    maps = m['commandMaps']
    if bundle['name'].endswith('_HeightParts'):
        ranges = [r['completeCommandRange'] for r in m['records']]
        selected = [c for c in maps if c['originalRange'] in ranges]
    else:
        selected = [c for c in maps if c.get('declaration') is True]
    require(bool(selected), 'No AST-selected original definition commands')
    first = min(c['outputStart'] for c in selected)
    baseline_first = first
    if revision_commands is not None:
        mapped = [c for c in revision_commands if c['baselineOutputRange'][0] == first]
        require(len(mapped) == 1, 'Original first command mapping is not unique')
        first = mapped[0]['finalOutputRange'][0]
    require(0 < first < len(code), 'Invalid source-AST output boundary')
    return {'preamble': code[:first].decode(), 'formal_definition': code[first:].decode(),
            'boundary_utf8_offset': first, 'source_ast_metadata': str(bundle['metadata']),
            'source_ast_metadata_sha256': sha(bundle['metadata']),
            'original_baseline_boundary_utf8_offset': baseline_first,
            'explicit_revision': revision_record,
            'schema_note': 'Offline decomposition only: API definition = preamble + formal_definition. No theorem formal_statement/preamble fields are sent.'}


def prepare(output=OUT / 'preview', paper_context=None, revision_records=None):
    """Create exact local payloads. Without final paper context they are preview-only."""
    output = _under_tmp(output)
    rows = _formal_readbacks()
    revisions = read(revision_records) if revision_records else {}
    paper = read(paper_context) if paper_context else None
    if paper is not None:
        require(paper['passed'] is True, 'Paper context not accepted')
        contexts = {r['definition_name']: r for r in paper['bundles']}
        require(set(contexts) == {b['name'] for b in BUNDLES}, 'Paper bundle set differs')
    else:
        contexts = {}
    prior = read(PRIOR)
    prior_path = W / ('Definitions/Def_' + prior['definition_name'] + '.lean')
    require(prior['definition_id'] == 'ca8c8d06-ce2b-4683-8de7-662afa4a0138'
            and prior['visibility'] == 'private' and prior['mathlib_rev'] == ENV
            and prior['deprecated_at'] is None, 'Saved prior Definition scope differs')
    require(prior['definition'].encode() == prior_path.read_bytes(), 'Uploaded prior dependency bytes differ')
    publications, decompositions, sources = [], [], {}
    metadata = {str(READBACKS): sha(READBACKS), str(PRIOR): sha(PRIOR)}
    for b in BUNDLES:
        relative = 'Definitions/Def_' + b['name'] + '.lean'
        path = W / relative
        raw = path.read_bytes()
        code = raw.decode()
        require('Copyright (c) 2026 ' in code and 'Released under Apache 2.0 license' in code,
                'Original source notice missing')
        require('sorry' not in code.split(), 'Definition has a placeholder')
        imports = [m for l in code.splitlines() if l.startswith('import ') for m in l.split()[1:]]
        project = [m for m in imports if m.startswith('Definitions.')]
        expected_project = ['Definitions.Def_' + prior['definition_name']] if b['name'].endswith('_HeightParts') else []
        require(project == expected_project, 'Unexpected project import closure')
        parts = _native_parts(b, raw, revisions.get(b['name']))
        require((parts['preamble'] + parts['formal_definition']).encode() == raw, 'Code decomposition is lossy')
        decompositions.append(dict(definition_name=b['name'], **parts))
        natural = '**Formal-code readback**\n\n' + _bundle_readback(b, rows)
        revision = revisions.get(b['name'])
        if revision and revision.get('equationSource') is not None:
            supplement = read(OUT / 'helper-readback-supplement.json')
            require(supplement['declaration'] == 'AbcAdaptation.Reference.Iut.epsilonE.eq_1', 'Wrong equation supplement')
            natural += '\n\n**Defining-equation helper supplement (separate from frozen original readbacks)**\n\n'
            natural += '\n\n'.join('**' + label + '**\n\n' + supplement['readbacks'][lang]
                for lang, label in [('en', 'English'), ('zh-Hans', '简体中文'), ('ja', '日本語')])
            metadata[str(OUT / 'helper-readback-supplement.json')] = sha(OUT / 'helper-readback-supplement.json')
        if paper is not None:
            p = contexts[b['name']]
            require(p['source'] == b['source'] and p['publication_markdown'].strip(), 'Paper source binding differs')
            natural += '\n\n**Paper source context (English; separate from formal-code readback)**\n\n' + p['publication_markdown']
        payload = {'definition_name': b['name'], 'definition_title': b['title'], 'definition': code,
                   'natural_language_statement': natural, 'source': b['source'], 'env': ENV, 'private': True}
        publications.append({'tag': b['name'], 'endpoint': '/submit-definition', 'payload': payload})
        sources[relative] = sha(path)
        metadata[str(b['metadata'])] = sha(b['metadata'])
        save(output / 'payloads' / (b['name'] + '.json'), payload)
    if paper is not None:
        metadata[str(Path(paper_context).resolve())] = sha(paper_context)
        if paper.get('sourcePaperArtifact'):
            original = paper['sourcePaperArtifact']
            require(sha(original['path']) == original['sha256'], 'Original English paper artifact changed')
            metadata[original['path']] = original['sha256']
    if revision_records is not None:
        metadata[str(Path(revision_records).resolve())] = sha(revision_records)
        for record in revisions.values():
            metadata[record['baseline']['path']] = record['baseline']['sha256']
            original = record['originalSourceAstMetadata']
            metadata[original['path']] = original['sha256']
            if record['equationSource']:
                e = record['equationSource']
                metadata[e['sourceExprFile']] = e['sourceExprSha256']
                metadata[e['sourceExportReceipt']] = e['sourceExportReceiptSha256']
    packet = {'schema': 'small-suppliers-private-definition-packet/v1', 'workspace': str(W),
              'mission_id': MISSION, 'root_id': ROOT, 'environment': ENV, 'visibility': 'private',
              'publication_ready': paper is not None, 'source_sha256': sources, 'metadata_sha256': metadata,
              'publications': publications, 'verification': [], 'post_limit': 3,
              'readbacks': rows, 'excluded_declarations': ['AbcAdaptation.Reference.Iut.Corollary312VariantData.one_le_dmod'],
              'explicit_revision_records': revisions,
              'prior_dependency': {'module': 'Definitions.Def_' + prior['definition_name'],
                  'definition_id': prior['definition_id'], 'definition_name': prior['definition_name'],
                  'source_sha256': sha(prior_path), 'saved_item': str(PRIOR)},
              'root_graph_membership': False}
    save(output / 'packet.json', packet)
    save(output / 'code-decomposition.json', decompositions)
    return packet


def check(packet_path, ready_path):
    """Offline checks; a source export alone never authorizes publication."""
    packet, ready = read(packet_path), read(ready_path)
    require(packet['publication_ready'] is True, 'Final paper context has not been bound')
    require(ready['passed'] is True and ready['packet_sha256'] == sha(packet_path), 'Root acceptance not bound')
    require(set(ready['gates']) == GATES and all(v is True for v in ready['gates'].values()), 'Root delivery gates pending')
    require(packet['workspace'] == str(W) and packet['mission_id'] == MISSION
            and packet['root_id'] == ROOT and packet['environment'] == ENV
            and packet['visibility'] == 'private' and packet['verification'] == []
            and packet['post_limit'] == 3, 'Publication scope changed')
    for p, h in packet['metadata_sha256'].items():
        require(sha(p) == h, 'Metadata changed: ' + p)
    for p, h in packet['source_sha256'].items():
        require(sha(W / p) == h, 'Native source changed: ' + p)
    for p, h in ready['evidence_sha256'].items():
        require(sha(p) == h, 'Acceptance evidence changed: ' + p)
    require(set(r['tag'] for r in packet['publications']) == {b['name'] for b in BUNDLES}, 'Bundle set changed')
    for row in packet['publications']:
        p = row['payload']
        require(row['endpoint'] == '/submit-definition' and p['definition_name'] == row['tag']
                and p['private'] is True and p['env'] == ENV,
                'Wrong API payload scope')
        require(p['definition'] == (W / ('Definitions/Def_' + row['tag'] + '.lean')).read_text(), 'Payload code changed')
        for b in BUNDLES:
            if b['name'] == row['tag']:
                require(p['source'] == b['source'] and p['definition_title'] == b['title'], 'Payload source/title changed')
                for n in b['declarations']:
                    require(all(t in p['natural_language_statement'] for t in packet['readbacks'][n]['readbacks'].values()),
                            'Formal readback string missing')
    identity = read(ready['source_kernel_identity']['result'])
    receipt_path = ready['source_kernel_identity']['receipt']
    receipt = read(receipt_path)
    require(ready['source_kernel_identity']['result'] in ready['evidence_sha256']
            and receipt_path in ready['evidence_sha256'], 'Identity result/receipt not hashed')
    require(identity['schema'] == 'small-supplier-kernel-identity-result/v1'
            and identity['rootCount'] == 5 and identity['comparedRecordCount'] == 38
            and len(identity['comparisons']) == 38 and identity['hasSorryAx'] is False
            and identity['unresolvedTargetNames'] == [] and identity['compatibilitySubstitutions'] == [],
            'Five-root/full-structure source kernel identity not accepted')
    require({n for b in BUNDLES for n in b['declarations']} <= {r['target'] for r in identity['comparisons']},
            'One of five selected roots is missing from identity comparison')
    require(all(r['kernelTypeEqual'] is True and r['computationShapeEqual'] is True
                and r['sourceTargetSignatureBinderInfoPlacementEqual'] is True for r in identity['comparisons']),
            'Source kernel comparison incomplete')
    require(receipt['status'] == 'succeeded' and receipt['result']['exit_code'] == 0, 'Identity CI not accepted')
    require(receipt['request']['workspace'] == str(W) and receipt['request']['exclusive'] is True
            and receipt['result']['snapshot']['workspace_mode'] == 'exclusive_worktree'
            and receipt['result']['snapshot']['snapshot_id'] is None, 'Identity CI input mode differs')
    bound = receipt['request']['worktree_manifest'].get('input_hashes', {})
    require(all(bound.get(str(W / p)) == h for p, h in packet['source_sha256'].items()), 'Identity does not bind exact three native files')
    require(ready['axiom_audit']['sorryAx_found'] is False and ready['axiom_audit']['unexpected_axioms'] == [], 'Axiom acceptance pending')
    return packet


def _protocol():
    """Reuse existing exact-readback network functions; do not execute module top level."""
    names = {'check_scope', 'check_job', 'check_definition', 'poll'}
    functions = [n for n in ast.parse(PROTOCOL.read_text()).body if isinstance(n, ast.FunctionDef) and n.name in names]
    require({f.name for f in functions} == names, 'Existing delivery protocol changed')
    ns = dict(Path=Path, read=read, save=save, require=require, ENV=ENV, MISSION=MISSION,
              ROOT=ROOT, CREATOR=CREATOR, time=time, urllib=urllib)
    exec(compile(ast.Module(body=functions, type_ignores=[]), '<existing-definition-network-protocol>', 'exec'), ns)
    return ns


def _prior_readback(api, packet, directory):
    d = packet['prior_dependency']
    item = api.request('/definitions/' + urllib.parse.quote(d['definition_id'], safe=''))
    save(directory / 'prior-PrimeSelection-readback.json', item)
    require(item['definition_name'] == d['definition_name'] and item['visibility'] == 'private'
            and item['mathlib_rev'] == ENV and item['deprecated_at'] is None, 'Remote prior dependency changed')
    require(hashlib.sha256(item['definition'].encode()).hexdigest() == d['source_sha256'], 'Remote imported namespace/code differs')


def deliver(api, packet_path, ready_path, directory, timeout_seconds=900):
    """Explicit root-only publication after check(). Never called by import or prepare."""
    packet = check(packet_path, ready_path)
    directory = Path(directory)
    directory.mkdir(parents=True, exist_ok=True)
    protocol = _protocol()
    protocol['check_scope'](api, directory)
    _prior_readback(api, packet, directory)
    before = api.request('/theorems/' + ROOT + '/graph')
    baseline = directory / 'root-graph-before.json'
    if baseline.exists():
        require(read(baseline) == before, 'Root graph changed since original delivery began')
    else:
        save(baseline, before)
    identity = {'packet_sha256': sha(packet_path), 'names': [b['name'] for b in BUNDLES]}
    binding = directory / 'packet-binding.json'
    if binding.exists():
        require(read(binding) == identity, 'Journal belongs to another packet')
    else:
        save(binding, identity)
    ids_path = directory / 'published-ids.json'
    ids = read(ids_path) if ids_path.exists() else {}
    for row in packet['publications']:
        check(packet_path, ready_path)
        tag = row['tag']
        intent, submitted = directory / (tag + '-intent.json'), directory / (tag + '-submit.json')
        if intent.exists():
            require(read(intent) == row and submitted.exists(), 'Unknown POST outcome: reconcile original job; do not resubmit')
        else:
            require(not submitted.exists(), 'POST receipt lacks original intent')
            save(intent, row)
            save(submitted, api.request('/submit-definition', row['payload'], 'POST'))
        posted = read(submitted)
        require(posted.get('job_id') and not posted.get('errors'), 'Invalid original POST receipt')
        job = protocol['poll'](api, directory, row, posted['job_id'], timeout_seconds)
        require(job['theorem_id'] == ids.get(tag, job['theorem_id']), 'Published ID changed')
        ids[tag] = job['theorem_id']
        save(ids_path, ids)
        protocol['check_definition'](api, directory, row, job['theorem_id'])
    after = api.request('/theorems/' + ROOT + '/graph')
    save(directory / 'root-graph-after.json', after)
    require(before == after, 'Definitions publication changed root graph')
    return ids


def reconcile(api, packet_path, ready_path, directory, name, job_id):
    """Read nominated original job only, preserving exact code/metadata readback."""
    packet = check(packet_path, ready_path)
    row = next(r for r in packet['publications'] if r['tag'] == name)
    directory = Path(directory)
    require(read(directory / (name + '-intent.json')) == row, 'Original intent differs')
    protocol = _protocol()
    protocol['check_scope'](api, directory)
    job = api.request('/publish-jobs/' + urllib.parse.quote(job_id, safe=''))
    save(directory / (name + '-reconcile-readback.json'), job)
    protocol['check_job'](job, row)
    require(job['id'] == job_id and job['status'] == 'PUBLISHED', 'Original job has not published')
    protocol['check_definition'](api, directory, row, job['theorem_id'])
    target = directory / (name + '-submit.json')
    if target.exists():
        require(read(target)['job_id'] == job_id, 'Different original job already saved')
    else:
        save(target, {'job_id': job_id, 'definition_name': name, 'reconciled_exact_readback': True})
    return job['theorem_id']
