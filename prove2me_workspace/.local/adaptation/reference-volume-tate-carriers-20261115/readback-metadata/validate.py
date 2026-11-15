#!/usr/bin/env python3
"""Read-only consistency validation; no compiler or platform operation."""
import hashlib
import json
from pathlib import Path

BASE = Path(__file__).resolve().parent
W = Path('/home/admin-wsl/Coq/abc/prove2me_workspace')

def read(path):
    return json.loads(Path(path).read_text(encoding='utf-8'))

def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

manifest = read(BASE / 'input-manifest.json')
validation = read(BASE / 'validation.json')
packet = read(BASE / 'blind-readbacks.json')
for entry in manifest['inputs']:
    assert sha(entry['path']) == entry['sha256'], entry['path']
for entry in manifest['original_artifacts']:
    assert sha(entry['path']) == entry['sha256'], entry['path']
    assert sha(entry['frozen_copy']) == entry['sha256'], entry['frozen_copy']
    assert {k: v for k, v in read(entry['path']).items() if k != 'bundles'} == entry['metadata_verbatim']
for entry in manifest['historical_original_artifacts']:
    assert sha(entry['path']) == sha(entry['frozen_copy']) == entry['sha256']
    assert sha(entry['integrated_copy']) == entry['integrated_copy_sha256'] == entry['sha256']
    historical, current = read(entry['path']), read(entry['superseding_final_artifact'])
    assert historical['bundles'] == current['bundles']
    assert {k: v for k, v in historical.items() if k != 'bundles'} == entry['metadata_verbatim']
for entry in manifest['original_recorded_inputs_checked']:
    assert sha(entry['recorded_input']['path']) == entry['recorded_input']['sha256'] == entry['actual_sha256']
for name, digest in validation['output_hashes'].items():
    assert sha(BASE / name) == digest, name
template = read(next(x['path'] for x in manifest['inputs'] if x['role'] == 'delivery_schema_template'))
previous = read(next(x['path'] for x in manifest['inputs'] if x['role'] == 'previous_accepted_schema'))
ledger = {x['producer']: x for x in read(next(x['path'] for x in manifest['inputs'] if x['role'] == 'final_source_ledger'))['entries']}
report = {x['definitionName']: x for x in read(next(x['path'] for x in manifest['inputs'] if x['role'] == 'wrapper_and_blind_input_hashes'))['bundles']}
assert set(template).issubset(packet) and set(previous).issubset(packet)
assert [x['definition_name'] for x in packet['bundles']] == [x['definition_name'] for x in template['bundles']]
assert len(packet['independent_reviews']) == 2
assert len({x['reviewer_id'] for x in packet['independent_reviews']}) == 2
for review in packet['independent_reviews']:
    assert set(template['independent_reviews'][0]).issubset(review)
    original = read(review['original_artifact'])
    assert sha(review['original_artifact']) == review['original_artifact_sha256']
    assert review['original_metadata_verbatim'] == {k: v for k, v in original.items() if k != 'bundles'}
    assert review['actual_model'] is original['actual_model'] is None
    assert review['author_model'] == original['author_model']
for bundle in packet['bundles']:
    name, provenance = bundle['definition_name'], bundle['provenance']
    original = read(provenance['original_artifact'])
    ob = original['bundles'][provenance['original_bundle_index']]
    assert bundle['source'] == ledger[name]['sourceURL']
    assert ledger[name]['originalModule'] == report[name]['module']
    assert provenance['effective_module_source_sha256'] == ledger[name]['sourceProvenance']['sourceSha256'] == report[name]['adaptationProvenance']['sourceSha256']
    assert provenance['upstream_module_source_sha256'] == ledger[name]['sourceProvenance']['upstreamSourceSha256']
    assert bundle['source_sha256'] == ledger[name]['wrappedSourceSha256'] == report[name]['sha256']
    assert sha(W / 'Definitions' / ('Def_' + name + '.lean')) == sha(report[name]['path']) == bundle['source_sha256']
    assert provenance['input_sha256'] == report[name]['blindReadback']['sha256'] == sha(report[name]['blindReadback']['path'])
    original_input = next(x for x in original['inputs'] if x['path'] == report[name]['blindReadback']['path'])
    assert provenance['input_sha256'] == original_input['sha256']
    assert sha(provenance['original_artifact']) == provenance['original_artifact_sha256']
    assert provenance['original_definition_name'] == ob['definition_name'] == name
    assert provenance['original_provenance_verbatim'] == original['provenance']
    assert provenance['actual_model'] is original['actual_model'] is None
    assert set(template['bundles'][0]).issubset(bundle)
    assert set(previous['bundles'][0]).issubset(bundle)
    assert set(template['bundles'][0]['provenance']).issubset(provenance)
    for key in ['en', 'zh-Hans', 'ja', 'declaration_coverage', 'possible_ambiguities']:
        assert bundle[key] == ob[key], (name, key)
    if 'proof_notes' in ob:
        assert bundle['proof_notes'] == ob['proof_notes']
    assert len(bundle['definition_title']) <= 200 and bundle['editorial_changes'] == []
assert len(packet['bundles']) == 5
assert all(validation[key] is False for key in [
    'new_independent_readback_performed', 'proof_acceptance_performed',
    'compilation_performed', 'ci_used', 'api_used', 'network_used', 'git_used', 'main_workspace_edited'])
print(json.dumps({'passed': True, 'bundles': 5, 'original_artifacts': 2,
                  'original_inputs_verified': len(manifest['original_recorded_inputs_checked']),
                  'all_readback_strings_and_disclosures_verbatim': True}, ensure_ascii=False))
