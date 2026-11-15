#!/usr/bin/env python3
"""Read-only validation of assembled metadata and recorded source inputs."""
import hashlib
import json
from pathlib import Path

base = Path(__file__).resolve().parent

def read(path):
    return json.loads(Path(path).read_text(encoding='utf-8'))

def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

manifest = read(base / 'input-manifest.json')
validation = read(base / 'validation.json')
packet = read(base / 'blind-readbacks.json')
for entry in manifest['inputs']:
    assert sha(entry['path']) == entry['sha256'], entry['path']
for entry in manifest['original_artifacts']:
    assert sha(entry['path']) == entry['sha256'], entry['path']
    assert sha(entry['frozen_copy']) == entry['sha256'], entry['frozen_copy']
    assert {k: v for k, v in read(entry['path']).items() if k != 'bundles'} == entry['metadata_verbatim']
for entry in manifest['original_recorded_inputs_checked']:
    assert sha(entry['recorded_input']['path']) == entry['recorded_input']['sha256'] == entry['actual_sha256']
for name, digest in validation['output_hashes'].items():
    assert sha(base / name) == digest, name
template = read(next(x['path'] for x in manifest['inputs'] if x['role'] == 'delivery_schema_template'))
previous = read(next(x['path'] for x in manifest['inputs'] if x['role'] == 'previous_accepted_schema'))
ledger = {x['producer']: x for x in read(next(x['path'] for x in manifest['inputs'] if x['role'] == 'canonical_names_source_urls_and_module_hashes'))['entries']}
report = {x['definitionName']: x for x in read(next(x['path'] for x in manifest['inputs'] if x['role'] == 'wrapper_and_blind_input_hashes'))['bundles']}
assert set(template).issubset(packet)
assert set(previous).issubset(packet)
assert [x['definition_name'] for x in packet['bundles']] == [x['definition_name'] for x in template['bundles']]
for bundle in packet['bundles']:
    name = bundle['definition_name']
    provenance = bundle['provenance']
    original = read(provenance['original_artifact'])
    original_bundle = original['bundles'][provenance['original_bundle_index']]
    assert bundle['source'] == ledger[name]['sourceURL']
    assert bundle['source_sha256'] == ledger[name]['wrappedSourceSha256'] == report[name]['sha256']
    assert provenance['input_sha256'] == report[name]['blindReadback']['sha256']
    assert sha(report[name]['blindReadback']['path']) == provenance['input_sha256']
    assert sha(provenance['original_artifact']) == provenance['original_artifact_sha256']
    assert provenance['original_definition_name'] == original_bundle['definition_name']
    assert set(template['bundles'][0]).issubset(bundle)
    assert set(previous['bundles'][0]).issubset(bundle)
    assert set(template['bundles'][0]['provenance']).issubset(provenance)
    for key in ['en', 'zh-Hans', 'ja', 'declaration_coverage', 'possible_ambiguities']:
        assert bundle[key] == original_bundle[key], (name, key)
    assert len(bundle['definition_title']) <= 200
    assert bundle['editorial_changes'] == []
assert len(packet['bundles']) == 5
assert all(validation[key] is False for key in [
    'new_independent_readback_performed', 'proof_acceptance_performed',
    'compilation_performed', 'ci_used', 'api_used', 'network_used', 'git_used', 'main_workspace_edited'])
print(json.dumps({'passed': True, 'bundles': 5, 'original_artifacts': 2,
                  'original_inputs_verified': len(manifest['original_recorded_inputs_checked']),
                  'all_readback_strings_verbatim': True}, ensure_ascii=False))
