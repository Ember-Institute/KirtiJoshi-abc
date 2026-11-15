#!/usr/bin/env python3
"""Read-only metadata validation; an optional separate map locates archive copies."""
import argparse
import hashlib
import json
from pathlib import Path

BASE = Path(__file__).resolve().parent
parser = argparse.ArgumentParser()
parser.add_argument('--copy-map', type=Path, help='Separate flat JSON object mapping original absolute input paths to archive paths')
args = parser.parse_args()
copy_map = json.loads(args.copy_map.read_text()) if args.copy_map else {}

def resolve(path):
    path = str(path)
    return Path(copy_map.get(path, path))

def read(path):
    return json.loads(resolve(path).read_text(encoding='utf-8'))

def sha(path):
    return hashlib.sha256(resolve(path).read_bytes()).hexdigest()

manifest, validation, packet = [read(BASE / name) for name in ['input-manifest.json', 'validation.json', 'blind-readbacks.json']]
for item in manifest['inputs']:
    assert sha(item['path']) == item['sha256'], item['path']
for item in manifest['original_artifacts']:
    assert sha(item['path']) == item['sha256'] == sha(BASE / item['frozen_copy_relative'])
    assert {k: v for k, v in read(item['path']).items() if k != 'bundles'} == item['metadata_verbatim']
for item in manifest['original_provenance_attachments']:
    assert sha(item['path']) == item['sha256'] == sha(BASE / item['frozen_copy_relative'])
for item in manifest['historical_original_artifacts']:
    assert sha(item['path']) == sha(item['declared_original_artifact']) == item['sha256'] == sha(BASE / item['frozen_copy_relative'])
    historical, current = read(item['path']), read(item['superseding_final_artifact'])
    assert item['revision_verbatim'] == current['revision']
    assert item['original_metadata_verbatim'] == {k: v for k, v in historical.items() if k != 'bundles'}
    assert current['revision']['originalSHA'] == item['sha256']
    assert current['revision']['same_original_fresh_context_continuation'] is True
    assert current['revision']['second_independent_audit'] is False
for item in manifest['original_recorded_inputs_checked']:
    assert sha(item['recorded_input']['path']) == item['recorded_input']['sha256'] == item['actual_sha256']
for name, digest in validation['output_hashes'].items():
    assert sha(BASE / name) == digest, name
template = read(next(x['path'] for x in manifest['inputs'] if x['role'] == 'delivery_schema_template'))
report = {x['definitionName']: x for x in read(next(x['path'] for x in manifest['inputs'] if x['role'] == 'wrapper_report'))['bundles']}
ledger_path = next(x['path'] for x in manifest['inputs'] if x['role'] == 'accepted_final_source_ledger')
ledger_document = read(ledger_path)
ledger = {x['producer']: x for x in ledger_document['entries']}
source_context = read(BASE / 'source-context-references.json')
assert source_context['accepted_ledger_verbatim'] == ledger_document
assert sha(BASE / source_context['ledger_copy_relative']) == sha(ledger_path) == source_context['ledger']['sha256']
assert source_context['proof_identity_policy']['source_proof_value_rows_may_have_null_wrapped_and_actualCompilerPair'] is True
names = [x['definition_name'] for x in template['bundles']]
assert set(template).issubset(packet)
assert [x['definition_name'] for x in packet['bundles']] == names
assert len(packet['independent_reviews']) == 2
subsets = []
for original_template, item in zip(template['independent_reviews'], packet['independent_reviews']):
    assert set(original_template).issubset(item)
    original = read(item['original_artifact'])
    assert sha(item['original_artifact']) == item['original_artifact_sha256']
    assert item['original_metadata_verbatim'] == {k: v for k, v in original.items() if k != 'bundles'}
    assert item['actual_model'] is original['actual_model'] is None
    subset = set(item['input_sha256_by_definition'])
    assert subset == set(original_template['input_sha256_by_definition'])
    assert subset == {x['definition_name'].removeprefix('Def_') for x in original['bundles']}
    for name, digest in item['input_sha256_by_definition'].items():
        blind = report[name]['blindReadback']
        actual_input = next(x for x in original['inputs'] if x['path'] == blind['path'])
        assert digest == actual_input['sha256'] == blind['sha256'] == sha(blind['path'])
    subsets.append(subset)
assert [len(x) for x in subsets] == [2, 2]
assert not subsets[0] & subsets[1] and subsets[0] | subsets[1] == set(names)
assert len({x['reviewer_id'] for x in packet['independent_reviews']}) == 2
for item in packet['bundles']:
    name, provenance = item['definition_name'], item['provenance']
    original = read(provenance['original_artifact'])
    ob = original['bundles'][provenance['original_bundle_index']]
    assert name == ob['definition_name'].removeprefix('Def_')
    assert provenance['original_definition_name'] == ob['definition_name']
    assert provenance['original_provenance_verbatim'] == original['provenance']
    if 'revision' in original:
        assert provenance['original_revision_verbatim'] == original['revision']
    assert provenance['actual_model'] is original['actual_model'] is None
    assert all(item[k] == ob[k] for k in ob if k != 'definition_name')
    assert item['source'] == ledger[name]['sourceURL']
    assert ledger[name]['originalModule'] == report[name]['module']
    assert item['source_sha256'] == ledger[name]['wrappedSourceSha256'] == report[name]['sha256'] == sha(report[name]['path'])
    actual_installed = next(x for x in manifest['inputs'] if x['role'] == 'actual_installed_definition' and Path(x['path']).name == 'Def_' + name + '.lean')
    assert sha(actual_installed['path']) == item['source_sha256']
    assert provenance['input_sha256'] == report[name]['blindReadback']['sha256'] == sha(report[name]['blindReadback']['path'])
    assert len(item['definition_title']) <= 200
    assert set(template['bundles'][0]).issubset(item)
    assert set(template['bundles'][0]['provenance']).issubset(provenance)
assert len(packet['bundles']) == 4
assert all(validation[k] is False for k in ['new_independent_readback_performed', 'proof_acceptance_performed',
    'compiler_type_review_performed', 'S2_04_completion_claimed', 'compilation_performed',
    'ci_used', 'api_used', 'network_used', 'git_used', 'main_workspace_edited', 'same_name_helper_identity_inferred'])
print(json.dumps({'metadata_passed': True, 'bundles': 4, 'primary_subset_sizes': [2, 2],
                  'primary_union_exactly_four': True, 'original_bundle_fields_and_disclosures_verbatim': True,
                  'original_inputs_verified': len(manifest['original_recorded_inputs_checked'])}, ensure_ascii=False))
