#!/usr/bin/env python3
"""Combine existing readbacks only after final-input confirmation."""
import argparse
import sys
from pathlib import Path
sys.dont_write_bytecode = True
from prepare import (OUT, ROOT, W, B, REPORT, TEMPLATE, ORIGINALS, RAW_ORIGINALS,
                     REVIEWER_IDS, FINAL_ORIGINAL_SHA256, FORMULA_CONFIRMATION, COMPILER_TYPES,
                     PROOF_IDENTITY_POLICY, TITLES, read, sha, record, save, check_wrappers, prepare)

LANGUAGES = ('en', 'zh-Hans', 'ja')
LEDGER = B / 'SOURCE_LEDGER.json'

def complete():
    template, reports, wrapper_checks = check_wrappers()
    originals = [read(p) for p in ORIGINALS]
    ledger_document = read(LEDGER)
    ledger = {x['producer']: x for x in ledger_document['entries']}
    names = [x['definition_name'] for x in template['bundles']]
    assert set(ledger) == set(names)
    assert [len(x['bundles']) for x in originals] == [2, 2]
    original_hashes = [sha(p) for p in ORIGINALS]
    assert original_hashes == FINAL_ORIGINAL_SHA256
    original_artifacts, historical_artifacts, attachments, verified_inputs = [], [], [], []
    for group, (path, original, reviewer) in enumerate(zip(ORIGINALS, originals, REVIEWER_IDS)):
        assert original['author_model'] == 'gpt-6.1-sol'
        assert original['actual_model'] is None
        assert original['fresh_context'] is True and original['input_only_formal_code'] is True
        expected = list(template['independent_reviews'][group]['input_sha256_by_definition'])
        assert [x['definition_name'].removeprefix('Def_') for x in original['bundles']] == expected
        relative = 'originals/' + path.name
        copied = OUT / relative
        copied.parent.mkdir(exist_ok=True)
        copied.write_bytes(path.read_bytes())
        assert sha(copied) == sha(path)
        original_artifacts.append({**record(path, 'immutable_original_blind_readback'),
                                   'reviewer_id': reviewer, 'frozen_copy_relative': relative,
                                   'metadata_verbatim': {k: v for k, v in original.items() if k != 'bundles'}})
        if 'revision' in original:
            revision = original['revision']
            historical_path = B / 'blind-originals/structures-v1.json'
            declared_historical = Path(revision['original_artifact'])
            assert sha(historical_path) == sha(declared_historical) == revision['originalSHA']
            historical = read(historical_path)
            relative_historical = 'originals/structures-v1.json'
            (OUT / relative_historical).write_bytes(historical_path.read_bytes())
            historical_artifacts.append({**record(historical_path, 'historical_structures_v1'),
                                         'declared_original_artifact': str(declared_historical),
                                         'frozen_copy_relative': relative_historical,
                                         'superseding_final_artifact': str(path),
                                         'revision_verbatim': revision,
                                         'original_metadata_verbatim': {k: v for k, v in historical.items() if k != 'bundles'},
                                         'same_context_revision_not_second_audit': revision['same_original_fresh_context_continuation'] and not revision['second_independent_audit'],
                                         'language_field_comparison': [
                                             {'definition_name': now['definition_name'],
                                              **{lang: old[lang] == now[lang] for lang in LANGUAGES}}
                                             for old, now in zip(historical['bundles'], original['bundles'])]})
        for item in original['inputs']:
            actual = sha(item['path'])
            assert actual == item['sha256']
            if 'sha256_after' in item:
                assert actual == item['sha256_after']
            verified_inputs.append({'original_artifact': str(path), 'recorded_input': item,
                                    'actual_sha256': actual, 'matches': True})
        provenance = original['provenance']
        for path_key, hash_key in [('frozen_English_artifact', 'frozen_English_sha256'),
                                   ('english_artifact', 'english_sha256')]:
            if path_key not in provenance:
                continue
            disclosed = provenance[path_key]
            attachment = Path(disclosed)
            if not attachment.is_absolute():
                attachment = RAW_ORIGINALS[group].parent / attachment
            assert sha(attachment) == provenance[hash_key]
            relative_attachment = 'originals/english-' + ('formulas' if group == 0 else 'structures') + '.json'
            (OUT / relative_attachment).write_bytes(attachment.read_bytes())
            attachments.append({**record(attachment, 'original_english_provenance_attachment'),
                                'original_artifact': str(path), 'disclosed_path_verbatim': disclosed,
                                'frozen_copy_relative': relative_attachment})
    packet = {
        'schema': 'reference-tate-theta-reviewed-blind-readbacks-v5', 'passed': True,
        'acceptance_scope': 'Offline metadata consistency only. This assembly is not an independent readback, proof acceptance, compiler-type review, or S2-04 completion.',
        'unconfirmed_chinese_terms_preserved': True,
        'unconfirmed_terms_policy': 'Preserve every original pending term, including 【待定译名：uniformizer】. No candidate is substituted. All original EN/ZH/JA and all original disclosures remain verbatim.',
        'bundles': [], 'independent_reviews': [],
    }
    for group, (original, path, reviewer, template_review) in enumerate(zip(
            originals, ORIGINALS, REVIEWER_IDS, template['independent_reviews'])):
        primary_map = {}
        for name in template_review['input_sha256_by_definition']:
            blind = reports[name]['blindReadback']
            item = next(x for x in original['inputs'] if x['path'] == blind['path'])
            assert item['sha256'] == blind['sha256'] == sha(blind['path'])
            primary_map[name] = item['sha256']
        review = {'reviewer_id': reviewer, 'author_model': original['author_model'],
                  'actual_model': original['actual_model'], 'fresh_context': original['fresh_context'],
                  'input_only_formal_code': original['input_only_formal_code'],
                  'original_artifact': str(path), 'original_artifact_sha256': sha(path), 'passed': True,
                  'input_sha256_by_definition': primary_map,
                  'original_metadata_verbatim': {k: v for k, v in original.items() if k != 'bundles'},
                  'acceptance_scope': 'Original identity and current input hash consistency only; the map covers only this reviewer primary subset.'}
        assert set(template_review).issubset(review)
        packet['independent_reviews'].append(review)
        if 'revision' in original:
            review['original_revision_verbatim'] = original['revision']
            review['fresh_context_scope'] = 'fresh_context records the original independent context; v2 is its same-context continuation, not a second fresh audit.'
        if group == 0:
            review['same_context_formal_type_confirmation'] = record(FORMULA_CONFIRMATION, 'same_context_formula_type_confirmation')
    for index, (template_row, title) in enumerate(zip(template['bundles'], TITLES)):
        group, ordinal = divmod(index, 2)
        original, path = originals[group], ORIGINALS[group]
        ob = original['bundles'][ordinal]
        name = template_row['definition_name']
        row, source = reports[name], ledger[name]
        assert ob['definition_name'].removeprefix('Def_') == name
        assert source['originalModule'] == row['module']
        assert sha(W / 'Definitions' / ('Def_' + name + '.lean')) == sha(row['path']) == row['sha256'] == source['wrappedSourceSha256']
        primary_map = packet['independent_reviews'][group]['input_sha256_by_definition']
        bundle = {k: v for k, v in ob.items() if k != 'definition_name'}
        bundle.update({'definition_name': name, 'source_sha256': row['sha256'],
                       'definition_title': title, 'source': source['sourceURL'], 'passed': True,
                       'editorial_changes': [],
                       'provenance': {
                           'author_model': original['author_model'], 'actual_model': original['actual_model'],
                           'fresh_context': original['fresh_context'],
                           'input_only_formal_code': original['input_only_formal_code'],
                           'input_sha256': primary_map[name], 'original_artifact': str(path),
                           'original_artifact_sha256': sha(path), 'reviewer_id': REVIEWER_IDS[group],
                           'original_bundle_index': ordinal,
                           'original_definition_name': ob['definition_name'],
                           'original_provenance_verbatim': original['provenance'],
                           'title_provenance': 'Content-grounded editorial trilingual title from the actual formal declarations, not a source-paper title or inferred theorem.',
                           'model_provenance': 'author_model is the original requested label; actual_model=null is retained, not replaced with an inferred runtime identity.',
                           'binder_retention_scope': 'Frozen original text is preserved. The final same-context compiler-type confirmation/revision is recorded separately; the assembler performs no additional compiler-type judgment.',
                           'metadata_assembly': 'Metadata only. Original readback strings, original optional fields and disclosures are copied verbatim.'}})
        if 'revision' in original:
            bundle['provenance']['original_revision_verbatim'] = original['revision']
        elif group == 0:
            bundle['provenance']['same_context_formal_type_confirmation'] = record(FORMULA_CONFIRMATION, 'same_context_formula_type_confirmation')
        assert set(template_row).issubset(bundle)
        assert set(template_row['provenance']).issubset(bundle['provenance'])
        assert len(title) <= 200
        assert all(isinstance(bundle[k], str) and bundle[k].strip() for k in [*LANGUAGES, 'source', 'definition_title'])
        assert all(bundle[k] == ob[k] for k in ob if k != 'definition_name')
        packet['bundles'].append(bundle)
    primary_sets = [set(x['input_sha256_by_definition']) for x in packet['independent_reviews']]
    assert [len(x) for x in primary_sets] == [2, 2]
    assert not primary_sets[0] & primary_sets[1] and primary_sets[0] | primary_sets[1] == set(names)
    inputs = [record(ROOT / 'AGENTS.md', 'workspace_instructions'),
              record(ROOT / 'docs/三语自然语言读回原则.md', 'readback_rules'),
              record(ROOT / 'docs/三语术语名词关键对照.md', 'terminology_rules'),
              record(TEMPLATE, 'delivery_schema_template'), record(REPORT, 'wrapper_report'),
              record(LEDGER, 'accepted_final_source_ledger'),
              record(FORMULA_CONFIRMATION, 'same_context_formula_type_confirmation'),
              record(COMPILER_TYPES, 'formal_compiler_telescope_input')]
    confirmation = read(FORMULA_CONFIRMATION)
    assert confirmation['same_context_continuation'] is True and confirmation['second_fresh_audit'] is False
    assert confirmation['revision_required'] is False
    assert sha(COMPILER_TYPES) == confirmation['compiler_input']['sha256_before'] == confirmation['compiler_input']['sha256_after']
    for artifact in confirmation['original_artifacts']:
        assert sha(artifact['path']) == artifact['sha256_before'] == artifact['sha256_after']
    relative_confirmation = 'originals/formula-formal-type-confirmation.json'
    (OUT / relative_confirmation).write_bytes(FORMULA_CONFIRMATION.read_bytes())
    attachments.append({**record(FORMULA_CONFIRMATION, 'same_context_formula_type_confirmation'),
                        'frozen_copy_relative': relative_confirmation})
    for check in wrapper_checks:
        inputs += [check['installed'], check['generated'], check['blind']]
    for key in ['wrapperReport', 'acceptedCompilerCorrespondence']:
        if key in ledger_document:
            linked = ledger_document[key]
            assert sha(linked['path']) == linked['sha256']
            inputs.append(record(linked['path'], 'ledger_referenced_' + key))
    ledger_relative = 'source-context/SOURCE_LEDGER.json'
    (OUT / ledger_relative).parent.mkdir(exist_ok=True)
    (OUT / ledger_relative).write_bytes(LEDGER.read_bytes())
    assert sha(OUT / ledger_relative) == sha(LEDGER)
    source_context = {'schema': 'reference-tate-theta-source-context-references-v5',
                      'scope': 'Accepted ledger source metadata kept separate from blind readback prose.',
                      'ledger': record(LEDGER, 'accepted_final_source_ledger'),
                      'ledger_copy_relative': ledger_relative,
                      'accepted_ledger_verbatim': ledger_document,
                      'proof_identity_policy': PROOF_IDENTITY_POLICY,
                      'correspondence_scope': 'The assembler does not construct per-constant source/compiler identity pairs. Final ledger proof rows, including null wrapped/actualCompilerPair and typed helper collision evidence, are preserved verbatim.'}
    save('blind-readbacks.json', packet)
    save('input-manifest.json', {'schema': 'reference-tate-theta-readback-metadata-inputs-v5',
                                'assembly_role': 'metadata_only', 'inputs': inputs,
                                'original_artifacts': original_artifacts, 'original_provenance_attachments': attachments,
                                'historical_original_artifacts': historical_artifacts,
                                'original_recorded_inputs_checked': verified_inputs,
                                'archive_policy': 'New within-packet copies are relative. Archive authored artifacts byte-for-byte; use a separate root copy-map without rewriting original artifacts or validation hashes.'})
    save('source-context-references.json', source_context)
    save('review.json', {'schema': 'reference-tate-theta-readback-metadata-review-v5',
                        'review_kind': 'additive_metadata_review_only', 'original_readback_text_changes': [],
                        'translation_corrections': [], 'new_independent_readback_performed': False,
                        'proof_acceptance_performed': False, 'S2_04_completion_claimed': False,
                        'name_mapping': [{'original': x['provenance']['original_definition_name'],
                                          'canonical': x['definition_name']} for x in packet['bundles']],
                        'optional_fields_policy': 'All original bundle fields other than the delivery name are retained verbatim, including proof_notes and optionalproof_notes under their exact original keys.',
                        'binder_retention_policy': 'The frozen formula audit is unchanged; its separate same-context type confirmation is included. The selected structure audit is author v2, whose four retained CompleteSpace assumptions and three uncertainty resolutions are recorded verbatim with v1 history. The assembler changes no original readback text.',
                        'same_context_type_followups_are_not_new_fresh_audits': True,
                        'proof_identity_policy': PROOF_IDENTITY_POLICY,
                        'archive_policy': 'Copy all authored artifacts byte-for-byte; a root copy-map is separate and does not rewrite these artifacts.'})
    assert original_hashes == [sha(p) for p in ORIGINALS]
    save('validation.json', {'schema': 'reference-tate-theta-readback-metadata-validation-v5',
                            'passed': True, 'scope': 'Offline metadata consistency only',
                            'bundle_count': 4, 'original_context_count': 2,
                            'historical_original_artifact_count': len(historical_artifacts),
                            'accepted_source_ledger_copied_verbatim': True,
                            'null_source_proof_correspondence_fields_preserved': True,
                            'same_name_helper_identity_inferred': False,
                            'primary_subset_sizes': [2, 2], 'primary_union_exactly_four': True,
                            'original_recorded_inputs_verified_count': len(verified_inputs),
                            'original_all_bundle_fields_except_delivery_name_verbatim': True,
                            'original_disclosures_verbatim': True, 'pending_terms_verbatim': True,
                            'new_independent_readback_performed': False, 'proof_acceptance_performed': False,
                            'compiler_type_review_performed': False, 'S2_04_completion_claimed': False,
                            'compilation_performed': False, 'ci_used': False, 'api_used': False,
                            'network_used': False, 'git_used': False, 'main_workspace_edited': False,
                            'output_hashes': {name: sha(OUT / name) for name in [
                                'blind-readbacks.json', 'input-manifest.json', 'source-context-references.json', 'review.json']}})
    print({'bundles': 4, 'primary_subset_sizes': [2, 2], 'original_inputs_verified': len(verified_inputs), 'metadata_passed': True})

if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--assemble', action='store_true')
    parser.add_argument('--accepted-ledger-confirmed', action='store_true',
                        help='Use only after coordinating-agent final-originals and accepted-ledger notification')
    options = parser.parse_args()
    if options.assemble:
        if not options.accepted_ledger_confirmed:
            parser.error('Final assembly requires coordinating-agent accepted-ledger confirmation')
        complete()
    else:
        prepare()
