#!/usr/bin/env python3
"""Assemble existing compiler-reviewed readbacks; never author mathematical text."""
import argparse
import hashlib
import json
from pathlib import Path

OUT = Path(__file__).resolve().parent
W = Path('/home/admin-wsl/Coq/abc/prove2me_workspace')
B = W / '.local/adaptation/reference-initial-theta-carriers-20261115'
TEMPLATE = Path('/tmp/p2m-initial-theta-delivery-v6-20261115/delivery-blind-readbacks.template.json')
REPORT = B / 'generated-wrapped/foundation-wrapper-report.json'
PAPER = B / 'paper-context.json'
ORCHESTRATION = B / 'blind-orchestration.json'
SLICES = B / 'readback-compiler-type-slices.json'
GROUPS = ('geometry', 'local')
LANGUAGES = ('en', 'zh-Hans', 'ja')
TITLES = [
    'Geometry interfaces and selected curve data — 几何接口与所选曲线数据 — 幾何インターフェースと選択された曲線データ',
    'Tate families and place transport — Tate 族与处的变换 — Tate 族と素点の変換',
    'Local geometry and chosen local data — 局部几何与所选局部数据 — 局所幾何と選択された局所データ',
    'Initial theta data records — 初始 theta 数据记录 — 初期 theta データのレコード',
]

def read(path):
    return json.loads(Path(path).read_text(encoding='utf-8'))

def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def text_sha(value):
    return hashlib.sha256(value.encode('utf-8')).hexdigest()

def save(name, value):
    (OUT / name).write_text(json.dumps(value, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')

def record(path, role):
    return {'path': str(path), 'sha256': sha(path), 'role': role}

def artifact(path, relative, role, copies):
    target = OUT / relative
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_bytes(Path(path).read_bytes())
    assert sha(target) == sha(path)
    row = {**record(path, role), 'copy_relative': relative}
    copies.append(row)
    return row

def declaration_name(row):
    return row.get('name', row.get('declaration_name'))

def build():
    template, report, paper, orchestration = [read(x) for x in [TEMPLATE, REPORT, PAPER, ORCHESTRATION]]
    names = [x['definition_name'] for x in template['bundles']]
    reports = {x['definitionName']: x for x in report['bundles']}
    papers = {x['module']: x for x in paper['bundles']}
    assert len(names) == len(reports) == len(papers) == 4
    assert orchestration['configured_model'] == 'gpt-6.1-sol'
    assert orchestration['fresh_context'] is True and orchestration['code_only_math_inputs'] is True
    assert sha(B / 'blind-context-map.json') == orchestration['code_context_map_sha256']
    assert len(orchestration['reviewer_tasks']) == 2
    originals, copies, inputs, checked_inputs = [], [], [], []
    artifact(ORCHESTRATION, 'evidence/blind-orchestration.json', 'orchestrator_model_configuration', copies)
    artifact(SLICES, 'evidence/readback-compiler-type-slices.json', 'formal_compiler_type_input', copies)
    for path, role in [(TEMPLATE, 'delivery_schema_template'), (REPORT, 'wrapper_report'),
                       (PAPER, 'exact_19_command_source_context'), (ORCHESTRATION, 'orchestrator_model_configuration'),
                       (SLICES, 'formal_compiler_type_input'), (B / 'blind-context-map.json', 'code_context_map')]:
        inputs.append(record(path, role))
    counts = {'declarations': 0, 'structures': 0, 'fields': 0, 'compiler_records': 0}
    for group in GROUPS:
        source = Path('/tmp/p2m-initial-theta-blind-' + group + '-v6-20261115')
        final_path = source / 'audit.compiler-reviewed-v2.json'
        final = read(final_path)
        assert final['provenance']['actual_model'] is None
        assert final['provenance']['requested_model'] == orchestration['configured_model']
        originals.append((final_path, final))
        for filename in ['audit.compiler-reviewed-v2.json', 'audit.json',
                         'english-original.json' if group == 'geometry' else 'english.original.json',
                         'compiler-type-review.json' if group == 'geometry' else 'audit.compiler-reviewed-v2.exactchanges.json']:
            artifact(source / filename, 'originals/' + group + '/' + filename, group + '_original_or_revision', copies)
        for item in final['provenance']['source_inputs']:
            assert sha(item['path']) == item['sha256'], item['path']
            checked_inputs.append({'group': group, 'original_record_verbatim': item,
                                   'actual_sha256': sha(item['path']), 'matches': True})
        rules = final['provenance'].get('rules_input', final['provenance'].get('instructions_path'))
        inputs.append(record(rules, group + '_auditor_rules'))
        if group == 'geometry':
            review = read(source / 'compiler-type-review.json')
            assert sha(source / 'audit.json') == review['original_audit_sha256']
            assert sha(source / 'english-original.json') == review['originalResponseSHA']
            assert sha(SLICES) == review['compiler_input']['sha256']
            assert review['compiler_input']['job_id'] == 'ci-014954-6c6f799b'
            assert review['counts'] == {'source_declarations': 13, 'structure_fields': 39,
                                         'constructors_cross_checked': 3, 'compiler_records_checked': 55}
            counts['compiler_records'] += review['counts']['compiler_records_checked']
        else:
            changes = read(source / 'audit.compiler-reviewed-v2.exactchanges.json')
            assert sha(final_path) == changes['revised_sha256']
            assert sha(source / 'audit.json') == changes['original_sha256']
            assert sha(source / 'english.original.json') == changes['preserved_english_sha256']
            evidence = final['provenance']['compiler_type_input']
            assert sha(SLICES) == evidence['sha256'] and evidence['job_id'] == 'ci-014954-6c6f799b'
            review = final['compiler_type_review']
            assert review['declarations_reviewed'] == 6 and review['fields_reviewed'] == 38 and review['constructors_reviewed'] == 4
            counts['compiler_records'] += 6 + 38 + 4
    packet = {'schema': 'reference-initial-theta-compiler-reviewed-readbacks-v6', 'passed': True,
              'acceptance_scope': 'Readback byte preservation, input binding and completion of the supplied compiler-type review only. This assembler performed no mathematical kernel audit, proof acceptance, new independent readback, or parent-obligation completion.',
              'unconfirmed_chinese_terms_preserved': True,
              'unconfirmed_terms_policy': 'Every final original pending-term field and every original language string is preserved verbatim. No term is silently replaced.',
              'bundles': [], 'independent_reviews': []}
    source_context = {'schema': 'initial-theta-readback-source-metadata-v6',
                      'scope': 'Paper/source provenance and exact command selection only, separate from formal readback prose.',
                      'paper_context': record(PAPER, 'exact_19_command_source_context'), 'bundles': []}
    for group_index, (final_path, final) in enumerate(originals):
        expected = list(template['independent_reviews'][group_index]['input_sha256_by_definition'])
        assert [x['definition_name'].removeprefix('Def_') for x in final['bundles']] == expected
        reviewer = orchestration['reviewer_tasks'][group_index]
        primary = {}
        for original_row in final['bundles']:
            name = original_row['definition_name'].removeprefix('Def_')
            wrapped, original_input = reports[name], Path(original_row['input_path'])
            installed = W / 'Definitions' / ('Def_' + name + '.lean')
            blind = Path(wrapped['blindReadback']['path'])
            assert sha(installed) == sha(wrapped['path']) == wrapped['sha256']
            assert sha(original_input) == sha(blind) == wrapped['blindReadback']['sha256'] == original_row['input_sha256']
            assert original_input.read_bytes() == blind.read_bytes()
            assert original_input.parent == B / 'blind-context'
            primary[name] = original_row['input_sha256']
            for path, role in [(installed, 'actual_installed_definition'), (Path(wrapped['path']), 'generated_definition'),
                               (blind, 'authenticated_blind_input')]:
                inputs.append(record(path, role))
            paper_row = papers[wrapped['module']]
            provenance = paper_row['source_provenance']
            assert provenance['sourceSha256'] == wrapped['adaptationProvenance']['sourceSha256']
            assert sha(paper_row['source_path']) == paper_row['source_sha256'] == provenance['sourceSha256']
            inputs.append(record(paper_row['source_path'], 'original_module_source'))
            for binding in paper_row['selected_command_bindings']:
                assert sha(binding['source_command_path']) == binding['source_command_sha256']
                inputs.append(record(binding['source_command_path'], 'exact_selected_source_command'))
            source_url = provenance['originalRepository'] + '/blob/' + provenance['originalCommit'] + '/' + provenance['originalSourcePath']
            declarations = original_row['declarations']
            selected = paper_row['selected_source_commands']
            assert [declaration_name(x).removeprefix('AbcAdaptation.Reference.') for x in declarations] == selected
            assert len(paper_row['selected_command_bindings']) == len(selected)
            counts['declarations'] += len(declarations)
            for declaration in declarations:
                if declaration['kind'] != 'structure':
                    continue
                counts['structures'] += 1
                name_suffix = declaration_name(declaration).split('.')[-1]
                expected_fields = paper_row['structure_fields'][name_suffix]
                actual_fields = declaration.get('fields_covered')
                if actual_fields is None:
                    actual_fields = [x['field_name'] for x in declaration['fields']]
                assert actual_fields == expected_fields
                counts['fields'] += len(actual_fields)
            index = names.index(name)
            bundle = dict(original_row)
            bundle.update({'definition_name': name, 'source_sha256': wrapped['sha256'],
                           'definition_title': TITLES[index], 'source': source_url, 'passed': True,
                           'provenance': {
                               'author_model': orchestration['configured_model'], 'author_model_basis': 'orchestrator_configured',
                               'actual_model': final['provenance']['actual_model'],
                               'fresh_context': orchestration['fresh_context'],
                               'input_only_formal_code': orchestration['code_only_math_inputs'],
                               'input_sha256': original_row['input_sha256'],
                               'original_artifact': str(final_path), 'original_artifact_sha256': sha(final_path),
                               'reviewer_id': reviewer, 'original_bundle_index': final['bundles'].index(original_row),
                               'original_definition_name': original_row['definition_name'],
                               'original_provenance_verbatim': final['provenance'],
                               'orchestration': record(ORCHESTRATION, 'configured_model_not_observed_backend'),
                               'freshness_scope': 'The compiler-reviewed version continues the original fresh context; it is not an additional independent audit.',
                               'title_source': 'Editorial metadata based on the exact selected formal declarations; not added to any original readback string.',
                               'compiler_type_review_scope': 'The original reviewer inspected supplied formal output from ci-014954-6c6f799b. Assembly preserves that review and does not run or repeat it.'}})
            assert len(bundle['definition_title']) <= 200
            assert all(bundle[k] == v for k, v in original_row.items() if k != 'definition_name')
            assert set(template['bundles'][index]).issubset(bundle)
            packet['bundles'].append(bundle)
            source_context['bundles'].append({'definition_name': name, 'module': wrapped['module'],
                'source_url': source_url, 'source_provenance_verbatim': provenance,
                'selected_source_commands': selected, 'structure_fields': paper_row['structure_fields'],
                'selected_command_bindings': [{k: v for k, v in x.items() if k != 'source_text'}
                                              for x in paper_row['selected_command_bindings']]})
        review_row = {'reviewer_id': reviewer, 'author_model': orchestration['configured_model'],
                      'author_model_basis': 'orchestrator_configured', 'actual_model': None,
                      'fresh_context': True, 'input_only_formal_code': True,
                      'original_artifact': str(final_path), 'original_artifact_sha256': sha(final_path),
                      'passed': True, 'input_sha256_by_definition': primary,
                      'original_metadata_verbatim': {k: v for k, v in final.items() if k != 'bundles'},
                      'freshness_scope': 'Original independent fresh context followed by same-context compiler-type review; no additional independent audit claimed.',
                      'acceptance_scope': packet['acceptance_scope']}
        assert set(template['independent_reviews'][group_index]).issubset(review_row)
        packet['independent_reviews'].append(review_row)
    assert counts == {'declarations': 19, 'structures': 7, 'fields': 77, 'compiler_records': 103}, counts
    assert [x['definition_name'] for x in packet['bundles']] == names
    maps = [set(x['input_sha256_by_definition']) for x in packet['independent_reviews']]
    assert [len(x) for x in maps] == [2, 2] and not maps[0] & maps[1] and maps[0] | maps[1] == set(names)
    # Copying final rows retains the corrected distinction between the stored algebra
    # and the canonical scalar actions in towerModK, including per-field translations.
    save('blind-readbacks.json', packet)
    save('source-context.json', source_context)
    save('input-manifest.json', {'schema': 'initial-theta-readback-metadata-inputs-v6', 'inputs': inputs,
                                'original_inputs_checked': checked_inputs, 'original_and_evidence_copies': copies,
                                'compiler_type_review_coverage': counts,
                                'copy_policy': 'All originals and authored metadata are copied byte-for-byte; archive relocation uses a separate copy-map.'})
    save('validation.json', {'schema': 'initial-theta-readback-metadata-validation-v6', 'passed': True,
        'scope': packet['acceptance_scope'], 'coverage': counts, 'bundle_count': 4,
        'reviewer_primary_subset_sizes': [2, 2], 'all_final_original_fields_except_delivery_name_preserved': True,
        'orchestrator_configured_model': 'gpt-6.1-sol', 'actual_model': None,
        'model_basis': 'orchestrator_configured; actual backend unknown; original actual_model=null retained',
        'towerModK_stored_algebra_distinction_preserved_by_verbatim_copy': True,
        'new_independent_readback_performed': False, 'mathematical_kernel_acceptance_claimed': False,
        'parent_obligation_completed': False, 'main_workspace_edited': False, 'ci_compile_api_git_network_used': False,
        'output_sha256': {x: sha(OUT / x) for x in ['blind-readbacks.json', 'source-context.json', 'input-manifest.json']}})
    save('copy-map-relative.json', {x['path']: x['copy_relative'] for x in copies})
    print(json.dumps({'metadata_passed': True, 'coverage': counts, 'input_records_verified': len(checked_inputs)}))

def validate(copy_map_path=None):
    mapping = read(copy_map_path) if copy_map_path else {}
    def mapped(path):
        return Path(mapping.get(str(path), str(path)))
    def r(path):
        return read(mapped(path))
    def h(path):
        return sha(mapped(path))
    packet, manifest, validation = [read(OUT / x) for x in ['blind-readbacks.json', 'input-manifest.json', 'validation.json']]
    for item in manifest['inputs']:
        assert h(item['path']) == item['sha256'], item['path']
    for item in manifest['original_inputs_checked']:
        assert h(item['original_record_verbatim']['path']) == item['actual_sha256'] == item['original_record_verbatim']['sha256']
    for item in manifest['original_and_evidence_copies']:
        assert h(item['path']) == sha(OUT / item['copy_relative']) == item['sha256']
    for name, digest in validation['output_sha256'].items():
        assert sha(OUT / name) == digest
    template = r(next(x['path'] for x in manifest['inputs'] if x['role'] == 'delivery_schema_template'))
    reports = {x['definitionName']: x for x in r(next(x['path'] for x in manifest['inputs'] if x['role'] == 'wrapper_report'))['bundles']}
    orchestration = r(next(x['path'] for x in manifest['inputs'] if x['role'] == 'orchestrator_model_configuration'))
    assert len([x for x in manifest['inputs'] if x['role'] == 'exact_selected_source_command']) == 19
    assert set(template).issubset(packet)
    assert [x['definition_name'] for x in packet['bundles']] == [x['definition_name'] for x in template['bundles']]
    for row in packet['bundles']:
        p, name = row['provenance'], row['definition_name']
        original = r(p['original_artifact'])
        original_row = original['bundles'][p['original_bundle_index']]
        assert h(p['original_artifact']) == p['original_artifact_sha256']
        assert p['original_definition_name'] == original_row['definition_name']
        assert name == original_row['definition_name'].removeprefix('Def_')
        assert all(row[k] == v for k, v in original_row.items() if k != 'definition_name')
        assert p['original_provenance_verbatim'] == original['provenance']
        assert p['actual_model'] is original['provenance']['actual_model'] is None
        assert p['author_model'] == orchestration['configured_model'] and p['author_model_basis'] == 'orchestrator_configured'
        assert row['source_sha256'] == reports[name]['sha256'] == h(reports[name]['path'])
        assert p['input_sha256'] == row['input_sha256'] == h(row['input_path']) == reports[name]['blindReadback']['sha256']
        assert p['input_sha256'] == h(reports[name]['blindReadback']['path'])
        original_input = next(x for x in original['provenance']['source_inputs'] if x['path'] == row['input_path'])
        assert original_input['sha256'] == p['input_sha256']
    primary_sets = []
    for row in packet['independent_reviews']:
        original = r(row['original_artifact'])
        assert row['original_metadata_verbatim'] == {k: v for k, v in original.items() if k != 'bundles'}
        assert row['actual_model'] is None and row['author_model_basis'] == 'orchestrator_configured'
        primary_sets.append(set(row['input_sha256_by_definition']))
        assert row['input_sha256_by_definition'] == {x['definition_name'].removeprefix('Def_'): x['input_sha256'] for x in original['bundles']}
    assert [len(x) for x in primary_sets] == [2, 2] and not primary_sets[0] & primary_sets[1]
    assert primary_sets[0] | primary_sets[1] == {x['definition_name'] for x in packet['bundles']}
    assert validation['coverage'] == {'declarations': 19, 'structures': 7, 'fields': 77, 'compiler_records': 103}
    archive = OUT / 'archive-manifest.json'
    if archive.exists():
        for item in read(archive)['files']:
            assert sha(OUT / item['relative_path']) == item['sha256']
    print(json.dumps({'metadata_passed': True, 'bundles': 4, 'coverage': validation['coverage'],
                      'all_final_language_strings_and_fields_verbatim': True, 'actual_model': None}))

if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--validate', action='store_true')
    parser.add_argument('--copy-map', type=Path)
    args = parser.parse_args()
    if args.validate:
        validate(args.copy_map)
    else:
        build()
