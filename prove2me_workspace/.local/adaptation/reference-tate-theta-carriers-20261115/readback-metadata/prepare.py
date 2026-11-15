#!/usr/bin/env python3
"""Prepare metadata checks and titles without creating readback content."""
import hashlib
import json
from pathlib import Path

OUT = Path(__file__).resolve().parent
ROOT = Path('/home/admin-wsl/Coq/abc')
W = ROOT / 'prove2me_workspace'
B = W / '.local/adaptation/reference-tate-theta-carriers-20261115'
REPORT = B / 'generated-wrapped/foundation-wrapper-report.json'
TEMPLATE = Path('/tmp/p2m-tate-theta-delivery-v5-20261115/delivery-blind-readbacks.template.json')
ORIGINALS = [B / 'blind-originals/formulas.json', B / 'blind-originals/structures.json']
RAW_ORIGINALS = [Path('/tmp/p2m-tate-theta-blind-formulas-v5-20261115/audit.json'),
                 Path('/tmp/p2m-tate-theta-blind-structures-v5-20261115/audit.json')]
REVIEWER_IDS = ['/root/tate_theta_blind_formulas_v5', '/root/tate_theta_blind_structures_v5']
FINAL_ORIGINAL_SHA256 = ['7bac0bbb4b6e069569f8302d36ee6b386425ed818dcded679f07b6f6c1ee0e65',
                         '4361a2fd2f4e9925ce139ab46098c522b011e8e44e8e9e0e99de2269666997a4']
FORMULA_CONFIRMATION = B / 'blind-materials/formulas/formal-type-confirmation.json'
COMPILER_TYPES = B / 'readback-compiler-types.json'
PROOF_IDENTITY_POLICY = {
    'status': 'coordinator_policy_for_preparation_not_independent_kernel_acceptance',
    'source_count': 78, 'source_named_count': 76, 'source_genuine_proof_value_count': 2,
    'current_owned_count': 77, 'current_named_count': 76, 'current_compiler_only_count': 1,
    'source_proof_value_rows_may_have_null_wrapped_and_actualCompilerPair': True,
    'same_name_is_not_identity_evidence': True,
    'qOrder_helper_collision': {
        'helper_basename': 'qOrder._proof_1',
        'source_type_as_reported': 'Infinite (𝓞 F)',
        'current_same_name_type_as_reported': 'Module.Finite ℤ (𝓞 F)',
        'policy': 'Preserve final typed collision evidence. Do not identify these distinct typed helpers by their name.'},
    'preservation': 'Copy final accepted ledger verbatim, including typed collisions, compiler-only evidence, genuine proof values and null correspondence fields.'}
TITLES = [
    'Tate c₄³/Δ formula — Tate 的 c₄³/Δ 公式 — Tate の c₄³/Δ の式',
    'Tate coordinate series — Tate 坐标级数 — Tate 座標の級数',
    'Prime data, torsion action and local parameters — 素数数据、挠点作用与局部参数 — 素数データ・捩れ点作用・局所パラメータ',
    'Tate quotient structures and coordinates — Tate 商结构与坐标 — Tate 商構造と座標',
]

def read(path):
    return json.loads(Path(path).read_text(encoding='utf-8'))

def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def record(path, role):
    return {'path': str(path), 'sha256': sha(path), 'role': role}

def save(name, value):
    (OUT / name).write_text(json.dumps(value, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')

def check_wrappers():
    template, report = read(TEMPLATE), read(REPORT)
    names = [x['definition_name'] for x in template['bundles']]
    reports = {x['definitionName']: x for x in report['bundles']}
    assert len(names) == len(reports) == 4 and set(names) == set(reports)
    subsets = [list(x['input_sha256_by_definition']) for x in template['independent_reviews']]
    assert len(subsets) == 2 and [len(x) for x in subsets] == [2, 2]
    assert not set(subsets[0]) & set(subsets[1])
    assert set(subsets[0]) | set(subsets[1]) == set(names)
    assert subsets == [names[:2], names[2:]]
    checks = []
    for name in names:
        row = reports[name]
        installed = W / 'Definitions' / ('Def_' + name + '.lean')
        generated = Path(row['path'])
        blind = Path(row['blindReadback']['path'])
        assert sha(installed) == sha(generated) == row['sha256']
        assert installed.read_bytes() == generated.read_bytes()
        assert sha(blind) == row['blindReadback']['sha256']
        checks.append({'definition_name': name, 'module': row['module'],
                       'installed': record(installed, 'actual_installed_definition'),
                       'generated': record(generated, 'generated_definition'),
                       'blind': record(blind, 'authenticated_blind_input'),
                       'installed_generated_report_match': True})
    return template, reports, checks

def prepare():
    template, reports, checks = check_wrappers()
    originals_available = []
    for index, raw_path in enumerate(RAW_ORIGINALS):
        path = ORIGINALS[index] if ORIGINALS[index].is_file() else raw_path
        if not path.is_file():
            originals_available.append({'path': str(path), 'available': False})
            continue
        original = read(path)
        if path == ORIGINALS[index]:
            assert sha(path) == FINAL_ORIGINAL_SHA256[index]
        expected_names = list(template['independent_reviews'][index]['input_sha256_by_definition'])
        original_names = [x['definition_name'] for x in original['bundles']]
        assert [x.removeprefix('Def_') for x in original_names] == expected_names
        actual_inputs = []
        for item in original['inputs']:
            actual = sha(item['path'])
            assert actual == item['sha256']
            if 'sha256_after' in item:
                assert actual == item['sha256_after']
            actual_inputs.append({'recorded_input': item, 'actual_sha256': actual, 'matches': True})
        primary_map = {}
        for name in expected_names:
            blind = reports[name]['blindReadback']
            actual_input = next(x for x in original['inputs'] if x['path'] == blind['path'])
            assert actual_input['sha256'] == blind['sha256'] == sha(blind['path'])
            primary_map[name] = blind['sha256']
        originals_available.append({**record(path, 'raw_original_schema_preparation_only'),
                                    'available': True, 'author_model': original['author_model'],
                                    'actual_model': original.get('actual_model'),
                                    'reviewer_id': REVIEWER_IDS[index],
                                    'original_bundle_name_mapping': dict(zip(original_names, expected_names)),
                                    'primary_input_sha256_by_definition': primary_map,
                                    'recorded_inputs_checked': actual_inputs,
                                    'bundle_field_sets': [list(x) for x in original['bundles']],
                                    'original_metadata_keys': [k for k in original if k != 'bundles']})
    followups = []
    for path, role in [(FORMULA_CONFIRMATION, 'same_context_formula_type_confirmation'),
                       (COMPILER_TYPES, 'formal_compiler_telescope_input')]:
        if path.is_file():
            followups.append(record(path, role))
    save('prepared-wrapper-validation.json', {
        'schema': 'reference-tate-theta-readback-metadata-preparation-v5',
        'status': 'preparation-only-awaiting-two-final-originals-and-accepted-ledger',
        'template': record(TEMPLATE, 'required_delivery_schema'),
        'report': record(REPORT, 'wrapper_and_blind_input_hashes'), 'checks': checks,
        'primary_subsets': [list(x['input_sha256_by_definition']) for x in template['independent_reviews']],
        'originals_schema_preparation': originals_available,
        'integrated_final_originals_expected': [str(x) for x in ORIGINALS],
        'coordinator_confirmed_final_original_sha256': FINAL_ORIGINAL_SHA256,
        'formal_type_followups': followups,
        'proof_identity_policy': PROOF_IDENTITY_POLICY,
        'reviewer_context_ids_confirmed_by_coordinator': REVIEWER_IDS,
        'accepted_ledger_confirmation_received': False,
        'editorial_titles': dict(zip([x['definition_name'] for x in template['bundles']], TITLES)),
        'readback_text_generated': False, 'final_packet_generated': False,
        'uniformizer_policy': 'Preserve every original 【待定译名：uniformizer】 marker verbatim.',
        'binder_retention_policy': 'Keep frozen original text and final same-context compiler-type confirmation/revision verbatim. Formulas are unchanged with a separate confirmation; structures selects v2 and preserves historical v1. The assembler makes no additional compiler-type judgment.',
        'archive_policy': 'All authored artifacts must be copied byte-for-byte. Use a separate root copy-map; never rewrite archived artifact paths or validation hashes.',
        'scope': 'Partial reference adaptation only; no S2-04 completion or proof acceptance is claimed.',
    })
    save('required-delivery-schema.json', {
        'schema': 'reference-tate-theta-readback-metadata-required-fields-v5',
        'template': record(TEMPLATE, 'required_delivery_schema'),
        'required_top_level_fields': list(template),
        'required_bundle_fields': list(template['bundles'][0]),
        'required_bundle_provenance_fields': list(template['bundles'][0]['provenance']),
        'required_independent_review_fields': list(template['independent_reviews'][0]),
        'bundle_order': [x['definition_name'] for x in template['bundles']],
        'independent_primary_subsets': [list(x['input_sha256_by_definition']) for x in template['independent_reviews']],
        'primary_subset_policy': 'Each map contains exactly its reviewer original primary subset, not prerequisite files or the other reviewer targets. The two maps are disjoint and their union is exactly four.',
        'proof_identity_policy': PROOF_IDENTITY_POLICY,
        'preservation_policy': 'Copy actual original EN/ZH/JA, declaration coverage, ambiguities, proof notes and complete disclosures verbatim. author_model is not inferred runtime identity; actual_model remains null when reported null.',
        'archive_copy_policy': 'Use relative paths for new within-packet copies. Preserve all originally disclosed paths verbatim. Migration uses a separate copy-map and does not rewrite generated validation hashes.',
        'finalization_policy': 'Do not create an accepted final packet until the coordinating agent confirms both final originals and the accepted final ledger.',
    })
    print(json.dumps({'wrapper_checks_passed': len(checks), 'primary_subset_sizes': [2, 2],
                      'raw_originals_available': sum(x['available'] for x in originals_available),
                      'final_packet_generated': False}, ensure_ascii=False))

if __name__ == '__main__':
    prepare()
