#!/usr/bin/env python3
"""Assemble existing blind readbacks; do not compile, translate, or publish."""
import hashlib
import json
from pathlib import Path

OUT = Path(__file__).resolve().parent
ROOT = Path('/home/admin-wsl/Coq/abc')
BASE = ROOT / 'prove2me_workspace/.local/adaptation/reference-packet-field-carriers-20261115'
PREVIOUS = BASE.parent / 'foundation-reference-carriers-20261115/blind-readbacks.json'
REPORT = BASE / 'generated-wrapped/foundation-wrapper-report.json'
LEDGER = BASE / 'SOURCE_LEDGER.json'
TEMPLATE = BASE / 'delivery-blind-readbacks.template.json'
LANGUAGES = ('en', 'zh-Hans', 'ja')

def read(path):
    return json.loads(Path(path).read_text(encoding='utf-8'))

def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def save(name, value):
    (OUT / name).write_text(json.dumps(value, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')

def record(path, role):
    path = Path(path)
    return {'path': str(path), 'sha256': sha(path), 'role': role}

titles = [
    'Large-volume container data — 大体积容器数据 — 大体積コンテナデータ',
    'Hull systems and least hull regions — 包络系统与最小包络区域 — 包絡系と最小包絡領域',
    'Global field conditions and auxiliary constructions — 全局域条件与辅助构造 — 大域体の条件と補助構成',
    'Automorphisms and finite places — 自同构与有限处 — 自己同型と有限素点',
    'Tate parameters in normed fields — 赋范域中的 Tate 参数 — ノルム体上の Tate パラメータ',
]
template = read(TEMPLATE)
ledger = {x['producer']: x for x in read(LEDGER)['entries']}
reports = {x['definitionName']: x for x in read(REPORT)['bundles']}
original_paths = [BASE / 'blind-originals/container-hull.json', BASE / 'blind-originals/global-tate.json']
originals = [read(p) for p in original_paths]
original_hashes = [sha(p) for p in original_paths]
flat = [(original_paths[0], originals[0], x) for x in originals[0]['bundles']]
flat += [(original_paths[1], originals[1], x) for x in originals[1]['bundles']]
assert len(flat) == len(template['bundles']) == len(ledger) == len(reports) == 5

inputs = [record(ROOT / 'AGENTS.md', 'workspace_instructions'),
          record(ROOT / 'docs/三语自然语言读回原则.md', 'readback_rules'),
          record(ROOT / 'docs/三语术语名词关键对照.md', 'terminology_rules'),
          record(LEDGER, 'canonical_names_source_urls_and_module_hashes'),
          record(REPORT, 'wrapper_and_blind_input_hashes'),
          record(TEMPLATE, 'delivery_schema_template'),
          record(PREVIOUS, 'previous_accepted_schema')]
dependencies_checked = []
artifacts = []
for path, original in zip(original_paths, originals):
    copied = OUT / 'originals' / path.name
    copied.parent.mkdir(exist_ok=True)
    copied.write_bytes(path.read_bytes())
    assert sha(copied) == sha(path)
    artifacts.append({**record(path, 'immutable_original_blind_readback'),
                      'frozen_copy': str(copied),
                      'metadata_verbatim': {k: v for k, v in original.items() if k != 'bundles'}})
    rows = original.get('inputs', []) + original.get('rule_inputs', []) + original.get('formal_dependency_inputs', [])
    if 'audit_rules_actually_read' in original:
        rows += [original['audit_rules_actually_read']]
    for row in rows:
        actual = sha(row['path'])
        assert actual == row['sha256'], ('Original input changed', row['path'])
        dependencies_checked.append({'original_artifact': str(path), 'recorded_input': row,
                                     'actual_sha256': actual, 'matches': True})

packet = {
    'schema': 'reference-packet-field-reviewed-blind-readbacks-v3',
    'passed': True,
    'acceptance_scope': 'Metadata assembly and byte/hash/schema consistency only. This does not add an independent readback, a proof acceptance, a compilation receipt, or publication authorization.',
    'unconfirmed_chinese_terms_preserved': True,
    'unconfirmed_terms_policy': 'User-confirmed capsule=标签集, procession=标签集递增族, hull=包络. All original English, Simplified Chinese and Japanese readback strings are preserved verbatim. This assembly introduces no new readback terminology or translation.',
    'bundles': [],
}
source_context = {'schema': 'reference-packet-field-source-context-references-v1',
                  'scope': 'Source/provenance metadata only; not part of the original blind readback and not mathematical evidence added to it.',
                  'ledger': record(LEDGER, 'source_ledger'), 'bundles': []}

for index, (row, title, original_info) in enumerate(zip(template['bundles'], titles, flat)):
    original_path, original, original_bundle = original_info
    name = row['definition_name']
    entry, report = ledger[name], reports[name]
    generated = Path(report['path'])
    installed = ROOT / 'prove2me_workspace/Definitions' / ('Def_' + name + '.lean')
    blind = Path(report['blindReadback']['path'])
    actual = sha(installed)
    assert name == report['definitionName'] == entry['producer']
    assert actual == sha(generated) == report['sha256'] == entry['wrappedSourceSha256']
    assert installed.read_bytes() == generated.read_bytes()
    assert sha(blind) == report['blindReadback']['sha256']
    original_input = next(x for x in original['inputs'] if x['path'] == str(blind))
    assert original_input['sha256'] == sha(blind)
    if index >= 2:
        assert original_bundle['definition_name'] == 'Def_' + name
        assert original_bundle['input'] == original_input
    fresh_key = 'fresh_context' if 'fresh_context' in original else 'genuinefresh_context'
    assert original[fresh_key] is True and original['input_only_formal_code'] is True
    provenance = {
        'author_model': original['author_model'],
        'fresh_context': original[fresh_key],
        'input_only_formal_code': original['input_only_formal_code'],
        'input_sha256': sha(blind),
        'original_artifact': str(original_path),
        'original_artifact_sha256': sha(original_path),
        'original_bundle_index': index if index < 2 else index - 2,
        'original_definition_name': original_bundle['definition_name'],
        'original_fresh_context_field': {'key': fresh_key, 'value': original[fresh_key]},
        'original_blind_input': original_input,
        'source_semantics': 'Wrapper report binds the production file and the narrative-stripped blind input. Source context remains separate from all three original readback strings.',
        'translation_provenance': original.get('translation_provenance', {
            'source': 'en in the immutable original artifact',
            'translator_model': original['author_model'],
            'languages': ['zh-Hans', 'ja'],
            'disclosure_verbatim': original.get('provenance_note'),
        }),
        'rules_scope_disclosure': original.get('provenance_note', original.get('readback_method')),
        'metadata_assembly': 'Existing readbacks combined with ledger/report/file hashes. No new independent blind reading or proof acceptance was performed.',
        'title_provenance': 'Editorial trilingual title based on actual formal declarations; no title field exists in ledger, wrapper report, payload, or Lean source. Approved as editorial metadata by the coordinating agent.',
    }
    bundle = {'definition_name': name, 'source_sha256': actual,
              'definition_title': title, 'source': entry['sourceURL'],
              **{lang: original_bundle[lang] for lang in LANGUAGES},
              'passed': True,
              'declaration_coverage': original_bundle['declaration_coverage'],
              'possible_ambiguities': original_bundle['possible_ambiguities'],
              'editorial_changes': [], 'provenance': provenance}
    assert len(title) <= 200
    assert set(row).issubset(bundle)
    assert set(row['provenance']).issubset(provenance)
    for lang in LANGUAGES:
        assert bundle[lang] == original_bundle[lang]
        assert bundle[lang].strip()
        assert 'REPLACE_WITH' not in bundle[lang]
    packet['bundles'].append(bundle)
    inputs += [record(installed, 'actual_installed_definition'), record(generated, 'generated_definition'),
               record(blind, 'authenticated_blind_input')]
    source_context['bundles'].append({
        'definition_name': name, 'originalModule': entry['originalModule'],
        'sourceURL': entry['sourceURL'], 'sourceProvenance': entry['sourceProvenance'],
        'wrappedSourceSha256': entry['wrappedSourceSha256'], 'actualScope': entry['actualScope'],
        'rootGraphMembership': entry['rootGraphMembership'],
        'canonicalC22Connected': entry['canonicalC22Connected'],
    })

assert set(template).issubset(packet)
previous = read(PREVIOUS)
assert set(previous).issubset(packet)
assert all(set(previous['bundles'][0]).issubset(x) for x in packet['bundles'])
save('blind-readbacks.json', packet)
save('source-context-references.json', source_context)
save('input-manifest.json', {
    'schema': 'reference-packet-field-readback-metadata-inputs-v3',
    'assembly_role': 'metadata_only', 'inputs': inputs,
    'original_artifacts': artifacts, 'original_recorded_inputs_checked': dependencies_checked,
    'terminology_decisions': [
        {'original': 'capsule', 'zh-Hans': '标签集', 'status': 'user_confirmed', 'term': 'TERM-009'},
        {'original': 'procession', 'zh-Hans': '标签集递增族', 'status': 'user_confirmed', 'term': 'TERM-010'},
        {'original': 'hull', 'zh-Hans': '包络', 'status': 'user_confirmed', 'term': 'TERM-008'},
    ],
})
save('review.json', {
    'schema': 'reference-packet-field-readback-metadata-review-v3',
    'review_kind': 'additive_metadata_review_only',
    'original_readback_text_changes': [], 'translation_corrections': [],
    'fresh_context_normalization': {
        'artifact': str(original_paths[0]), 'original_key': 'genuinefresh_context',
        'original_value': True, 'delivery_key': 'fresh_context',
        'reason': 'Normalize original metadata spelling for the required delivery schema while preserving the original key/value and artifact.'},
    'bundle_identifier_mapping': [
        {'original_artifact': x['provenance']['original_artifact'],
         'original_definition_name': x['provenance']['original_definition_name'],
         'canonical_delivery_name': x['definition_name']} for x in packet['bundles']],
    'hull_japanese_decision': 'Preserve generic 包絡 in the original readback: the actual definitions impose no holomorphic condition. TERM-008 explicitly does not add 正則 automatically to a general hull. File naming/source intent is not added to formal semantics.',
    'title_decision': 'Use content-grounded editorial titles; title provenance is explicit in each bundle.',
    'proof_acceptance_performed': False, 'new_independent_readback_performed': False,
})

# Validate the serialized delivery artifact, not merely the in-memory construction.
serialized = read(OUT / 'blind-readbacks.json')
checks = []
for row, (_, original, ob) in zip(serialized['bundles'], flat):
    checks.append({'definition_name': row['definition_name'],
                   'canonical_name_and_source_url_match_ledger': row['source'] == ledger[row['definition_name']]['sourceURL'],
                   'installed_generated_report_ledger_hashes_match': row['source_sha256'] == sha(ROOT / 'prove2me_workspace/Definitions' / ('Def_' + row['definition_name'] + '.lean')) == reports[row['definition_name']]['sha256'] == ledger[row['definition_name']]['wrappedSourceSha256'],
                   'original_en_zh_ja_verbatim': all(row[k] == ob[k] for k in LANGUAGES),
                   'coverage_and_ambiguities_verbatim': all(row[k] == ob[k] for k in ['declaration_coverage', 'possible_ambiguities']),
                   'title_within_200_characters': len(row['definition_title']) <= 200,
                   'original_artifact_unchanged': sha(row['provenance']['original_artifact']) == row['provenance']['original_artifact_sha256'],
                   'blind_input_hash_matches_original_and_wrapper': row['provenance']['input_sha256'] == reports[row['definition_name']]['blindReadback']['sha256'],
                   'required_template_keys_present': set(template['bundles'][0]).issubset(row),
                   'required_previous_schema_keys_present': set(previous['bundles'][0]).issubset(row)})
assert all(v is True for c in checks for k, v in c.items() if k != 'definition_name')
assert original_hashes == [sha(p) for p in original_paths]
assert [x['definition_name'] for x in serialized['bundles']] == [x['definition_name'] for x in template['bundles']]
save('validation.json', {
    'schema': 'reference-packet-field-readback-metadata-validation-v3',
    'passed': True, 'scope': 'Offline metadata consistency only',
    'bundle_count': len(checks), 'original_artifact_count': len(artifacts),
    'original_recorded_inputs_verified_count': len(dependencies_checked),
    'template_top_level_keys_present': set(template).issubset(serialized),
    'previous_accepted_schema_top_level_keys_present': set(previous).issubset(serialized),
    'canonical_bundle_order_matches_template': True,
    'source_context_kept_separate': True, 'checks': checks,
    'new_independent_readback_performed': False, 'proof_acceptance_performed': False,
    'compilation_performed': False, 'ci_used': False, 'api_used': False,
    'network_used': False, 'git_used': False, 'main_workspace_edited': False,
    'output_hashes': {name: sha(OUT / name) for name in [
        'blind-readbacks.json', 'input-manifest.json', 'review.json', 'source-context-references.json']},
})
print(json.dumps({'output': str(OUT / 'blind-readbacks.json'), 'bundles': len(checks),
                  'verified_original_inputs': len(dependencies_checked), 'passed': True}, ensure_ascii=False))
