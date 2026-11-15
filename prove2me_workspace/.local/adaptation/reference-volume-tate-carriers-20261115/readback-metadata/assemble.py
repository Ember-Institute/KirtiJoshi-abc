#!/usr/bin/env python3
"""Offline metadata assembly helpers; no readback text is generated here."""
import hashlib
import json
import argparse
from pathlib import Path

OUT = Path(__file__).resolve().parent
ROOT = Path('/home/admin-wsl/Coq/abc')
W = ROOT / 'prove2me_workspace'
B = W / '.local/adaptation/reference-volume-tate-carriers-20261115'
TEMPLATE = B / 'delivery-blind-readbacks.template.json'
REPORT = B / 'generated-wrapped/foundation-wrapper-report.json'
LEDGER = B / 'SOURCE_LEDGER.json'
ORIGINALS = [B / 'blind-originals/volume.json', B / 'blind-originals/tate.json']
PREVIOUS = W / '.local/adaptation/reference-packet-field-carriers-20261115/blind-readbacks.json'
LANGUAGES = ('en', 'zh-Hans', 'ja')
REVIEWERS = ['/root/volume_tate_blind_volume_v4', '/root/volume_tate_blind_tate_v4']
TITLES = [
    'Container hull systems — 容器包络系统 — コンテナの包絡系',
    'Logarithmic volume data and aggregates — 对数体积数据与汇总 — 対数体積データと集計',
    'Coprimality and Tate parameters with a positive integer — 互素性与附正整数的 Tate 参数 — 互いに素な条件と正整数付き Tate パラメータ',
    'Series and a Weierstrass equation from Tate parameters — Tate 参数的级数与 Weierstrass 方程 — Tate パラメータによる級数と Weierstrass 方程式',
    'Norm exponents and Tate parameters with a positive integer — 范数指数与附正整数 Tate 参数的构造 — ノルムの指数と正整数付き Tate パラメータ',
]

def read(path):
    return json.loads(Path(path).read_text(encoding='utf-8'))

def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def save(name, value):
    (OUT / name).write_text(json.dumps(value, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')

def record(path, role):
    return {'path': str(path), 'sha256': sha(path), 'role': role}

def check_wrappers():
    template, report = read(TEMPLATE), read(REPORT)
    names = [x['definition_name'] for x in template['bundles']]
    reports = {x['definitionName']: x for x in report['bundles']}
    assert len(names) == len(reports) == 5 and set(names) == set(reports)
    checks = []
    for name in names:
        row = reports[name]
        installed = W / 'Definitions' / ('Def_' + name + '.lean')
        generated = Path(row['path'])
        blind = Path(row['blindReadback']['path'])
        assert sha(installed) == sha(generated) == row['sha256']
        assert installed.read_bytes() == generated.read_bytes()
        assert sha(blind) == row['blindReadback']['sha256']
        checks.append({'definition_name': name,
                       'installed': record(installed, 'actual_installed_definition'),
                       'generated': record(generated, 'generated_definition'),
                       'blind': record(blind, 'authenticated_blind_input'),
                       'installed_generated_report_match': True})
    return template, reports, checks

def require_actual_originals_and_final_ledger():
    missing = [str(p) for p in [*ORIGINALS, LEDGER] if not p.is_file()]
    if missing:
        raise SystemExit('Final assembly is pending actual original artifacts and final ledger: ' + ', '.join(missing))
    return [read(p) for p in ORIGINALS], read(LEDGER)

def prepare():
    template, reports, checks = check_wrappers()
    save('prepared-wrapper-validation.json', {
        'schema': 'reference-volume-tate-readback-metadata-preparation-v4',
        'status': 'wrappers-checked-awaiting-actual-originals-and-final-ledger',
        'template': record(TEMPLATE, 'required_delivery_schema'),
        'report': record(REPORT, 'wrapper_and_blind_input_hashes'),
        'checks': checks,
        'originals_expected': [str(p) for p in ORIGINALS],
        'reviewer_contexts_expected': REVIEWERS,
        'final_source_ledger_expected': str(LEDGER),
        'editorial_titles': dict(zip([x['definition_name'] for x in template['bundles']], TITLES)),
        'readback_text_generated': False, 'final_packet_generated': False,
        'uniformizer_policy': 'Preserve 【待定译名：uniformizer】 verbatim if present. No candidate substitution.',
        'disclosure_policy': 'Preserve exact original disclosures, including incidental pinned Mathlib documentation lines and corrected prerequisite paths. Do not recast this as no comments ever seen.',
    })
    save('required-delivery-schema.json', {
        'schema': 'reference-volume-tate-readback-metadata-required-fields-v4',
        'template': record(TEMPLATE, 'required_delivery_schema'),
        'required_top_level_fields': list(template),
        'required_bundle_fields': list(template['bundles'][0]),
        'required_bundle_provenance_fields': list(template['bundles'][0]['provenance']),
        'required_independent_review_fields': list(template['independent_reviews'][0]),
        'bundle_order': [x['definition_name'] for x in template['bundles']],
        'original_distribution': [2, 3],
        'readback_copy_policy': 'Copy actual original EN/ZH/JA, coverage and ambiguities verbatim. Record original bundle-name mapping and complete original metadata.',
        'source_policy': 'Use only the final SOURCE_LEDGER sourceURL for source. Keep effective/upstream anchors and source context separate.',
        'acceptance_scope': 'Metadata consistency only; no fresh readback or proof acceptance by assembler.',
    })
    print(json.dumps({'wrapper_checks_passed': len(checks), 'final_packet_generated': False,
                      'status': 'awaiting-parent-notification-of-originals-and-final-ledger'}, ensure_ascii=False))

def complete():
    """Call only after the coordinating agent confirms final originals/ledger."""
    template, reports, wrapper_checks = check_wrappers()
    originals, ledger_document = require_actual_originals_and_final_ledger()
    ledger = {x['producer']: x for x in ledger_document['entries']}
    assert sha(ledger_document['wrapperReport']['path']) == ledger_document['wrapperReport']['sha256'] == sha(REPORT)
    correspondence = ledger_document['acceptedCompilerCorrespondence']
    assert sha(correspondence['path']) == correspondence['sha256']
    names = [x['definition_name'] for x in template['bundles']]
    assert set(ledger) == set(names)
    assert [len(x['bundles']) for x in originals] == [2, 3]
    assert [x['definition_name'] for o in originals for x in o['bundles']] == names
    original_hashes = [sha(p) for p in ORIGINALS]
    artifacts, historical_artifacts, verified_inputs, inputs = [], [], [], []
    for path, original, reviewer in zip(ORIGINALS, originals, REVIEWERS):
        assert original['fresh_context'] is True and original['input_only_formal_code'] is True
        assert original['author_model'] == 'gpt-6.1-sol'
        frozen = OUT / 'originals' / path.name
        frozen.parent.mkdir(exist_ok=True)
        frozen.write_bytes(path.read_bytes())
        assert sha(frozen) == sha(path)
        metadata = {k: v for k, v in original.items() if k != 'bundles'}
        artifacts.append({**record(path, 'immutable_final_original_blind_readback'),
                          'reviewer_id': reviewer, 'frozen_copy': str(frozen),
                          'metadata_verbatim': metadata})
        revision = original['provenance'].get('revision')
        if revision:
            historical_path = Path(revision['original_artifact'])
            assert sha(historical_path) == revision['original_artifact_sha256']
            historical = read(historical_path)
            assert original['bundles'] == historical['bundles'], 'Revision changed readback content'
            integrated_historical = B / 'blind-originals/tate-v1.json'
            assert sha(integrated_historical) == sha(historical_path)
            frozen_historical = OUT / 'originals/tate-v1.json'
            frozen_historical.write_bytes(historical_path.read_bytes())
            historical_artifacts.append({**record(historical_path, 'historical_original_readback_v1'),
                                         'integrated_copy': str(integrated_historical),
                                         'integrated_copy_sha256': sha(integrated_historical),
                                         'frozen_copy': str(frozen_historical),
                                         'superseding_final_artifact': str(path),
                                         'bundles_verbatim_in_final_revision': True,
                                         'input_status': 'Historical input manifest is preserved as recorded; its old Weierstrass input is not rebound to the current file or revalidated as a current input.',
                                         'metadata_verbatim': {k: v for k, v in historical.items() if k != 'bundles'}})
        for row in original['inputs']:
            actual = sha(row['path'])
            assert actual == row['sha256'], ('Stale original input', path, row['path'])
            verified_inputs.append({'original_artifact': str(path), 'recorded_input': row,
                                    'actual_sha256': actual, 'matches': True})
    packet = {
        'schema': 'reference-volume-tate-reviewed-blind-readbacks-v4',
        'passed': True,
        'acceptance_scope': 'Offline metadata consistency only. Existing independent readbacks are attributed to their original contexts. This assembly performs no new independent readback, proof acceptance, compilation, or publication.',
        'unconfirmed_chinese_terms_preserved': True,
        'unconfirmed_terms_policy': 'Preserve all original pending Chinese term markers, including 【待定译名：uniformizer】, without candidate substitution. User-confirmed capsule=标签集, procession=标签集递增族, hull=包络. All original EN/ZH/JA strings remain verbatim; pending terminology does not block code work.',
        'bundles': [], 'independent_reviews': [],
    }
    for artifact, original, reviewer, template_review in zip(artifacts, originals, REVIEWERS, template['independent_reviews']):
        review = {
            'reviewer_id': reviewer, 'author_model': original['author_model'],
            'actual_model': original['actual_model'],
            'fresh_context': original['fresh_context'],
            'input_only_formal_code': original['input_only_formal_code'],
            'original_artifact': artifact['path'], 'original_artifact_sha256': artifact['sha256'],
            'passed': True, 'acceptance_scope': 'Original identity/input hash consistency only; not a proof-correctness judgment.',
            'original_metadata_verbatim': artifact['metadata_verbatim'],
            'input_only_formal_code_semantics': 'Copied original flag describes mathematical evidence. Exact original disclosures qualify incidental Mathlib documentation output; no claim that comments were never seen is added.',
        }
        assert set(template_review).issubset(review)
        packet['independent_reviews'].append(review)
    for index, (template_row, title) in enumerate(zip(template['bundles'], TITLES)):
        group = 0 if index < 2 else 1
        ordinal = index if group == 0 else index - 2
        original, path = originals[group], ORIGINALS[group]
        ob = original['bundles'][ordinal]
        name = template_row['definition_name']
        report, entry = reports[name], ledger[name]
        assert entry['originalModule'] == report['module'], ('Module identity differs', name)
        assert entry['sourceProvenance']['sourceSha256'] == report['adaptationProvenance']['sourceSha256']
        effective = entry['sourceProvenance']['frozenEffectiveSource']
        assert sha(effective['path']) == effective['sha256'] == entry['sourceProvenance']['sourceSha256']
        installed = W / 'Definitions' / ('Def_' + name + '.lean')
        blind = Path(report['blindReadback']['path'])
        actual = sha(installed)
        assert actual == entry['wrappedSourceSha256'] == report['sha256']
        original_input = next(x for x in original['inputs'] if x['path'] == str(blind))
        assert original_input['sha256'] == sha(blind) == report['blindReadback']['sha256'], ('Stale readback binding', name)
        assert ob['definition_name'] == name
        provenance = {
            'author_model': original['author_model'], 'actual_model': original['actual_model'],
            'fresh_context': original['fresh_context'],
            'input_only_formal_code': original['input_only_formal_code'],
            'input_sha256': sha(blind), 'original_artifact': str(path),
            'original_artifact_sha256': sha(path), 'original_bundle_index': ordinal,
            'original_definition_name': ob['definition_name'], 'reviewer_id': REVIEWERS[group],
            'original_blind_input': original_input,
            'original_provenance_verbatim': original['provenance'],
            'translation_provenance': 'The original provenance is retained verbatim above: Chinese and Japanese translate this original English and are not separate independent audits.',
            'source_semantics': 'Final source context remains separate. The original blind input hash must match both the current wrapper report and actual file; historical Weierstrass v1 cannot be silently rebound.',
            'effective_module_source_sha256': entry['sourceProvenance']['sourceSha256'],
            'upstream_module_source_sha256': entry['sourceProvenance']['upstreamSourceSha256'],
            'title_provenance': 'Editorial trilingual title based on actual formal declarations; no existing canonical title is claimed. No unresolved uniformizer term is translated in these titles.',
            'metadata_assembly': 'Metadata-only assembly. Original readback strings and optional proof notes are copied without editorial correction.',
        }
        bundle = {'definition_name': name, 'source_sha256': actual, 'definition_title': title,
                  'source': entry['sourceURL'], **{lang: ob[lang] for lang in LANGUAGES},
                  'passed': True, 'declaration_coverage': ob['declaration_coverage'],
                  'possible_ambiguities': ob['possible_ambiguities'],
                  'editorial_changes': [], 'provenance': provenance}
        if 'proof_notes' in ob:
            bundle['proof_notes'] = ob['proof_notes']
        assert len(title) <= 200
        assert set(template_row).issubset(bundle)
        assert set(template_row['provenance']).issubset(provenance)
        assert all(isinstance(bundle[k], str) and bundle[k].strip() for k in [*LANGUAGES, 'source', 'definition_title'])
        packet['bundles'].append(bundle)
    inputs = [record(ROOT / 'AGENTS.md', 'workspace_instructions'),
              record(ROOT / 'docs/三语自然语言读回原则.md', 'readback_rules'),
              record(ROOT / 'docs/三语术语名词关键对照.md', 'terminology_rules'),
              record(TEMPLATE, 'delivery_schema_template'), record(REPORT, 'wrapper_and_blind_input_hashes'),
              record(LEDGER, 'final_source_ledger'), record(PREVIOUS, 'previous_accepted_schema'),
              record(correspondence['path'], 'ledger_referenced_compiler_correspondence')]
    for row in wrapper_checks:
        inputs += [row['installed'], row['generated'], row['blind']]
    for name in names:
        provenance = ledger[name]['sourceProvenance']
        inputs.append(record(provenance['frozenEffectiveSource']['path'], 'frozen_effective_module_source'))
        if 'frozenUpstreamSource' in provenance:
            upstream = provenance['frozenUpstreamSource']
            assert sha(upstream['path']) == upstream['sha256'] == provenance['upstreamSourceSha256']
            inputs.append(record(upstream['path'], 'frozen_upstream_module_source'))
    source_context = {
        'schema': 'reference-volume-tate-source-context-references-v4',
        'scope': 'Final ledger source metadata, kept separate from original blind readbacks.',
        'ledger': record(LEDGER, 'final_source_ledger'),
        'ledger_references_verbatim': {k: ledger_document[k] for k in ['wrapperReport', 'acceptedCompilerCorrespondence']},
        'source_fields': [{k: v for k, v in ledger[name].items()
                           if any(t in k.lower() for t in ['source', 'anchor', 'override', 'scope', 'provenance'])
                           or k in ['producer', 'originalModule', 'wrappedSourceSha256', 'rootGraphMembership', 'canonicalC22Connected']}
                          for name in names],
    }
    previous = read(PREVIOUS)
    assert set(previous).issubset(packet) and set(template).issubset(packet)
    assert all(set(previous['bundles'][0]).issubset(x) for x in packet['bundles'])
    save('blind-readbacks.json', packet)
    save('source-context-references.json', source_context)
    save('input-manifest.json', {
        'schema': 'reference-volume-tate-readback-metadata-inputs-v4',
        'assembly_role': 'metadata_only', 'inputs': inputs, 'original_artifacts': artifacts,
        'historical_original_artifacts': historical_artifacts,
        'original_recorded_inputs_checked': verified_inputs,
        'final_ledger_selection': 'Used after the coordinating agent confirmed the final source ledger. No source URL was inferred from historical anchors.',
        'terminology': {'capsule': '标签集', 'procession': '标签集递增族', 'hull': '包络',
                        'uniformizer': '【待定译名：uniformizer】'},
    })
    save('review.json', {
        'schema': 'reference-volume-tate-readback-metadata-review-v4',
        'review_kind': 'additive_metadata_review_only', 'original_readback_text_changes': [],
        'translation_corrections': [], 'new_independent_readback_performed': False,
        'proof_acceptance_performed': False,
        'disclosures': 'Complete original provenance, including incidental generic Mathlib documentation output and corrected allowed prerequisite paths, is preserved verbatim in packet and manifest.',
        'runtime_model_disclosure': 'author_model remains the original task-designated label; actual_model=null is preserved. No runtime identity is invented.',
        'pending_terms_policy': 'Preserve every original marker verbatim; no uniformizer candidate substitution.',
        'weierstrass_version_policy': 'Only the final original whose input hash matches current explicit-end wrapper framing can be assembled. Historical v1 is not used as evidence for a changed hash.',
        'title_decision': 'Titles are content-grounded editorial metadata with explicit provenance.',
    })
    checks = []
    serialized = read(OUT / 'blind-readbacks.json')
    for row in serialized['bundles']:
        name, provenance = row['definition_name'], row['provenance']
        original = read(provenance['original_artifact'])
        ob = original['bundles'][provenance['original_bundle_index']]
        copied_keys = [*LANGUAGES, 'declaration_coverage', 'possible_ambiguities']
        if 'proof_notes' in ob:
            copied_keys.append('proof_notes')
        checks.append({'definition_name': name,
                       'module_identity_matches_final_ledger_and_report': ledger[name]['originalModule'] == reports[name]['module'],
                       'module_source_hash_matches_final_ledger_and_report': row['provenance']['effective_module_source_sha256'] == ledger[name]['sourceProvenance']['sourceSha256'] == reports[name]['adaptationProvenance']['sourceSha256'],
                       'source_url_matches_final_ledger': row['source'] == ledger[name]['sourceURL'],
                       'source_hash_matches_installed_generated_report_ledger': row['source_sha256'] == sha(W / 'Definitions' / ('Def_' + name + '.lean')) == sha(reports[name]['path']) == reports[name]['sha256'] == ledger[name]['wrappedSourceSha256'],
                       'original_text_and_coverage_verbatim': all(row[k] == ob[k] for k in copied_keys),
                       'pending_marker_occurrences_preserved': all(row[k].count('【待定译名：') == ob[k].count('【待定译名：') for k in LANGUAGES),
                       'original_provenance_verbatim': provenance['original_provenance_verbatim'] == original['provenance'],
                       'original_artifact_unchanged': sha(provenance['original_artifact']) == provenance['original_artifact_sha256'],
                       'blind_input_matches_original_report_actual_file': provenance['input_sha256'] == reports[name]['blindReadback']['sha256'] == sha(reports[name]['blindReadback']['path']),
                       'title_within_200_characters': len(row['definition_title']) <= 200})
    assert all(v is True for row in checks for k, v in row.items() if k != 'definition_name')
    assert original_hashes == [sha(p) for p in ORIGINALS]
    save('validation.json', {
        'schema': 'reference-volume-tate-readback-metadata-validation-v4',
        'passed': True, 'scope': 'Offline metadata consistency only',
        'bundle_count': 5, 'original_artifact_count': 2,
        'original_recorded_inputs_verified_count': len(verified_inputs),
        'historical_original_artifact_count': len(historical_artifacts),
        'tate_v2_is_same_reviewer_revision_not_second_fresh_audit': True,
        'template_top_level_keys_present': set(template).issubset(serialized),
        'previous_accepted_schema_top_level_keys_present': set(previous).issubset(serialized),
        'distinct_original_reviewer_contexts': len({r['reviewer_id'] for r in serialized['independent_reviews']}) == 2,
        'source_context_kept_separate': True, 'checks': checks,
        'new_independent_readback_performed': False, 'proof_acceptance_performed': False,
        'compilation_performed': False, 'ci_used': False, 'api_used': False,
        'network_used': False, 'git_used': False, 'main_workspace_edited': False,
        'output_hashes': {name: sha(OUT / name) for name in [
            'blind-readbacks.json', 'input-manifest.json', 'review.json', 'source-context-references.json']},
    })
    print(json.dumps({'output': str(OUT / 'blind-readbacks.json'), 'passed': True,
                      'bundles': 5, 'original_inputs_verified': len(verified_inputs)}, ensure_ascii=False))

if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--assemble', action='store_true', help='Use only after final-ready notification from coordinating agent')
    options = parser.parse_args()
    if options.assemble:
        complete()
    else:
        prepare()
