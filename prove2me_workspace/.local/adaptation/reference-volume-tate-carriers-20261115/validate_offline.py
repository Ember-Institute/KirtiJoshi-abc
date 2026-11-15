#!/usr/bin/env python3
"""Offline draft checks with synthetic fixtures; never creates real ready/receipts."""
import sys
sys.dont_write_bytecode = True
import contextlib
import gzip
import importlib.util
import io
import json
from pathlib import Path
import runpy
import tempfile
from types import SimpleNamespace
from unittest.mock import patch

B = Path(__file__).resolve().parent
sys.path.insert(0, str(B))
import common


def load_module(name):
    spec = importlib.util.spec_from_file_location(name, B / (name + '.py'))
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def dump(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2) + '\n')


def main():
    for path in B.glob('*.py'):
        compile(path.read_bytes(), str(path), 'exec')
    checks = ['all_python_sources_parse']
    with tempfile.TemporaryDirectory(prefix='offline-fixtures-', dir=B) as temp:
        temp = Path(temp)
        root, work = temp / 'repo', temp / 'repo/work'
        unit = work / 'unit'
        unit.mkdir(parents=True)
        delivery = load_module('delivery')
        delivery.WORKSPACE, delivery.UNIT = work, unit
        bundles, rbrows, paperrows = [], [], []
        for i, (name, module) in enumerate(zip(delivery.NAMES, delivery.MODULES)):
            source = work / ('Definitions/Def_' + name + '.lean')
            source.parent.mkdir(exist_ok=True)
            code = '-- SYNTHETIC OFFLINE FIXTURE ' + str(i) + '\n'
            source.write_text(code)
            payload, blind = unit / (name + '-payload.json'), unit / (name + '-blind.txt')
            dump(payload, {'definition_name': name, 'code': code})
            blind.write_text(code)
            original = unit / (name + '-original.txt')
            original.write_text('SYNTHETIC TEST RESPONSE\n')
            bundles.append({'definitionName': name, 'path': str(source), 'sha256': delivery.sha(source),
                'payload': str(payload), 'payloadSha256': delivery.sha(payload),
                'blindReadback': {'path': str(blind), 'sha256': delivery.sha(blind)}})
            rbrows.append({'definition_name': name, 'source_sha256': delivery.sha(source),
                'definition_title': 'SYNTHETIC TITLE', 'source': 'SYNTHETIC SOURCE',
                'en': 'Synthetic formal text', 'zh-Hans': 'Synthetic text', 'ja': 'Synthetic text', 'passed': True,
                'provenance': {'fresh_context': True, 'input_only_formal_code': True, 'author_model': 'SYNTHETIC FIXTURE',
                    'original_artifact': str(original), 'original_artifact_sha256': delivery.sha(original),
                    'input_sha256': delivery.sha(blind)}})
            paperrows.append({'module': module, 'source_context_en': 'Synthetic source',
                'implementation_scope_en': 'Synthetic implementation', 'consumer_scope_en': 'Synthetic consumer',
                'quotation_ids': [], 'publication_markdown': 'SYNTHETIC PAPER FIXTURE'})
        report, rb, paper, ledger = [unit / n for n in ['wrapper.json', 'readbacks.json', 'paper.json', 'ledger.json']]
        dump(report, {'definitionsBundleCount': 5, 'bundles': bundles})
        dump(rb, {'passed': True, 'unconfirmed_chinese_terms_preserved': True, 'bundles': rbrows})
        dump(paper, {'schema': 'prove2me-reference-foundation-paper-context-v1', 'paper_sources': {},
                     'quotations': [], 'bundles': paperrows})
        dump(ledger, {'fixture_only': True})
        packet = delivery.prepare(report, rb, paper, ledger, unit / 'packet')
        assert len(packet['publications']) == 5 and all(r['payload']['private'] is True for r in packet['publications'])
        packet_path = unit / 'packet/packet.json'
        try:
            delivery.preflight(packet_path, B / 'delivery-ready.template.json')
            raise AssertionError('Incomplete template was accepted')
        except ValueError:
            pass
        checks += ['exact_five_bundle_prepare', 'incomplete_ready_template_rejected']
        by_name = {row['tag']: row for row in packet['publications']}

        class API:
            posts = 0
            def request(self, endpoint, payload=None, method='GET'):
                if method == 'POST':
                    assert endpoint == '/submit-definition' and payload['private'] is True
                    self.posts += 1
                    return {'job_id': 'fixture-job-' + payload['definition_name']}
                if endpoint.startswith('/missions?'):
                    return {'missions': [{'id': delivery.MISSION, 'visibility': 'private',
                        'creator': {'id': delivery.CREATOR}, 'main_theorem': {'theorem_id': delivery.ROOT}}]}
                if endpoint == '/theorems/' + delivery.ROOT:
                    return {'visibility': 'private', 'mathlib_rev': delivery.ENV}
                if endpoint == '/theorems/' + delivery.ROOT + '/graph':
                    return {'nodes': [], 'fixture_only': True}
                if endpoint.startswith('/publish-jobs/'):
                    job = endpoint.rsplit('/', 1)[1]
                    name = job.removeprefix('fixture-job-')
                    p = by_name[name]['payload']
                    return {'id': job, 'kind': 'definition', 'theorem_name': name, 'visibility': 'private',
                        'definitions': p['definition'], 'theorem_title': p['definition_title'],
                        'natural_language_statement': p['natural_language_statement'], 'source': p['source'],
                        'status': 'PUBLISHED', 'theorem_id': 'fixture-id-' + name}
                if endpoint.startswith('/definitions/'):
                    target = endpoint.rsplit('/', 1)[1]
                    name = target.removeprefix('fixture-id-')
                    return {**by_name[name]['payload'], 'definition_id': target, 'visibility': 'private',
                            'mathlib_rev': delivery.ENV}
                raise AssertionError(endpoint)

        api = API()
        with patch.object(delivery, 'load_api', return_value=api), patch.object(delivery, 'preflight', return_value=packet):
            journal = unit / 'journal'
            delivery.deliver(packet_path, unit / 'unused-ready', journal)
            assert api.posts == 5
            delivery.deliver(packet_path, unit / 'unused-ready', journal)
            assert api.posts == 5
            name = delivery.NAMES[0]
            (journal / (name + '-submit.json')).unlink()
            try:
                delivery.deliver(packet_path, unit / 'unused-ready', journal)
                raise AssertionError('Unknown POST outcome was silently resubmitted')
            except ValueError as e:
                assert 'Unknown POST outcome' in str(e)
            assert api.posts == 5
            delivery.reconcile(packet_path, unit / 'unused-ready', journal, name, 'fixture-job-' + name)
            delivery.deliver(packet_path, unit / 'unused-ready', journal)
            assert api.posts == 5
        checks += ['mock_delivery_exactly_five_posts', 'resume_no_duplicate_posts', 'lost_post_receipt_stops',
                   'get_only_reconciliation_then_resume', 'root_graph_unchanged']

        # The same offline helpers now point only to the synthetic evidence tree.
        common.ROOT, common.WORKSPACE, common.UNIT = root, work, unit
        common.PREFIX = unit.relative_to(root).as_posix()
        common.DEFINITIONS = [str((work / ('Definitions/Def_' + n + '.lean')).relative_to(root)) for n in common.NAMES]
        common.REGISTRY = work / 'registry.json'
        prior_registry = {'reference_source_preparation': {'scope': delivery.SCOPE,
            'canonicalC22Connected': False, 'definitions': [], 'packet_field_unit': {'preserve': 'exactly'}},
            'graph_state': {'preserve': ['all', 'states']}}
        dump(common.REGISTRY, prior_registry)
        plan = root / 'plan.md'
        plan.write_text('- [ ] S2-04 remains open\n')
        for name in ['kernel-result.json', 'production-result.json']:
            dump(unit / name, {'job_id': 'fixture-' + name, 'status': 'succeeded',
                'request': {'workspace': str(work), 'parameters': {}, 'worktree_manifest': {}},
                'result': {'exit_code': 0, 'cpu_time_seconds': 3, 'cpu_user_seconds': 2, 'cpu_system_seconds': 1},
                'resources': {'wall_time_seconds': 5, 'peak_rss_bytes': 1024,
                    'cpu_time_seconds': 3, 'cpu_user_seconds': 2, 'cpu_system_seconds': 1}})
        ready = unit / 'fixture-ready.json'
        dump(ready, {'ci_receipts': {'wrapped_kernel_type_identity': [str(unit / 'kernel-result.json')],
            **{g: [str(unit / 'production-result.json')] for g in ['checks_axioms', 'import_audit', 'act1scene1', 'axiom_audit']}}})
        journal_names = ['delivery-summary.json', 'published-ids.json', 'packet-binding.json',
            'root-graph-before.json', 'root-graph-after.json', 'mission-list-readback.json', 'mission-root-readback.json']
        journal_names += [n + s for n in delivery.NAMES for s in ['-intent.json', '-submit.json', '-result.json', '-published-item.json']]
        journal_names += [delivery.NAMES[0] + '-reconcile-readback.json']
        evidence_names = ['kernel-result.json', 'production-result.json'] + ['journal/' + n for n in journal_names]
        evidence_list = temp / 'finalize-evidence.json'
        dump(evidence_list, evidence_names)
        finalizer = load_module('finalize')
        # Replace only the preflight's already-tested contract, without fabricating actual acceptance.
        offline_delivery = {**delivery.__dict__, 'preflight': lambda *args: packet}
        with patch.object(finalizer.runpy, 'run_path', return_value=offline_delivery), patch.object(sys, 'argv', [
                'finalize.py', '--packet', str(packet_path), '--ready', str(ready), '--journal', str(journal),
                '--evidence-list', str(evidence_list), '--kernel-receipt', 'kernel-result.json',
                '--production-receipt', 'production-result.json', '--plan', str(plan), '--out', str(temp / 'finalization')]), contextlib.redirect_stdout(io.StringIO()):
            finalizer.main()
        candidate = common.read(temp / 'finalization/platform-node-registry.candidate.json')
        assert candidate['reference_source_preparation']['packet_field_unit'] == prior_registry['reference_source_preparation']['packet_field_unit']
        assert candidate['graph_state'] == prior_registry['graph_state']
        assert len(candidate['reference_source_preparation']['definitions']) == 5
        assert candidate['reference_source_preparation']['volume_tate_unit']['S2-04_completed'] is False
        assert common.read(common.REGISTRY) == prior_registry
        summary = common.read(temp / 'finalization/finalization-summary.json')
        assert summary['ci_attempts'][0]['cpu_time_seconds'] == 3
        assert summary['ci_attempts'][0]['peak_pss_bytes'] is None
        checks += ['finalizer_exact_candidate_and_prior_unit_preserved', 'finalizer_default_does_not_install',
                   'resource_cpu_sum_and_unknown_pss_retained']
        packager = load_module('package_evidence')
        (unit / 'small.diff').write_bytes(b'fixture diff\n')
        (unit / 'double-newline.txt').write_bytes(b'fixture\n\n')
        (unit / 'plain.txt').write_bytes(b'fixture\n')
        inputs = temp / 'inputs.json'
        extension = temp / 'reviewed-extension-actual-name.json'
        fixture_receipts = ['kernel-result.json', 'production-result.json'] + [
            'journal/' + n + suffix for n in delivery.NAMES for suffix in ['-submit.json', '-result.json']]
        dump(inputs, ['small.diff', 'double-newline.txt', *fixture_receipts])
        dump(extension, ['plain.txt'])
        before = {p: p.read_bytes() for p in [unit / 'small.diff', unit / 'double-newline.txt', unit / 'plain.txt']}
        for i in [1, 2]:
            with patch.object(sys, 'argv', ['package_evidence.py', '--input-list', str(inputs),
                    '--extra-list', str(extension), '--out', str(temp / ('review-' + str(i)))]), contextlib.redirect_stdout(io.StringIO()):
                packager.main()
        out1, out2 = [temp / ('review-' + str(i)) / common.PREFIX for i in [1, 2]]
        assert (out1 / extension.name).read_bytes() == extension.read_bytes()
        assert not (out1 / 'post-delivery-evidence-allowlist.json').exists()
        for name in ['small.diff', 'double-newline.txt']:
            a, b = [o / ('archives/' + name + '.gz') for o in [out1, out2]]
            assert a.read_bytes() == b.read_bytes() and gzip.decompress(a.read_bytes()) == (unit / name).read_bytes()
        assert all(p.read_bytes() == data for p, data in before.items())
        checks += ['extension_filename_preserved', 'diff_and_double_newline_gzip',
                   'gzip_deterministic_and_lossless', 'source_originals_unchanged']
        # Exercise ready assembly with a non-default successful kernel path and
        # this unit's list-valued paper validation. Every receipt remains a fixture.
        ready_helper = load_module('prepare_ready')
        ready_helper.delivery = delivery
        fixture_inventory = {'modules': [{'module': m, 'declarations': [
            {'selected': j < 20} for j in range(31 if i == 0 else 29)]}
            for i, m in enumerate(delivery.MODULES)]}
        dump(unit / 'inventory.json', fixture_inventory)
        dump(unit / 'actual-retry-audit/audit.json', {'requiredComparedCount': 100,
            'configuration': {'inventorySha256': delivery.sha(unit / 'inventory.json'),
                'expectedRecordCount': 147, 'expectedSelectedCount': 100},
            'hasSorryAx': False, 'allOwnedTypeValueClosuresStandardAxiomsOnly': True,
            'ownedDeclarations': [{'hasSorryAx': False}]})
        validation = {'status': 'passed', 'checks': [{'check': 'fixture_only', 'passed': True}]}
        paper_value = delivery.read(paper)
        paper_value['validation'] = validation
        dump(paper, paper_value)
        dump(unit / 'paper-validation.json', validation)
        dump(unit / 'review.json', {'blocking_findings': [], 'status': 'passed', 'frozen': True,
            'frozen_evidence_sha256': {}, 'definitions_sha256': packet['source_sha256']})
        dump(unit / 'scope.json', {'passed': True, 'fixture_only': True})
        (work / 'FixtureAudit.lean').write_text('-- fixture only\n')
        def ci_receipt(name, source, task_type='leaf'):
            dump(unit / name, {'job_id': 'synthetic-ci-' + name, 'status': 'succeeded',
                'request': {'language': 'lean', 'workspace': str(work), 'exclusive': True,
                    'task_type': task_type, 'target': 'file', 'parameters': {'source': source},
                    'worktree_manifest': {'source_sha256': delivery.sha(work / source)}},
                'result': {'exit_code': 0, 'actual_arguments': ['lean', source],
                    'snapshot': {'workspace_mode': 'exclusive_worktree', 'snapshot_id': None},
                    'review': {'passed': True}}, 'resources': {'peak_rss_bytes': 1024}})
        ci_receipt('actual-retry-success-result.json', 'FixtureAudit.lean', 'review')
        ci_receipt('actual-production-result.json', 'FixtureAudit.lean', 'review')
        leaves = []
        for i, source in enumerate(packet['source_sha256']):
            name = 'fixture-leaf-' + str(i) + '-result.json'
            ci_receipt(name, source)
            leaves.append(name)
        input_config = unit / 'ready-inputs.json'
        dump(input_config, {'reviewed': True, 'inventory': 'inventory.json', 'wrapper_report': report.name,
            'blind_readbacks': rb.name, 'paper_context': paper.name, 'paper_validation': 'paper-validation.json',
            'source_ledger': ledger.name, 'prepublication_review': 'review.json',
            'production_receipt': 'actual-production-result.json', 'leaf_receipts': leaves,
            'gate_evidence': {g: ['scope.json'] for g in ['independent_readbacks', 'source_ledger_consumers', 'existing_mission_scope']}})
        with (patch.object(ready_helper.subprocess, 'run', return_value=SimpleNamespace(returncode=0, stdout='', stderr='')),
                patch.object(sys, 'argv', ['prepare_ready.py', '--inputs', str(input_config),
                    '--kernel-receipt', 'actual-retry-success-result.json', '--kernel-audit', 'actual-retry-audit/audit.json']),
                contextlib.redirect_stdout(io.StringIO())):
            ready_helper.main()
        assembled = delivery.read(unit / 'delivery/ready.json')
        assert assembled['ci_receipts']['wrapped_kernel_type_identity'] == [str(unit / 'actual-retry-success-result.json')]
        assert not (unit / 'delivery/ready.candidate.json').exists()
        checks += ['ready_dynamic_kernel_retry_path_and_paper_list', 'ready_full_preflight_on_synthetic_receipts']
    result = {'scope': 'synthetic offline draft validation only', 'passed': True, 'checks': checks,
              'ci_compilation_run': False, 'api_network_run': False, 'git_run': False,
              'actual_ready_or_publication_receipts_created': False}
    dump(B / 'delivery-offline-validation.json', result)
    print(json.dumps(result, ensure_ascii=False, indent=2))


if __name__ == '__main__':
    main()
