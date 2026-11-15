#!/usr/bin/env python3
"""Bind reviewed actual evidence; no compilation, API or publication occurs."""
import sys
sys.dont_write_bytecode = True
from pathlib import Path
import argparse
import importlib.util
import json
import subprocess
from common import UNIT, WORKSPACE, ROOT, MODULES, exact_path, require

B = UNIT
spec = importlib.util.spec_from_file_location('volume_tate_delivery', Path(__file__).with_name('delivery.py'))
delivery = importlib.util.module_from_spec(spec)
spec.loader.exec_module(delivery)


def validate_kernel_coverage(audit, declarations):
    """Check the two exact proof resolutions without inventing target identities."""
    selected = {d['name'] for d in declarations if d['selected'] is True}
    proof_names = {n + '._proof_1' for n in [
        'TateCurvesTheta.OrderedTateParameter.decidable', 'TateCurvesTheta.PrimeToOrder.decidable']}
    parents = {n.removesuffix('._proof_1') for n in proof_names}
    target_only = {'AbcAdaptation.Reference.' + n + '._aux_1' for n in parents}
    config = audit['configuration']
    # Preserve the historical source-obligation meaning of requiredComparedCount.
    # Named target identities and genuine proof resolutions have explicit dimensions.
    named_count = audit['requiredNamedComparedCount']
    proof_count = audit['requiredProofValueResolutionCount']
    source_count = audit['requiredSourceDeclarationCount']
    resolved_count = audit['requiredResolvedCount']
    require(source_count == resolved_count == len(selected) == 100 and
            audit['requiredComparedCount'] == source_count and named_count == 98 and proof_count == 2 and
            audit['requiredEliminatedInternalProofCount'] == proof_count and
            named_count + proof_count == resolved_count,
            'Kernel source/named/proof coverage differs')
    require(config['expectedNamedSelectedCount'] == named_count and
            config['expectedProofValueResolutionCount'] == proof_count, 'Kernel configured resolution counts differ')
    comparisons = audit['comparisons']
    names = [r['original'] for r in comparisons]
    require(len(names) == len(set(names)) and selected - proof_names <= set(names) and
            not proof_names & set(names), 'Selected named/proof identities differ')
    require(sum(r['sourceRecord']['selected'] is True for r in comparisons) == named_count,
            'Named comparison rows do not cover 98 selections')
    resolutions = audit['proofValueResolutions']
    require(len(resolutions) == 2 and {r['original'] for r in resolutions} == proof_names,
            'Exact source proof resolutions differ')
    configured = {r['original']: r for r in config['proofValueResolutions']}
    require(len(config['proofValueResolutions']) == 2 and set(configured) == proof_names,
            'Configured genuine source proof identities differ')
    standard_axioms = {'propext', 'Classical.choice', 'Quot.sound'}
    def expression(value):
        return isinstance(value, dict) and bool(value)
    for row in resolutions:
        binding = configured[row['original']]
        record = row['sourceRecord']
        require(row['resolution'] == 'genuine-exported-original-proof-value' and
                row['standaloneTargetIdentity'] is None and binding['standaloneTargetIdentity'] is None and
                record == binding['sourceRecord'] and record['name'] == row['original'] and
                record['constantKind'] == 'theorem' and record['selected'] is True and
                record['isProposition'] is True and record['isInstance'] is False,
                'Proof resolution does not bind the exact genuine source theorem')
        require(all(row[k] is True for k in ['originalTypeBinderInfoPreserved', 'exactOriginalTypeKernelChecked',
            'genuineOriginalValueInhabitsExactOriginalType', 'parentWholeValueEqualityRequired',
            'expandedDependenciesHaveAllowedOwners']) and row['hasSorryAx'] is False and
            expression(row['expandedType']) and expression(row['expandedValue']) and
            expression(record['elaboratedExpr']) and expression(record['valueExpr']) and
            set(row['expandedTypeAxioms']) <= standard_axioms and set(row['expandedValueAxioms']) <= standard_axioms,
            'Genuine source proof type/value evidence is incomplete')
        require(row['parentOriginal'] == binding['parentOriginal'] == row['original'].removesuffix('._proof_1'),
                'Proof resolution parent differs')
        parent = next(r for r in comparisons if r['original'] == row['parentOriginal'])
        require(parent['computationalValueEqualityChecked'] is True and
                (parent['kernelValueEqual'] is True or parent['kernelPropositionalValueEquality'] is True),
                'Resolved proof parent lacks complete kernel value equality')
        if parent['kernelValueEqual'] is not True:
            evidence = parent['propositionalValueEqualityEvidence']
            require(evidence['kernelCheckedPropositionalValueEquality'] is True and
                    evidence['sourceBooleanComputationTransported'] is True and
                    evidence['classicalDecisionSubstitution'] is False and evidence['hasSorryAx'] is False and
                    set(evidence['axioms']) <= standard_axioms and all(expression(evidence[k]) for k in [
                        'exactFullValueEquality', 'kernelCheckedEqualityProof',
                        'kernelCheckedDecisionBitEquality', 'sourceTargetDecisionBitEquation']),
                    'Parent full-value or decision-bit equality evidence is incomplete')
    owned = audit['ownedDeclarations']
    require(len(owned) == 100 and len({r['name'] for r in owned}) == 100 and
            set(audit['targetOnlyCompilerDeclarations']) == target_only and
            set(config['expectedTargetOnlyCompilerDeclarations']) == target_only and
            len(audit['targetOnlyCompilerDeclarations']) == 2 and target_only <= {r['name'] for r in owned},
            'Actual owned/target-only compiler declarations differ')
    transport = audit['standardRepresentationTransport']
    compatibility = config['decidableStandardCompatibility']
    require(transport['schema'] == 'decidable435-to433-representation-transport-v1' and
            transport['boundCompatibilityEvidence'] == compatibility and
            transport['genuineSourceFacts'] == compatibility['sourceFacts']['contents'] and
            transport['sourceFactFile'] == compatibility['sourceFacts']['path'] and
            transport['sourceConstructor'] == 'Decidable.intro' and
            all(transport[k] is True for k in ['exactConstructorTypeKernelChecked',
                'exactConstructorTypeBinderInfoPreserved', 'originalDecisionBitPreserved']) and
            transport['classicalDecisionSubstitution'] is False and transport['hasSorryAx'] is False and
            set(transport['axioms']) <= standard_axioms and all(expression(transport[k]) for k in [
                'translatedConstructorType', 'sourceBoolReflectsBody', 'inlineConstructorTransport',
                'kernelCheckedDecisionBitProof', 'decisionBitEquation']),
            'Decidable representation or original Boolean bit evidence is incomplete')
    for support in transport['missingStandardSupportExpansions']:
        require(support['standaloneTargetIdentity'] is None and support['exactOriginalTypeKernelChecked'] is True and
                support['hasSorryAx'] is False and expression(support['expandedValue']) and
                set(support['expandedAxioms']) <= standard_axioms and
                support['sourceRecord']['kind'] in {'definition', 'theorem'} and
                expression(support['sourceRecord']['valueExpr']), 'Genuine absent standard support evidence is incomplete')
    evidence_paths = set()
    for key in ['sourceFacts', 'sourceReceipt', 'platformFacts', 'platformReceipt', 'supportClosure', 'supportReceipt']:
        binding = compatibility[key]
        actual = Path(binding['path'])
        require(delivery.sha(actual) == binding['sha256'] and delivery.read(actual) == binding['contents'],
                'Bound Decidable compatibility input changed: ' + key)
        evidence_paths.add(actual)
    for key, job_id in [('sourceReceipt', 'ci-013901-2c932c62'),
                        ('platformReceipt', 'ci-013907-b9f0843a'), ('supportReceipt', 'ci-013924-3a1c20d9')]:
        receipt = compatibility[key]['contents']
        snapshot = receipt['result']['snapshot']
        require(receipt['job_id'] == job_id and receipt['status'] == 'succeeded' and
                receipt['result']['exit_code'] == 0 and snapshot['workspace_mode'] == 'exclusive_worktree' and
                snapshot['snapshot_id'] is None,
                'Genuine Decidable query receipt differs: ' + key)
    return evidence_paths


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--inputs', required=True, type=Path,
                        help='Completed reviewed ready-inputs JSON; paths relative to this unit')
    parser.add_argument('--kernel-receipt', required=True,
                        help='Actual successful kernel receipt, relative to this unit')
    parser.add_argument('--kernel-audit', required=True,
                        help='Actual JSON emitted by that successful audit, relative to this unit')
    args = parser.parse_args()
    load, sha = delivery.read, delivery.sha
    config = load(args.inputs)
    require(config['reviewed'] is True, 'Ready input selection is not reviewed')
    path = lambda n: exact_path(B, n)
    audit_path, kernel = path(args.kernel_audit), path(args.kernel_receipt)
    audit = load(audit_path)
    inv_path = path(config['inventory'])
    inv = load(inv_path)
    require({m['module'] for m in inv['modules']} == set(MODULES), 'Inventory module set differs')
    declarations = [d for m in inv['modules'] for d in m['declarations']]
    selected_count = sum(d['selected'] is True for d in declarations)
    require((len(declarations), selected_count) == (147, 100), 'Reviewed inventory count changed')
    compatibility_paths = validate_kernel_coverage(audit, declarations)
    require(audit['configuration']['inventorySha256'] == sha(inv_path), 'Kernel inventory is stale')
    require(audit['configuration']['expectedRecordCount'] == len(declarations) and
            audit['configuration']['expectedSelectedCount'] == selected_count, 'Kernel inventory configuration differs')
    require(audit['hasSorryAx'] is False and audit['allOwnedTypeValueClosuresStandardAxiomsOnly'] is True,
            'Kernel axiom closure not accepted')
    require(bool(audit['ownedDeclarations']) and all(d['hasSorryAx'] is False for d in audit['ownedDeclarations']),
            'Owned declaration axiom audit is incomplete')
    review_path = path(config['prepublication_review'])
    review = load(review_path)
    require(review['blocking_findings'] == [] and review['status'] == 'passed' and review['frozen'] is True,
            'Final frozen review is incomplete')
    require(all(sha(p) == digest for p, digest in review['frozen_evidence_sha256'].items()), 'Frozen evidence changed')
    blind_path = path(config['blind_readbacks'])
    require(load(blind_path)['passed'] is True, 'Actual blind readback is incomplete')
    paper_path, paper_check_path = path(config['paper_context']), path(config['paper_validation'])
    paper, paper_check = load(paper_path), load(paper_check_path)
    require(paper_check['status'] == 'passed' and bool(paper_check['checks']) and
            all(c['passed'] is True for c in paper_check['checks']), 'Paper artifact consistency review is incomplete')
    require(paper['validation'] == paper_check, 'Paper validation and context differ')
    destination = B / 'delivery'
    packet = delivery.prepare(path(config['wrapper_report']), blind_path, paper_path,
                              path(config['source_ledger']), destination)
    require(review['definitions_sha256'] == packet['source_sha256'], 'Reviewed Definition hashes differ')
    diff = subprocess.run(['git', 'diff', '--check'], cwd=ROOT, capture_output=True, text=True)
    require(diff.returncode == 0, diff.stdout + diff.stderr)
    for name in packet['source_sha256']:
        check = subprocess.run(['git', 'diff', '--no-index', '--check', '/dev/null', str(WORKSPACE / name)],
                               cwd=ROOT, capture_output=True, text=True)
        require(check.returncode in [0, 1] and not (check.stdout or check.stderr), check.stdout + check.stderr)
    diff_path = B / 'git-diff-check.json'
    delivery.save(diff_path, {'passed': True, 'tracked_diff_exit': diff.returncode,
        'new_definition_whitespace_checked': list(packet['source_sha256']), 'source_sha256': packet['source_sha256']})
    production = path(config['production_receipt'])
    leaves = [path(n) for n in config['leaf_receipts']]
    receipts = {'new_leaf_modules': leaves, 'checks_axioms': [kernel, production],
        'wrapped_kernel_type_identity': [kernel], 'import_audit': [production],
        'act1scene1': [production], 'axiom_audit': [production]}
    require(set(config['gate_evidence']) == {'independent_readbacks', 'source_ledger_consumers', 'existing_mission_scope'},
            'Unexpected non-CI evidence gate set')
    gates = {key: [path(n) for n in names] for key, names in config['gate_evidence'].items()}
    require(all(gates.values()), 'Missing reviewed non-CI evidence')
    gates['independent_readbacks'] += [blind_path, review_path, paper_check_path]
    gates['git_diff_check'] = [diff_path]
    evidence = {audit_path, inv_path, args.inputs.resolve(), paper_path, *compatibility_paths}
    evidence.update(p for group in [*receipts.values(), *gates.values()] for p in group)
    ready = {'passed': True, 'packet_sha256': sha(destination / 'packet.json'),
        'kernel_coverage': {'source': selected_count,
            'resolved': audit['requiredNamedComparedCount'] + audit['requiredProofValueResolutionCount'],
            'named': audit['requiredNamedComparedCount'], 'proof': audit['requiredProofValueResolutionCount'],
            'historical_requiredComparedCount': audit['requiredComparedCount']},
        'source_sha256': packet['source_sha256'], 'gates': dict.fromkeys(delivery.GATES, True),
        'ci_receipts': {key: list(map(str, value)) for key, value in receipts.items()},
        'axiom_audit': {'sorryAx_found': False, 'unexpected_axioms': []},
        'gate_evidence': {key: list(map(str, value)) for key, value in gates.items()},
        'evidence_sha256': delivery.path_hashes(evidence)}
    # Preflight in memory first. An invalid receipt must not leave ready.json behind.
    candidate = destination / 'ready.candidate.json'
    delivery.save(candidate, ready)
    try:
        delivery.preflight(destination / 'packet.json', candidate)
    finally:
        candidate.unlink()
    delivery.save(destination / 'ready.json', ready)
    print(json.dumps({'offline_ready': True, 'private_definition_count': len(packet['publications']),
                      'root_graph_membership': False, 'S2_04_completed': False}))


if __name__ == '__main__':
    main()
