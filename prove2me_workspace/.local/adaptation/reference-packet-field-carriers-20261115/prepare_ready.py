"""Bind final local and read-only platform evidence before five private publications."""
from pathlib import Path
import argparse
import importlib.util
import json
import subprocess

B = Path(__file__).resolve().parent
W = B.parents[2]
R = W.parent
spec = importlib.util.spec_from_file_location('packet_field_delivery', B / 'delivery.py')
delivery = importlib.util.module_from_spec(spec)
spec.loader.exec_module(delivery)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--kernel-receipt', required=True)
    args = parser.parse_args()
    load = delivery.read
    audit_path = B / 'kernel-audit/next-carrier-kernel-audit.json'
    audit = load(audit_path)
    assert audit['requiredSourceDeclarationCount'] == audit['requiredResolvedCount'] == 133
    assert audit['requiredComparedCount'] == 131
    assert audit['requiredEliminatedInternalProofCount'] == 2
    assert audit['hasSorryAx'] is False
    assert audit['allOwnedTypeValueClosuresStandardAxiomsOnly'] is True
    assert all(not d['hasSorryAx'] for d in audit['ownedDeclarations'])
    assert all(p['ownerTypeKernelEqual'] and p['ownerComputationalValueKernelEqual']
               for p in audit['eliminatedInternalProofResolutions'])
    review_path = B / 'final-review/prepublication-review.json'
    review = load(review_path)
    assert review['blocking_findings'] == []
    assert review['status'] == 'passed' and review['frozen'] is True
    assert all(delivery.sha(path) == digest for path, digest in review['frozen_evidence_sha256'].items())
    assert load(B / 'scope-preflight/scope-review.json')['passed'] is True
    assert load(B / 'blind-readbacks.json')['passed'] is True
    paper_check = load(B / 'paper-context-validation.json')
    assert all(paper_check['checks'].values())
    assert paper_check['paper_context_sha256'] == delivery.sha(B / 'paper-context.json')
    destination = B / 'delivery'
    packet = delivery.prepare(B / 'generated-wrapped/foundation-wrapper-report.json',
        B / 'blind-readbacks.json', B / 'paper-context.json', B / 'SOURCE_LEDGER.json', destination)
    assert review['definitions_sha256'] == packet['source_sha256']
    paths = list(packet['source_sha256'])
    diff = subprocess.run(['git', 'diff', '--check'], cwd=R, capture_output=True, text=True)
    assert diff.returncode == 0, diff.stdout + diff.stderr
    # New Definitions are untracked until the final exact-path staging step.
    for name in paths:
        check = subprocess.run(['git', 'diff', '--no-index', '--check', '/dev/null', str(W / name)],
                               cwd=R, capture_output=True, text=True)
        assert check.returncode in [0, 1] and not (check.stdout or check.stderr), check.stdout + check.stderr
    diff_path = B / 'git-diff-check.json'
    delivery.save(diff_path, {'passed': True, 'tracked_diff_exit': diff.returncode,
        'new_definition_whitespace_checked': paths, 'source_sha256': packet['source_sha256']})
    leaf_paths = [B / ('platform-' + slug + '-' + kind + '-result.json')
        for slug in ['Container', 'HolomorphicHull', 'GlobalField', 'PlacesOver', 'QParameterBasic']
        for kind in ['leaf', 'artifact']]
    kernel = B / args.kernel_receipt
    production = B / 'production-gates-result.json'
    receipts = {'new_leaf_modules': leaf_paths, 'checks_axioms': [kernel, production],
        'wrapped_kernel_type_identity': [kernel], 'import_audit': [production],
        'act1scene1': [production], 'axiom_audit': [production]}
    gates = {'independent_readbacks': [B / 'blind-readbacks.json', review_path,
            B / 'readback-metadata/validation.json', B / 'paper-context-validation.json'],
        'source_ledger_consumers': [B / 'SOURCE_LEDGER.json', B / 'source-provenance-audit.json',
            review_path, B / 'helper-resolution-evidence/root-integration.json'],
        'git_diff_check': [diff_path],
        'existing_mission_scope': [B / 'scope-preflight/scope-review.json',
            B / 'scope-preflight/mission-list-readback.json',
            B / 'scope-preflight/mission-root-readback.json', B / 'scope-preflight/root-graph.json']}
    evidence = {audit_path, B / 'original-exprs-acceptance.json'}
    evidence.update(path for group in [*receipts.values(), *gates.values()] for path in group)
    ready = {'passed': True, 'packet_sha256': delivery.sha(destination / 'packet.json'),
        'source_sha256': packet['source_sha256'], 'gates': dict.fromkeys(delivery.GATES, True),
        'ci_receipts': {key: list(map(str, value)) for key, value in receipts.items()},
        'axiom_audit': {'sorryAx_found': False, 'unexpected_axioms': []},
        'gate_evidence': {key: list(map(str, value)) for key, value in gates.items()},
        'evidence_sha256': delivery.path_hashes(evidence)}
    delivery.save(destination / 'ready.json', ready)
    delivery.preflight(destination / 'packet.json', destination / 'ready.json')
    print(json.dumps({'offline_ready': True, 'private_definition_count': len(packet['publications']),
                      'root_graph_membership': False, 'S2_04_completed': False}))


if __name__ == '__main__':
    main()
