#!/usr/bin/env python3
"""Bind frozen inventory provenance to actual delivered carrier audit evidence."""
import argparse
import copy
import json
from pathlib import Path
from carrier_contract import load, sha, require, unit_config, dependency_evidence

TASK = Path(__file__).resolve().parent


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--inventory-unit', required=True)
    p.add_argument('--dependency-closure', required=True)
    p.add_argument('--prior-ci-result', required=True)
    p.add_argument('--provenance-audit')
    p.add_argument('--out', required=True)
    args = p.parse_args()
    out = Path(args.out).resolve()
    require(TASK in out.parents, 'Output outside task directory')
    unit, closure = copy.deepcopy(load(args.inventory_unit)), load(args.dependency_closure)
    require(closure['schema'] == 'next-carrier-dependency-closure-v1', 'Unsupported closure schema')
    require(not closure['missingPriorAvailableConstants'], 'Inventory has unavailable prior carrier constants')
    audit = load(closure['priorKernelAuditPath'])
    dependency = {'status': 'accepted-kernel-audit',
                  'typedMap': closure['priorMap'], 'typedMapSha256': closure['priorMapSha256'],
                  'acceptedConstantNames': sorted(c['original'] for c in audit['comparisons']),
                  'auditEvidence': [
                      {'kind': 'kernel-audit', 'path': closure['priorKernelAuditPath'],
                       'sha256': closure['priorKernelAuditSha256']},
                      {'kind': 'ci-result', 'path': str(Path(args.prior_ci_result).resolve()),
                       'sha256': sha(args.prior_ci_result)}],
                  'modules': [{'originalModule': b['module'], 'wrappedModule': b['wrappedModule'],
                               'path': b['file'], 'sha256': b['sha256']}
                              for b in closure['importedBundles']]}
    provenance_audit = Path(args.provenance_audit) if args.provenance_audit else Path(args.inventory_unit).parent / 'source-provenance-audit.json'
    unit.update(dependencies=[dependency], sourceProvenanceAudit={'path': str(provenance_audit.resolve()),
                'sha256': sha(provenance_audit)}, inventoryEvidence=[
        {'path': str(Path(args.inventory_unit).resolve()), 'sha256': sha(args.inventory_unit)},
        {'path': str(Path(args.dependency_closure).resolve()), 'sha256': sha(args.dependency_closure)}])
    # Check every binding before publishing the ready-to-use configuration.
    dependency_evidence(unit)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(unit, ensure_ascii=False, indent=2) + '\n')
    unit_config(out)
    print(json.dumps({'status': 'offline-evidence-bound', 'path': str(out), 'sha256': sha(out),
                      'priorComparedConstants': len(dependency['acceptedConstantNames']),
                      'priorDeliveredModules': len(dependency['modules'])}, indent=2))


if __name__ == '__main__':
    main()
