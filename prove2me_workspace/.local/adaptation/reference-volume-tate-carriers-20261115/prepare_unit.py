#!/usr/bin/env python3
"""Bind the two accepted prior units and exact current source provenance offline."""
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
    p.add_argument('--foundation-ci-result', required=True)
    p.add_argument('--packet-field-correspondence', required=True)
    p.add_argument('--packet-field-typed-map')
    p.add_argument('--provenance-audit', required=True)
    p.add_argument('--out', required=True)
    args = p.parse_args()
    out = Path(args.out).resolve()
    require(TASK in out.parents, 'Output outside task directory')
    unit, closure = copy.deepcopy(load(args.inventory_unit)), load(args.dependency_closure)
    require(closure['schema'] == 'next-carrier-dependency-closure-v1', 'Unsupported closure schema')
    require(not closure['missingPriorAvailableConstants'], 'Unavailable prior constants')
    require(not closure['requiredPriorProofValueResolutions'], 'This unit has no accepted proof-value resolver scope')
    require(all(sha(e['path']) == e['sha256'] for e in closure['priorEvidence']), 'Closure prior evidence changed')
    correspondence_path = Path(args.packet_field_correspondence).resolve()
    correspondence = load(correspondence_path)
    # The foundation binding already accepted in packet-field is metadata only;
    # revalidate its receipt and audit in dependency_evidence below.
    old_unit = load(correspondence_path.parent / 'bound-unit-config.json')
    foundation, = old_unit['dependencies']
    foundation = copy.deepcopy(foundation)
    receipt = str(Path(args.foundation_ci_result).resolve())
    foundation['auditEvidence'] = [e for e in foundation['auditEvidence'] if e['kind'] != 'ci-result'] + [
        {'kind': 'ci-result', 'path': receipt, 'sha256': sha(receipt)}]
    typed_path = Path(args.packet_field_typed_map) if args.packet_field_typed_map else correspondence_path.parent / 'generated-wrapped/typed-original-source-wrapped-map.json'
    typed = load(typed_path)
    bundles = {b['module']: b for b in closure['importedBundles']}
    definitions = correspondence_path.parents[3] / 'Definitions'
    packet = {'status': 'accepted-kernel-audit', 'typedMap': str(typed_path.resolve()),
              'typedMapSha256': sha(typed_path),
              'acceptedConstantNames': sorted(c['original'] for c in correspondence['namedPairs']),
              'acceptedCorrespondence': {'path': str(correspondence_path), 'sha256': sha(correspondence_path)},
              'auditEvidence': [
                  {'kind': 'kernel-audit', 'path': correspondence['audit'], 'sha256': correspondence['auditSha256']},
                  {'kind': 'ci-result', 'path': correspondence['receipt'], 'sha256': correspondence['receiptSha256']}],
              'modules': [{'originalModule': m['originalModule'], 'wrappedModule': m['wrappedModule'],
                           'path': str(definitions / (m['wrappedModule'].split('.')[-1] + '.lean')),
                           'sha256': sha(definitions / (m['wrappedModule'].split('.')[-1] + '.lean'))}
                          for m in typed['modules']]}
    evidence = [{'path': str(Path(v).resolve()), 'sha256': sha(v)}
                for v in [args.inventory_unit, args.dependency_closure]]
    unit.update(dependencies=[foundation, packet],
                sourceProvenanceAudit={'path': str(Path(args.provenance_audit).resolve()), 'sha256': sha(args.provenance_audit)},
                inventoryEvidence=evidence)
    constants, modules, _ = dependency_evidence(unit)
    require(len(constants) == 241 and len(modules) == 10, 'Unexpected accepted prior unit counts')
    for bundle in bundles.values():
        actual = modules[bundle['module']]
        require(actual['sha256'] == bundle['sha256'] and Path(actual['path']).resolve() == Path(bundle['file']).resolve(),
                'Closure installed dependency bundle differs from accepted module')
    for c in closure['requiredPriorActualPairs']:
        actual = constants[c['original']]
        require(actual['wrappedName'] == c['target'] and actual['originalModule'] == c['module'],
                'Required prior actual pair differs')
    unit['requiredPriorActualNames'] = sorted(c['original'] for c in closure['requiredPriorActualPairs'])
    unit['proofValueResolverPolicy'] = 'not-needed-by-this-unit; elisions are evidence only and have no named target identity'
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(unit, ensure_ascii=False, indent=2) + '\n')
    unit_config(out)
    print(json.dumps({'status': 'offline-evidence-bound', 'path': str(out), 'sha256': sha(out),
                      'priorActualNamedConstants': len(constants), 'requiredPriorActualConstants': len(unit['requiredPriorActualNames']),
                      'proofValueResolverLoaded': False}, indent=2))


if __name__ == '__main__':
    main()
