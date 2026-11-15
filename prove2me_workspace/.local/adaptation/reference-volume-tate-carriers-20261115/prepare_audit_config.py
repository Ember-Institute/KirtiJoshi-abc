#!/usr/bin/env python3
"""Bind a strict kernel audit to inventory and accepted actual prior identities.

This program writes configuration and Lean source only. It never compiles.
"""
import argparse
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
W = Path('/home/admin-wsl/Coq/abc/prove2me_workspace')
ADAPTATION = W / '.local/adaptation'
FOUNDATION = ADAPTATION / 'foundation-reference-carriers-20261115'
PACKET = ADAPTATION / 'reference-packet-field-carriers-20261115'
DEFAULT_INV = HERE
STANDARD = ['Init', 'Lean', 'Std', 'Mathlib', 'Batteries', 'Aesop', 'Qq',
            'Plausible', 'ProofWidgets', 'ImportGraph', 'Cli', 'LeanSearchClient']
ALLOWED_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}


def load(path):
    return json.loads(Path(path).read_text())


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def dump(path, value):
    Path(path).write_text(json.dumps(value, indent=2, ensure_ascii=False) + '\n')


def name(text):
    result = []
    for part in text.split('.'):
        result = [result, 'str', part]
    return result


def prepend(prefix, value):
    if value == []:
        return prefix
    return [prepend(prefix, value[0]), value[1], value[2]]


def target_module(original):
    return 'Definitions.Def_AbcAdaptation_Reference_' + original.replace('.', '_')


def verify_receipt(path, expected_job):
    receipt = load(path)
    assert receipt['job_id'] == expected_job and receipt['status'] == 'succeeded'
    result = receipt['result']
    assert result['exit_code'] == 0
    assert result['snapshot']['workspace_mode'] == 'exclusive_worktree'
    assert result['snapshot']['snapshot_id'] is None
    return receipt


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--inventory-dir', type=Path, default=DEFAULT_INV)
    parser.add_argument('--output', type=Path, default=HERE / 'audit-config.json')
    parser.add_argument('--original-exprs', type=Path)
    parser.add_argument('--audit-output', type=Path)
    parser.add_argument('--wrapper-report', type=Path)
    args = parser.parse_args()
    # Output follows the location where the parent integrates this tool.
    assert args.output.resolve().parent == HERE
    invpath = args.inventory_dir / 'inventory.json'
    inventory = load(invpath)
    export = load(args.inventory_dir / 'export-config.json')
    imports = load(args.inventory_dir / 'imports.json')
    dep = load(args.inventory_dir / 'dependency-closure.json')
    assert sha(invpath) == export['inventorySha256']
    assert inventory['graphSha256'] == export['graphSha256'] == dep['graphSha256']
    for field in ['priorKernelAudit', 'priorInventory', 'priorMap']:
        key = field + ('Path' if field == 'priorKernelAudit' else '')
        assert sha(dep[key]) == dep[field + 'Sha256']
    for row in dep['priorEvidence']:
        assert sha(row['path']) == row['sha256']

    foundation_audit = load(FOUNDATION / 'kernel-audit/foundation-kernel-audit.json')
    assert foundation_audit['hasSorryAx'] is False
    foundation_receipt = FOUNDATION / 'kernel-audit-v2-result.json'
    verify_receipt(foundation_receipt, 'ci-013377-98675e26')
    accepted_path = PACKET / 'accepted-compiler-correspondence.json'
    accepted = load(accepted_path)
    assert accepted['status'] == 'accepted-kernel-audit'
    assert accepted['job_id'] == 'ci-013658-36534ff1'
    assert sha(accepted['receipt']) == accepted['receiptSha256']
    assert sha(accepted['audit']) == accepted['auditSha256']
    verify_receipt(accepted['receipt'], accepted['job_id'])
    packet_audit = load(accepted['audit'])
    assert packet_audit['hasSorryAx'] is False
    accepted_packet = {row['original']: row for row in accepted['namedPairs']}
    assert len(accepted_packet) == accepted['actualNamedComparisons']
    actual = {}
    for row in foundation_audit['comparisons']:
        source = row['sourceRecord']
        actual[row['original']] = {
            'original': row['original'], 'originalName': source['nameExpr'],
            'target': row['target'], 'targetName': name(row['target']),
            'targetToSourceUniverseIndices': row['targetToSourceUniverseIndices'],
            'expectedIsInstance': row['expectedIsInstance'],
            'expectedSourceAxioms': [name(ax) for ax in source['axioms']],
            'sourceOwner': source['module'], 'acceptedJob': 'ci-013377-98675e26'}
    for row in packet_audit['comparisons']:
        n = row['original']
        assert n in accepted_packet
        identity = accepted_packet[n]
        assert row['target'] == identity['target']
        assert row['targetToSourceUniverseIndices'] == identity['targetToSourceUniverseIndices']
        assert n not in actual
        source = row['sourceRecord']
        actual[n] = {
            'original': n, 'originalName': identity['originalName'],
            'target': identity['target'], 'targetName': identity['targetName'],
            'targetToSourceUniverseIndices': identity['targetToSourceUniverseIndices'],
            'expectedIsInstance': identity['isInstance'],
            'expectedSourceAxioms': [name(ax) for ax in source['axioms']],
            'sourceOwner': identity['sourceOwner'], 'acceptedJob': accepted['job_id']}
    assert set(accepted_packet) <= set(actual)
    required = dep['requiredPriorActualPairs']
    assert {r['original'] for r in required} == set(dep['requiredPriorConstants'])
    project_map = []
    for required_row in required:
        row = dict(actual[required_row['original']])
        assert row['target'] == required_row['target'] and row['sourceOwner'] == required_row['module']
        # This unit has no dependency on the old exceptional helper identities.
        assert row['target'] == 'AbcAdaptation.Reference.' + row['original']
        row.update(required=False, mappingRole='prior-accepted-required')
        project_map.append(row)

    current = {d['name']: d for m in inventory['modules'] for d in m['declarations']}
    assert len(current) == export['expectedRecordCount'] == len(export['records'])
    assert not set(current) & set(actual)
    for record in export['records']:
        n = record['name']
        d = current[n]
        assert d['selectedForBundle'] == record['selected']
        assert not d['hasSorryAx'] and set(d['axioms']) <= ALLOWED_AXIOMS
        project_map.append({
            'original': n, 'originalName': record['nameExpr'],
            'target': 'AbcAdaptation.Reference.' + n,
            'targetName': prepend(name('AbcAdaptation.Reference'), record['nameExpr']),
            'required': record['selected'], 'mappingRole': 'current-unit',
            'targetToSourceUniverseIndices': None,
            'expectedIsInstance': d['isInstance'],
            'expectedSourceAxioms': [name(ax) for ax in d['axioms']]})
    assert len(project_map) == len({r['original'] for r in project_map})
    assert len(project_map) == len({r['target'] for r in project_map})
    assert sum(r['selected'] for r in export['records']) == export['expectedSelectedCount']

    bundles = {r['wrappedModule']: r for r in dep['importedBundles']}
    # Retain the transitive Def dependencies of needed owners, never unrelated bundles.
    needed = {target_module(r['module']) for r in required}
    while True:
        expanded = set(needed)
        for module in needed:
            row = bundles[module]
            assert sha(row['file']) == row['sha256']
            for line in Path(row['file']).read_text().splitlines():
                if line.startswith('import Definitions.'):
                    expanded.add(line.removeprefix('import ').strip())
        if expanded == needed:
            break
        needed = expanded
    dependencies = [r for r in dep['importedBundles'] if r['wrappedModule'] in needed]
    by_module = {r['module']: r for r in imports}
    wrapper = ({r['module']: r for r in load(args.wrapper_report)['bundles']}
               if args.wrapper_report else None)
    modules = []
    for module in inventory['modules']:
        planned = list(dict.fromkeys(by_module[module['module']]['platform433Candidates']))
        direct = wrapper[module['module']]['platformImports'] if wrapper else planned
        assert len(direct) == len(set(direct)) and 'Mathlib' not in direct
        assert set(direct) <= set(planned), ('unreviewed direct import', module['module'], set(direct) - set(planned))
        for imported in direct:
            if imported.startswith('Definitions.') and imported in bundles:
                assert imported in needed, ('extra prior owner', imported)
        assert sha(module['source']) == module['sourceSha256']
        modules.append({
            'original': module['module'], 'source': module['source'],
            'sourceSha256': module['sourceSha256'],
            'normalizedSha256': module['normalizedSha256'],
            'target': target_module(module['module']), 'allowedDirectImports': direct,
            'importPolicy': 'exact explicit module set; implicit Init imports excluded',
            'sourceProvenance': module['provenance']})

    evidence_paths = [invpath, args.inventory_dir / 'export-config.json',
                      args.inventory_dir / 'imports.json', args.inventory_dir / 'dependency-closure.json',
                      foundation_receipt, accepted_path, Path(accepted['receipt']), Path(accepted['audit'])]
    evidence_paths += [Path(r['path']) for r in dep['priorEvidence']]
    evidence_paths += [Path(r['file']) for r in dependencies]
    if args.wrapper_report:
        evidence_paths.append(args.wrapper_report)
    evidence_paths = list(dict.fromkeys(p.resolve() for p in evidence_paths))
    config = {
        'schema': 'next-carrier-kernel-audit-config-v3',
        'inventorySha256': export['inventorySha256'], 'graphSha256': export['graphSha256'],
        'expectedRecordCount': len(current),
        'expectedSelectedCount': export['expectedSelectedCount'], 'expectedModuleCount': len(modules),
        'outputDir': str((args.audit_output or HERE / 'kernel-audit').resolve()),
        'originalExprFile': str((args.original_exprs or Path(export['outputFile'])).resolve()),
        'modules': modules, 'allowedDependencyModules': [name(r['wrappedModule']) for r in dependencies],
        'standardModulePrefixes': [name(n) for n in STANDARD],
        'projectPrefixes': [name(n) for n in ['Iut', 'TateCurvesTheta', 'Genl', 'AbcAdaptation', 'Definitions', 'Theorems', 'Solutions']],
        'originalProjectPrefixes': [name(n) for n in ['Iut', 'TateCurvesTheta', 'Genl']],
        'targetProjectPrefix': name('AbcAdaptation.Reference'), 'projectMap': project_map,
        'standardRenames': [],
        'standardRenamePolicy': 'No standard renames without separate actual compiler/source evidence.',
        'priorBundleEvidence': {
            'actualAcceptedNamedConstants': len(actual), 'requiredPriorConstants': dep['requiredPriorConstants'],
            'requiredActualPairs': required, 'bundles': dependencies,
            'acceptedKernelJobs': ['ci-013377-98675e26', accepted['job_id']],
            'candidateMapPolicy': 'Only actual accepted named identities; proof-value elisions have no standalone target.'},
        'inputEvidence': [{'path': str(p), 'sha256': sha(p)} for p in evidence_paths],
        'importPlanStatus': ('bound to wrapper report' if wrapper else 'candidate plan; regenerate with --wrapper-report before audit acceptance')}
    dump(args.output, config)
    dump(HERE / 'accepted-prior-identity-map.json', {
        'schema': 'volume-tate-accepted-prior-identity-map-v1',
        'policy': 'Actual named constants only; unit config includes only required dependency identities.',
        'namedPairs': list(actual.values()), 'requiredCount': len(required),
        'evidence': config['inputEvidence']})
    dump(HERE / 'source-axiom-inventory.json', {
        'schema': 'next-carrier-source-axiom-inventory-v3',
        'graphSha256': export['graphSha256'], 'inventorySha256': export['inventorySha256'],
        'standardAxioms': sorted(ALLOWED_AXIOMS), 'hasSorryAx': False,
        'newModuleCount': len(modules), 'newDeclarationCount': len(current),
        'newSelectedDeclarationCount': export['expectedSelectedCount'],
        'declarations': [{'name': n, 'module': d['module'], 'selected': d['selectedForBundle'],
                          'isInstance': d['isInstance'], 'axioms': d['axioms'], 'hasSorryAx': d['hasSorryAx']}
                         for n, d in sorted(current.items())]})
    template = (HERE / 'AuditNextCarriers.template.lean').read_text()
    header = 'import Lean\n' + ''.join('import ' + r['wrappedModule'] + '\n' for r in dependencies)
    header += ''.join('import ' + r['target'] + '\n' for r in modules)
    (HERE / 'AuditNextCarriers.lean').write_text(header + '\n' + template[template.index('/-! Stable JSON'):])
    print(json.dumps({'config': str(args.output.resolve()), 'sha256': sha(args.output),
                      'newDeclarations': len(current), 'newSelected': export['expectedSelectedCount'],
                      'requiredAcceptedPriorIdentities': len(required), 'projectMap': len(project_map),
                      'allowedPriorModules': [r['wrappedModule'] for r in dependencies]}, indent=2))


if __name__ == '__main__':
    main()
