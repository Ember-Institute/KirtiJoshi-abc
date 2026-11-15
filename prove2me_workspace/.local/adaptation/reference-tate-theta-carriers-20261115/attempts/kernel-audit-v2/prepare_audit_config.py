#!/usr/bin/env python3
"""Bind the four-module audit to actual source Names and three accepted prior units.

Writes local JSON and Lean files only. No compiler, CI, API, network, or Git calls.
Final configuration requires actual original-exprs and an actual wrapper report.
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
VOLUME = ADAPTATION / 'reference-volume-tate-carriers-20261115'
STANDARD = ['Init', 'Lean', 'Std', 'Mathlib', 'Batteries', 'Aesop', 'Qq',
            'Plausible', 'ProofWidgets', 'ImportGraph', 'Cli', 'LeanSearchClient']
ALLOWED_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}
EXPECTED_MODULES = ['TateCurvesTheta.TateCurve.JInvariant',
                    'TateCurvesTheta.TateCurve.Parametrization',
                    'Iut.Cor312.ThetaData.AdmissiblePrime',
                    'Iut.Cor312.ThetaData.TateStructure']


def load(path):
    return json.loads(Path(path).read_text())


def sha(path):
    digest = hashlib.sha256()
    with Path(path).open('rb') as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b''):
            digest.update(chunk)
    return digest.hexdigest()


def dump(path, value):
    Path(path).write_text(json.dumps(value, indent=2, ensure_ascii=False) + '\n')


def name(text):
    """For public module/axiom literals only; never recover compiler Names this way."""
    result = []
    for part in text.split('.'):
        assert part and not part.isdecimal(), ('non-public literal', text)
        result = [result, 'str', part]
    return result


def name_parts(value):
    if value == []:
        return []
    assert isinstance(value, list) and len(value) == 3
    prefix, kind, part = value
    assert ((kind == 'str' and isinstance(part, str)) or
            (kind == 'num' and isinstance(part, int) and not isinstance(part, bool) and part >= 0))
    return name_parts(prefix) + [(kind, part)]


def display_name(value):
    return '.'.join(str(v) for _, v in name_parts(value))


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
    assert receipt['request']['exclusive'] is True
    assert Path(receipt['request']['workspace']).resolve() == W.resolve()
    assert result['snapshot']['workspace_mode'] == 'exclusive_worktree'
    assert result['snapshot']['snapshot_id'] is None
    return receipt


def accepted_prior():
    evidence = []
    foundation_receipt = FOUNDATION / 'kernel-audit-v2-result.json'
    verify_receipt(foundation_receipt, 'ci-013377-98675e26')
    foundation_path = FOUNDATION / 'kernel-audit/foundation-kernel-audit.json'
    foundation = load(foundation_path)
    assert foundation['hasSorryAx'] is False
    evidence += [foundation_receipt, foundation_path]
    actual = {}
    for row in foundation['comparisons']:
        source = row['sourceRecord']
        assert row['kernelTypeEqual'] and row['instanceRegistryMatchesAcceptedGraph']
        assert not set(source['axioms']) - ALLOWED_AXIOMS
        original_name = source['nameExpr']
        assert display_name(original_name) == row['original']
        assert row['target'] == 'AbcAdaptation.Reference.' + row['original']
        actual[row['original']] = {
            'original': row['original'], 'originalName': original_name,
            'target': row['target'], 'targetName': None,
            'targetNameResolutionStatus': 'accepted legacy display identity; resolve exact actual platform Name at expected owner',
            'targetToSourceUniverseIndices': row['targetToSourceUniverseIndices'],
            'expectedIsInstance': row['expectedIsInstance'],
            'expectedSourceAxioms': [name(ax) for ax in source['axioms']],
            'sourceOwner': source['module'], 'acceptedJob': 'ci-013377-98675e26'}
    assert len(actual) == 110
    for unit, job, count in [(PACKET, 'ci-013658-36534ff1', 131),
                             (VOLUME, 'ci-013964-cce30c9e', 98)]:
        accepted_path = unit / 'accepted-compiler-correspondence.json'
        accepted = load(accepted_path)
        assert accepted['status'] == 'accepted-kernel-audit' and accepted['job_id'] == job
        assert sha(accepted['receipt']) == accepted['receiptSha256']
        assert sha(accepted['audit']) == accepted['auditSha256']
        verify_receipt(accepted['receipt'], job)
        audit = load(accepted['audit'])
        assert audit['hasSorryAx'] is False
        compared = {r['original']: r for r in audit['comparisons']}
        assert len(compared) == len(audit['comparisons'])
        identities = accepted['namedPairs']
        assert len(identities) == accepted['actualNamedComparisons'] == count
        assert {r['original'] for r in identities} == set(compared)
        for identity in identities:
            n = identity['original']
            assert n not in actual
            row = compared[n]
            source = row['sourceRecord']
            assert identity['target'] == row['target']
            assert identity['targetToSourceUniverseIndices'] == row['targetToSourceUniverseIndices']
            assert identity['originalName'] == source['nameExpr']
            assert display_name(identity['targetName']) == row['target']
            assert row['kernelTypeEqual'] and row['instanceRegistryMatchesAcceptedGraph']
            assert set(source['axioms']) <= ALLOWED_AXIOMS
            actual[n] = {
                'original': n, 'originalName': identity['originalName'],
                'target': identity['target'], 'targetName': identity['targetName'],
                'targetToSourceUniverseIndices': identity['targetToSourceUniverseIndices'],
                'expectedIsInstance': identity.get('expectedIsInstance', identity.get('isInstance')),
                'expectedSourceAxioms': [name(ax) for ax in source['axioms']],
                'sourceOwner': identity['sourceOwner'], 'acceptedJob': job}
            assert actual[n]['expectedIsInstance'] == source['isInstance']
        evidence += [accepted_path, Path(accepted['receipt']), Path(accepted['audit'])]
    assert len(actual) == 339
    return actual, list(dict.fromkeys(evidence))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--inventory-dir', type=Path)
    parser.add_argument('--output', type=Path, default=HERE / 'audit-config.json')
    parser.add_argument('--original-exprs', type=Path)
    parser.add_argument('--original-view-evidence', type=Path, help='Hash-bound lossless raw/compact token-equivalence report')
    parser.add_argument('--audit-output', type=Path)
    parser.add_argument('--compact-output', action='store_true', help='Serialize complete audit JSON with Json.compress; preserve all checks and values')
    parser.add_argument('--wrapper-report', type=Path)
    parser.add_argument('--prior-only', action='store_true', help='Verify and export only the339 accepted prior named identities')
    args = parser.parse_args()
    assert args.output.resolve().parent == HERE
    actual, prior_evidence = accepted_prior()
    prior_map = {
        'schema': 'tate-theta-accepted-prior-identity-map-v1',
        'status': 'accepted-prior-only-current-unit-not-compared',
        'policy': 'Actual named constants only from foundation110 + packet-field131 + volume-tate98. Prior proof-value resolutions have no named identity.',
        'namedPairs': list(actual.values()),
        'evidence': [{'path': str(p), 'sha256': sha(p)} for p in prior_evidence]}
    dump(HERE / 'accepted-prior-identity-map.json', prior_map)
    if args.prior_only:
        print(json.dumps({'acceptedPriorNamedIdentities': len(actual), 'currentUnitCompared': False}))
        return
    if not args.inventory_dir or not args.original_exprs or not args.wrapper_report:
        parser.error('Final config requires --inventory-dir, --original-exprs, and --wrapper-report; use --prior-only for prior evidence only')
    invpath = args.inventory_dir / 'inventory.json'
    inventory = load(invpath)
    export = load(args.inventory_dir / 'export-config.json')
    imports = load(args.inventory_dir / 'imports.json')
    dep = load(args.inventory_dir / 'dependency-closure.json')
    assert sha(invpath) == export['inventorySha256']
    assert inventory['graphSha256'] == export['graphSha256'] == dep['graphSha256']
    assert [m['module'] for m in inventory['modules']] == EXPECTED_MODULES
    assert sum(len(m['selectedSourceCommandCandidates']) for m in inventory['modules']) == 20
    assert sha(inventory['graph']) == inventory['graphSha256']
    for row in dep['priorEvidence']:
        assert sha(row['path']) == row['sha256']
    required = dep['requiredPriorActualPairs']
    assert {r['original'] for r in required} == set(dep['requiredPriorConstants'])
    assert len(required) == 42 and dep['availableAcceptedNamedCount'] == len(actual)
    assert dep['requiredPriorProofValueResolutions'] == []
    project_map = []
    for required_row in required:
        row = dict(actual[required_row['original']])
        assert row['target'] == required_row['target'] and row['sourceOwner'] == required_row.get('sourceOwner', required_row.get('module'))
        row.update(required=False, mappingRole='prior-accepted-required',
                   targetOwner=target_module(row['sourceOwner']))
        project_map.append(row)
    current = {d['name']: d for m in inventory['modules'] for d in m['declarations']}
    assert len(current) == export['expectedRecordCount'] == len(export['records']) == 117
    assert not set(current) & set(actual)
    serialization_view_evidence = []
    serialization_view = None
    if args.original_view_evidence:
        serialization_view = load(args.original_view_evidence)
        view = serialization_view
        assert view['schema'] == 'tate-theta-lossless-original-exprs-compact-view-v1'
        assert Path(view['compact']['path']).resolve() == args.original_exprs.resolve()
        assert sha(args.original_exprs) == view['compact']['sha256']
        assert args.original_exprs.stat().st_size == view['compact']['bytes']
        assert view['recordCount'] == 117 and view['selectedCount'] == 78
        assert all(view['preservation'][k] is True for k in [
            'completeLexicalTokenStreamsCompared', 'onlyWhitespaceOutsideJsonStringsRemoved',
            'allExprNameBinderMetadataAndRecordValuesUnchanged', 'parsedJsonEquality'])
        raw = Path(view['raw']['path'])
        assert sha(raw) == view['raw']['sha256'] and raw.stat().st_size == view['raw']['bytes']
        acceptance_path = Path(view['sourceAcceptance']['path'])
        assert sha(acceptance_path) == view['sourceAcceptance']['sha256']
        acceptance = load(acceptance_path)
        assert acceptance['status'] == 'accepted' and acceptance['originalExprsSha256'] == view['raw']['sha256']
        compiler_receipt_path = Path(acceptance['compilerReceiptPath'])
        assert sha(compiler_receipt_path) == acceptance['compilerReceiptSha256']
        compiler_receipt = load(compiler_receipt_path)
        assert compiler_receipt['status'] == 'succeeded' and compiler_receipt['result']['exit_code'] == 0
        assert compiler_receipt['job_id'] == acceptance['job_id']
        serialization_view_evidence = [args.original_view_evidence, raw, acceptance_path, compiler_receipt_path]
    source = load(args.original_exprs)
    assert source['schema'] == 'foundation-original-exprs-v2' and source['compilerVersion'] == '4.35.0-rc3'
    for k in ['inventorySha256', 'graphSha256']:
        assert source[k] == export[k]
    records = {r['name']: r for r in source['records']}
    assert len(records) == len(source['records']) == source['recordCount'] == len(current)
    assert set(records) == set(current)
    assert source['selectedCount'] == export['expectedSelectedCount'] == 78
    excluded = []
    for entry in export['records']:
        n = entry['name']
        d, record = current[n], records[n]
        assert d['selectedForBundle'] == entry['selected'] == record['selected']
        assert record['isInstance'] == d['isInstance']
        assert set(record['axioms']) == set(d['axioms']) <= ALLOWED_AXIOMS and not d['hasSorryAx']
        assert record['module'] == d['module'] and display_name(record['nameExpr']) == n
        if entry['nameExpr'] is not None:
            assert record['nameExpr'] == entry['nameExpr']
        for key in ['sourceSha256', 'normalizedSha256']:
            assert record[key] == entry[key]
        parts = name_parts(record['nameExpr'])
        if d['isPrivate']:
            assert not record['selected'] and parts[0] == ('str', '_private')
            assert ('num', 0) in parts
            excluded.append({'original': n, 'originalName': record['nameExpr'], 'target': None,
                             'reason': 'unselected source-private declaration; actual Name preserved without inventing target identity'})
            continue
        project_map.append({
            'original': n, 'originalName': record['nameExpr'],
            'target': 'AbcAdaptation.Reference.' + n,
            'targetName': prepend(name('AbcAdaptation.Reference'), record['nameExpr']),
            'required': record['selected'], 'mappingRole': 'current-unit',
            'targetToSourceUniverseIndices': None,
            'expectedIsInstance': d['isInstance'],
            'expectedSourceAxioms': [name(ax) for ax in d['axioms']]})
    assert len(excluded) == 6 and len(project_map) == 153
    assert len(project_map) == len({r['original'] for r in project_map}) == len({r['target'] for r in project_map})
    assert sum(r['selected'] for r in source['records']) == 78
    bundles = {r['wrappedModule']: r for r in dep['importedBundles']}
    needed = {target_module(r.get('sourceOwner', r.get('module'))) for r in required}
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
    wrappers = load(args.wrapper_report)
    wrapper = {r['module']: r for r in wrappers['bundles']}
    assert set(wrapper) == set(EXPECTED_MODULES)
    modules = []
    for module in inventory['modules']:
        planned = list(dict.fromkeys(by_module[module['module']]['platform433Candidates']))
        wr = wrapper[module['module']]
        assert sha(wr['path']) == wr['sha256']
        direct = wr['platformImports']
        assert len(direct) == len(set(direct)) and 'Mathlib' not in direct
        assert set(direct) <= set(planned), ('unreviewed direct import', module['module'], set(direct) - set(planned))
        for imported in direct:
            if imported.startswith('Definitions.') and imported in bundles:
                assert imported in needed, ('extra prior owner', imported)
        assert sha(module['source']) == module['sourceSha256']
        modules.append({
            'original': module['module'], 'source': module['source'],
            'sourceSha256': module['sourceSha256'], 'normalizedSha256': module['normalizedSha256'],
            'target': target_module(module['module']), 'allowedDirectImports': direct,
            'importPolicy': 'exact explicit module set; implicit Init imports excluded',
            'sourceProvenance': module['provenance']})
    evidence_paths = [invpath, args.inventory_dir / 'export-config.json', args.inventory_dir / 'imports.json',
                      args.inventory_dir / 'dependency-closure.json', args.original_exprs, args.wrapper_report]
    evidence_paths += serialization_view_evidence + prior_evidence + [Path(r['path']) for r in dep['priorEvidence']] + [Path(r['file']) for r in dependencies]
    evidence_paths = list(dict.fromkeys(p.resolve() for p in evidence_paths))
    config = {
        'schema': 'next-carrier-kernel-audit-config-v3',
        'inventorySha256': export['inventorySha256'], 'graphSha256': export['graphSha256'],
        'expectedRecordCount': len(current), 'expectedSelectedCount': 78, 'expectedNamedSelectedCount': 78,
        'expectedProofValueResolutionCount': 0, 'expectedTargetOnlyCompilerDeclarations': [],
        'expectedModuleCount': len(modules),
        'outputDir': str((args.audit_output or HERE / 'kernel-audit').resolve()),
        'auditJsonSerialization': 'compact' if args.compact_output else 'pretty',
        'originalExprFile': str(args.original_exprs.resolve()),
        'originalExprSerializationView': serialization_view,
        'modules': modules, 'allowedDependencyModules': [name(r['wrappedModule']) for r in dependencies],
        'standardModulePrefixes': [name(n) for n in STANDARD],
        'projectPrefixes': [name(n) for n in ['Iut', 'TateCurvesTheta', 'Genl', 'AbcAdaptation', 'Definitions', 'Theorems', 'Solutions']],
        'originalProjectPrefixes': [name(n) for n in ['Iut', 'TateCurvesTheta', 'Genl']],
        'targetProjectPrefix': name('AbcAdaptation.Reference'), 'projectMap': project_map,
        'excludedOriginalDeclarations': excluded, 'standardRenames': [],
        'standardRenamePolicy': 'No standard renames, source expansions, or equality fallbacks in this unit.',
        'priorBundleEvidence': {
            'actualAcceptedNamedConstants': len(actual), 'requiredPriorConstants': dep['requiredPriorConstants'],
            'requiredActualPairs': required, 'bundles': dependencies,
            'acceptedKernelJobs': ['ci-013377-98675e26', 'ci-013658-36534ff1', 'ci-013964-cce30c9e'],
            'candidateMapPolicy': 'Only actual accepted named identities; prior proof-value elisions have no standalone target.'},
        'inputEvidence': [{'path': str(p), 'sha256': sha(p)} for p in evidence_paths],
        'importPlanStatus': 'bound to actual wrapper report; current target comparisons require new kernel receipt'}
    dump(args.output, config)
    dump(HERE / 'source-axiom-inventory.json', {
        'schema': 'next-carrier-source-axiom-inventory-v3', 'graphSha256': export['graphSha256'],
        'inventorySha256': export['inventorySha256'], 'standardAxioms': sorted(ALLOWED_AXIOMS), 'hasSorryAx': False,
        'newModuleCount': len(modules), 'newDeclarationCount': len(current), 'newSelectedDeclarationCount': 78,
        'declarations': [{'name': n, 'nameExpr': records[n]['nameExpr'], 'module': d['module'],
                          'selected': d['selectedForBundle'], 'isInstance': d['isInstance'],
                          'axioms': d['axioms'], 'hasSorryAx': d['hasSorryAx']} for n, d in sorted(current.items())]})
    template = (HERE / 'AuditNextCarriers.template.lean').read_text()
    if args.compact_output:
        final_serialization = ']).pretty ++ "\\n")'
        assert template.count(final_serialization) == 1
        template = template.replace(final_serialization, ']).compress ++ "\\n")')
    header = 'import Lean\n' + ''.join('import ' + r['wrappedModule'] + '\n' for r in dependencies)
    header += ''.join('import ' + r['target'] + '\n' for r in modules)
    (HERE / 'AuditNextCarriers.lean').write_text(header + '\n' + template[template.index('/-! Stable JSON'):])
    print(json.dumps({'config': str(args.output.resolve()), 'sha256': sha(args.output),
                      'newDeclarations': len(current), 'newSelected': 78, 'excludedPrivateNoTarget': len(excluded),
                      'requiredAcceptedPriorIdentities': len(required), 'projectMap': len(project_map),
                      'allowedPriorModules': [r['wrappedModule'] for r in dependencies]}, indent=2))


if __name__ == '__main__':
    main()
