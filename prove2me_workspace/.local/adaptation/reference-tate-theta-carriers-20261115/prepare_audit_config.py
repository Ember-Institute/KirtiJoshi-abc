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


def platform_helper_evidence(args, export, records):
    proof = 'TateCurvesTheta.TateParameter.tateJ.eq_1'
    parent = 'TateCurvesTheta.TateParameter.tateJ'
    if not args.platform_facts or not args.platform_receipt or not args.platform_query_config:
        raise ValueError('Exact source equation proof requires --platform-facts, --platform-receipt, and --platform-query-config')
    receipt = verify_receipt(args.platform_receipt, 'ci-014164-c01e488c')
    facts = load(args.platform_facts)
    assert facts['schema'] == 'tate-theta-platform-helper-facts-v1' and facts['compilerVersion'] == '4.33.1'
    for key in ['inventorySha256', 'graphSha256']:
        assert facts[key] == export[key]
    assert facts['sourceRecordCount'] == 117 and facts['publicSourceCandidateCount'] == 111
    assert facts['selectedSourceCount'] == 78 and facts['selectedMissingCount'] == 1
    assert facts['ownedDeclarationCount'] == len(facts['ownedDeclarations']) == 77
    assert facts['targetOnlyNames'] == []
    req = receipt['request']
    manifest = req['worktree_manifest']
    query_source = W / req['parameters']['source']
    assert req['task_type'] == 'leaf' and req['target'] == 'file'
    assert sha(query_source) == manifest['source_sha256']
    assert manifest['input_hashes'][str(query_source)] == sha(query_source)
    queried_config = Path(req['environment']['NEXT_CARRIER_AUDIT_CONFIG'])
    assert sha(args.platform_query_config) == manifest['input_hashes'][str(queried_config)]
    assert load(args.platform_query_config) == facts['sourceAuditConfiguration']
    coverage = facts['expectedCurrentCandidates']
    assert len(coverage) == 111 and len({r['original'] for r in coverage}) == 111
    selected = [r for r in coverage if r['selected']]
    assert len(selected) == 78
    missing = [r for r in selected if not r['present']]
    assert len(missing) == 1 and missing[0]['original'] == proof
    for row in coverage:
        source = records[row['original']]
        assert source['nameExpr'] == row['originalName'] and source['selected'] == row['selected']
    owned = {r['name']: r for r in facts['ownedDeclarations']}
    assert len(owned) == 77 and set(owned) == {r['candidateTarget'] for r in coverage if r['present']}
    assert set(owned) == {r['candidateTarget'] for r in selected if r['present']}
    for row in facts['ownedDeclarations']:
        assert not row['hasSorryAx'] and display_name(row['nameExpr']) == row['name']
        for key in ['axioms', 'typeAxioms', 'valueAxioms']:
            assert set(row[key]) <= ALLOWED_AXIOMS
    for row in coverage:
        if row['present']:
            target = owned[row['candidateTarget']]
            assert target['nameExpr'] == row['candidateTargetName']
            assert target['module'] == target_module(records[row['original']]['module'])
            assert target['constantKind'] == row['actualConstantKind']
            assert target['levelParams'] == row['actualLevelParams']
    parent_target = 'AbcAdaptation.Reference.' + parent
    parent_facts = [r for r in facts['helperFacts'] if r['name'] == parent_target]
    assert len(parent_facts) == 1
    actual_parent = parent_facts[0]
    assert actual_parent['constantKind'] == 'definition' and not actual_parent['isProposition']
    assert actual_parent['valueExpr'] is not None and not actual_parent['hasSorryAx']
    assert records[parent]['selected'] and not records[parent]['isProposition']
    assert records[parent]['constantKind'] == 'definition' and records[parent]['valueExpr'] is not None
    evidence_paths = [args.platform_facts, args.platform_receipt, args.platform_query_config, query_source]
    binding = {
        'facts': {'path': str(args.platform_facts.resolve()), 'sha256': sha(args.platform_facts), 'contents': facts},
        'receipt': {'path': str(args.platform_receipt.resolve()), 'sha256': sha(args.platform_receipt), 'contents': receipt},
        'querySource': {'path': str(query_source.resolve()), 'sha256': sha(query_source)},
        'queryConfiguration': {'path': str(args.platform_query_config.resolve()), 'sha256': sha(args.platform_query_config)},
        'policy': 'Only actual platform query evidence; exactly one absent selected equation theorem and77 actual owned named constants.'}
    return binding, actual_parent, evidence_paths


def standard_proof_evidence(args, export, current, records):
    original = 'NumberField.RingOfIntegers.instHasFiniteQuotients'
    for key in ['standard_source_facts', 'standard_source_receipt', 'standard_platform_facts',
                'standard_platform_receipt', 'standard_source_query_config']:
        if getattr(args, key) is None:
            raise ValueError('Exact standard proof requires --' + key.replace('_', '-'))
    source = load(args.standard_source_facts)
    platform = load(args.standard_platform_facts)
    source_receipt = verify_receipt(args.standard_source_receipt, 'ci-014215-2414b895')
    platform_receipt = verify_receipt(args.standard_platform_receipt, 'ci-014243-25ac457f')
    assert source['schema'] == 'tate-theta-exact-standard-source-facts-v1' and source['compilerVersion'] == '4.35.0-rc3'
    assert platform['schema'] == 'tate-theta-exact-standard-platform-facts-v1' and platform['compilerVersion'] == '4.33.1'
    for facts in [source, platform]:
        for key in ['inventorySha256', 'graphSha256']:
            assert facts[key] == export[key]
    assert source['selectedOriginalScopeCount'] == 78
    assert source['relevantStandardNameCount'] == platform['relevantStandardNameCount'] == 270
    assert [display_name(n) for n in platform['missingRelevantStandardNames']] == [original]
    assert len(platform['originalCurrentStandardShapeChecks']) == 7
    assert all(r['succeeded'] for r in platform['originalCurrentStandardShapeChecks'])
    assert platform['genuineSourceBodyAttempt']['succeeded'] is False
    native = platform['nativeProofAttempt']
    assert all(native[k] is True for k in ['succeeded', 'kernelCheckedExactSourceType', 'dependencyOwnersStandardOnly'])
    assert native['hasSorryAx'] is False and set(native['axioms']) <= ALLOWED_AXIOMS
    source_record = next(r for r in source['facts'] if r['name'] == original)
    assert source_record['constantKind'] == 'theorem' and source_record['isProposition'] and source_record['isInstance']
    assert len(source_record['levelParams']) == 1 and source_record['valueExpr'] is not None
    native_params = []
    def visit(value):
        if isinstance(value, dict):
            if value.get('kind') == 'param' and value['name'] not in native_params:
                native_params.append(value['name'])
            for item in value.values():
                visit(item)
        elif isinstance(value, list):
            for item in value:
                visit(item)
    visit(native['type']); visit(native['value'])
    assert len(native_params) == 1
    assert name_parts(native_params[0]) == [('str', '_finiteQuotientsQueryUniverse'), ('num', 0)]
    query_paths = []
    for receipt in [source_receipt, platform_receipt]:
        req = receipt['request']; manifest = req['worktree_manifest']
        query = W / req['parameters']['source']
        assert req['task_type'] == 'leaf' and req['target'] == 'file'
        assert sha(query) == manifest['source_sha256'] == manifest['input_hashes'][str(query)]
        query_paths.append(query)
    old_config_path = source_receipt['request']['environment']['NEXT_CARRIER_AUDIT_CONFIG']
    assert sha(args.standard_source_query_config) == source_receipt['request']['worktree_manifest']['input_hashes'][old_config_path]
    original_facts_path = platform_receipt['request']['environment']['NEXT_CARRIER_STANDARD_SOURCE_FACTS']
    assert sha(args.standard_source_facts) == platform_receipt['request']['worktree_manifest']['input_hashes'][original_facts_path]
    assert 'import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients\n' in query_paths[1].read_text()
    consumers = sorted(n for n, d in current.items() if d['selectedForBundle'] and
                       original in set(d['directTypeDeps']) | set(d['directValueDeps']) and
                       not records[n]['isProposition'] and records[n]['valueExpr'] is not None)
    assert len(consumers) == 9
    paths = [args.standard_source_facts, args.standard_source_receipt, args.standard_platform_facts,
             args.standard_platform_receipt, args.standard_source_query_config] + query_paths
    evidence = {}
    for key, path, contents in [
        ('sourceFacts', args.standard_source_facts, source),
        ('sourceReceipt', args.standard_source_receipt, source_receipt),
        ('platformFacts', args.standard_platform_facts, platform),
        ('platformReceipt', args.standard_platform_receipt, platform_receipt)]:
        evidence[key] = {'path': str(path.resolve()), 'sha256': sha(path), 'contents': contents}
    evidence['sourceQueryConfiguration'] = {'path': str(args.standard_source_query_config.resolve()),
                                           'sha256': sha(args.standard_source_query_config),
                                           'historicalRequestInputPath': old_config_path}
    compatibility = {
        'schema': 'tate-theta-exact-standard-proof-compatibility-v1', 'original': original,
        'standaloneTargetIdentity': None, 'platformJob': platform_receipt['job_id'],
        'nativeLevelParams': native_params, 'sourceLevelParams': source_record['levelParams'],
        'requiredDataConsumers': consumers, 'evidence': evidence,
        'method': 'Actual closed native proof at the exact original proposition-valued instance type; restore its actual query universe to the original universe before expansion.',
        'sourceBodyFailure': platform['genuineSourceBodyAttempt'],
        'scope': 'Only this absent standard instance; project77 named plus1 genuine source proof dimensions remain unchanged.'}
    return compatibility, paths


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--inventory-dir', type=Path)
    parser.add_argument('--output', type=Path, default=HERE / 'audit-config.json')
    parser.add_argument('--original-exprs', type=Path)
    parser.add_argument('--original-view-evidence', type=Path, help='Hash-bound lossless raw/compact token-equivalence report')
    parser.add_argument('--audit-output', type=Path)
    parser.add_argument('--compact-output', action='store_true', help='Serialize complete audit JSON with Json.compress; preserve all checks and values')
    parser.add_argument('--wrapper-report', type=Path)
    parser.add_argument('--standard-source-facts', type=Path)
    parser.add_argument('--standard-source-receipt', type=Path)
    parser.add_argument('--standard-platform-facts', type=Path)
    parser.add_argument('--standard-platform-receipt', type=Path)
    parser.add_argument('--standard-source-query-config', type=Path)
    parser.add_argument('--platform-facts', type=Path)
    parser.add_argument('--platform-receipt', type=Path)
    parser.add_argument('--platform-query-config', type=Path, help='Stable archived configuration whose SHA is bound by the actual platform query receipt')
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
    platform_binding, actual_parent_fact, platform_evidence_paths = platform_helper_evidence(args, export, records)
    standard_compatibility, standard_evidence_paths = standard_proof_evidence(args, export, current, records)
    proof_resolutions = []
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
        if n == 'TateCurvesTheta.TateParameter.tateJ.eq_1':
            assert record['selected'] and record['constantKind'] == 'theorem' and record['isProposition']
            assert not record['isInstance'] and record['valueExpr'] is not None
            proof_resolutions.append({
                'original': n, 'originalName': record['nameExpr'], 'sourceRecord': record,
                'standaloneTargetIdentity': None,
                'expectedSourceAxioms': [name(ax) for ax in d['axioms']],
                'parentOriginal': 'TateCurvesTheta.TateParameter.tateJ',
                'actualParentFact': actual_parent_fact,
                'parentWholeValueEqualityRequired': True,
                'parentKernelDefinitionalValueEqualityRequired': True,
                'resolutionPolicy': 'Kernel-check the genuine exported source proof at its exact relocated type; no target theorem identity.'})
            continue
        project_map.append({
            'original': n, 'originalName': record['nameExpr'],
            'target': 'AbcAdaptation.Reference.' + n,
            'targetName': prepend(name('AbcAdaptation.Reference'), record['nameExpr']),
            'required': record['selected'], 'mappingRole': 'current-unit',
            'targetToSourceUniverseIndices': None,
            'expectedIsInstance': d['isInstance'],
            'expectedSourceAxioms': [name(ax) for ax in d['axioms']]})
    assert len(excluded) == 6 and len(project_map) == 152 and len(proof_resolutions) == 1
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
    evidence_paths += standard_evidence_paths + platform_evidence_paths + serialization_view_evidence + prior_evidence + [Path(r['path']) for r in dep['priorEvidence']] + [Path(r['file']) for r in dependencies]
    evidence_paths = list(dict.fromkeys(p.resolve() for p in evidence_paths))
    config = {
        'schema': 'next-carrier-kernel-audit-config-v3',
        'inventorySha256': export['inventorySha256'], 'graphSha256': export['graphSha256'],
        'expectedRecordCount': len(current), 'expectedSelectedCount': 78, 'expectedNamedSelectedCount': 77,
        'expectedProofValueResolutionCount': 1, 'expectedTargetOnlyCompilerDeclarations': [],
        'proofValueResolutions': proof_resolutions, 'platformHelperEvidence': platform_binding,
        'expectedModuleCount': len(modules),
        'standardProofCompatibility': standard_compatibility,
        'auditorStandardImports': ['Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients'],
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
        'standardRenamePolicy': 'No standard renames or equality fallbacks. Only the exact absent tateJ.eq_1 theorem uses its genuine exported source proof value.',
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
    header = 'import Lean\n' + ''.join('import ' + m + '\n' for m in config['auditorStandardImports'])
    header += ''.join('import ' + r['wrappedModule'] + '\n' for r in dependencies)
    header += ''.join('import ' + r['target'] + '\n' for r in modules)
    (HERE / 'AuditNextCarriers.lean').write_text(header + '\n' + template[template.index('/-! Stable JSON'):])
    print(json.dumps({'config': str(args.output.resolve()), 'sha256': sha(args.output),
                      'newDeclarations': len(current), 'newSelected': 78, 'newNamedSelected': 77,
                      'sourceProofValueResolutions': len(proof_resolutions), 'excludedPrivateNoTarget': len(excluded),
                      'requiredAcceptedPriorIdentities': len(required), 'projectMap': len(project_map),
                      'allowedPriorModules': [r['wrappedModule'] for r in dependencies]}, indent=2))


if __name__ == '__main__':
    main()
