"""Local evidence checks shared by the next-carrier offline generators.

No process launch, compilation, network access, or Git access. Only input files
are read. Lean names are compiler-supplied; this module does not discover names.
"""
import hashlib
import difflib
import json
from pathlib import Path

MODULES = {'TateCurvesTheta.TateCurve.JInvariant': 'JInvariant', 'TateCurvesTheta.TateCurve.Parametrization': 'Parametrization', 'Iut.Cor312.ThetaData.AdmissiblePrime': 'AdmissiblePrime', 'Iut.Cor312.ThetaData.TateStructure': 'TateStructure'}

CONTEXT_IMPORTS = {
    'TateCurvesTheta.TateCurve.JInvariant': ['Mathlib.Topology.MetricSpace.Ultra.Basic'],
    'TateCurvesTheta.TateCurve.Parametrization': ['Mathlib.Topology.MetricSpace.Ultra.Basic'],
}
PREFIX = 'AbcAdaptation.Reference'
PROJECT_PREFIXES = ('Iut', 'TateCurvesTheta')


def require(ok, message):
    if not ok:
        raise ValueError(message)


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def load(path):
    return json.loads(Path(path).read_text())


def project_name(name):
    return any(name == p or name.startswith(p + '.') for p in PROJECT_PREFIXES)


def canonical_module(module):
    return 'Definitions.Def_AbcAdaptation_Reference_' + module.replace('.', '_')


def unit_config(path):
    unit = load(path)
    require(unit['schema'] == 'reference-carrier-unit-v1', 'Unexpected unit config schema')
    require(set(unit['projectPrefixes']) == set(PROJECT_PREFIXES), 'Structural project prefix scope differs')
    require(unit['prefixMap'] == {p: PREFIX + '.' + p for p in PROJECT_PREFIXES}, 'Structural prefix map differs')
    audit_info = unit['sourceProvenanceAudit']
    require(sha(audit_info['path']) == audit_info['sha256'], 'Source Git provenance audit changed')
    audit = load(audit_info['path'])
    require(audit['schema'] == 'next-carrier-source-provenance-audit-v1', 'Unexpected source provenance audit')
    provenance_records = {r['module']: r for r in audit['records']}
    sources = {s['module']: s for s in unit['sources']}
    require(len(sources) == len(unit['sources']) and set(sources) == set(MODULES), 'Unit source module set differs')
    for module, source in sources.items():
        p = source['provenance']
        audited = provenance_records[module]
        require(audited['provenance'] == p and audited['workingSourceEqualsExactCommitBlob'] is (not p.get('sourceOverridden', False))
                and audited['sourceCommit'] == p['originalCommit'] and audited['gitBlobObject'] == p['sourceGitObject']
                and audited['sha256'] == source['sourceSha256']
                and audited['actualOrigin'].removesuffix('.git') == p['originalRepository'].removesuffix('.git'),
                'Actual repository Git source provenance differs: ' + module)
        for key in ['originalSourcePath', 'originalAuthors', 'originalRepository', 'originalCommit', 'originalLicense']:
            require(isinstance(p[key], str) and p[key], 'Missing provenance ' + key + ': ' + module)
            require('\n' not in p[key] and '\r' not in p[key] and '-/' not in p[key], 'Unsafe provenance field: ' + key)
        require(len(p['originalCommit']) == 40 and all(c in '0123456789abcdef' for c in p['originalCommit']), 'Provenance commit is not a full Git SHA')
        require(p['originalLicense'] == 'Apache-2.0', 'Unsupported source license')
        raw = Path(source['source']).read_bytes()
        require(sha(source['source']) == source['sourceSha256'] == p['sourceSha256'], 'Provenance source bytes changed')
        git_blob = hashlib.sha1(b'blob ' + str(len(raw)).encode() + b'\0' + raw).hexdigest()
        require(not p.get('sourceOverridden', False), 'This four-module unit permits no source override')
        require(p['sourceGitBlobMatches'] is True and git_blob == p['sourceGitObject']
                and p['actualGitRepository'], 'Source differs from recorded Git blob')
        if p.get('licenseFile') is not None:
            require(sha(p['licenseFile']) == p['licenseSha256'], 'Unbound source license file')
        else:
            require(p.get('sourceHeaderSha256') and p.get('licenseEvidence')
                    and p.get('repositoryLicenseFiles') == [], 'Absent license file lacks source-header evidence')
        evidence = p['evidence']
        require(evidence and all(sha(e['path']) == e['sha256'] for e in evidence), 'Source provenance evidence changed')
        require(any(Path(e['path']).resolve() == Path(source['source']).resolve() for e in evidence),
                'Provenance does not include actual source artifact')
        manifests = [load(e['path']) for e in evidence if Path(e['path']).name == 'lake-manifest.json']
        if module.startswith('TateCurvesTheta.'):
            matches = [r for manifest in manifests for r in manifest['packages']
                       if r.get('url') == p['originalRepository'] and r.get('rev') == p['originalCommit']]
            require(len(matches) == 1 and matches[0] == p['manifestPackage'],
                    'Tate repository/commit differs from actual dependency manifest')
    return unit


def validate_prior_comparison(c, packet_field=False):
    require(c['kernelTypeEqual'] and c['computationShapeEqual']
            and c['instanceRegistryMatchesAcceptedGraph'], 'Prior kernel type/shape/instance comparison failed')
    strict = c['binderInfoPlacementEqual'] and c['allExpressionBinderInfoEqual']
    if not strict:
        require(packet_field and c['original'] == 'Iut.solvableClosure._proof_3'
                and c['target'] == PREFIX + '.Iut.solvableClosure._proof_2'
                and c['exposedBinderInfoEqual'] is True
                and c['implementationDataInstanceKernelEqual'] is True
                and c['binderImplementationDifferenceAccountedFor'] is True,
                'Unaccepted prior BinderInfo mismatch')
        e = c['internalBinderImplementationEvidence']
        require(e['allEightExposedPiBindersAndDomainsStrictlyEqual'] is True
                and e['allThreeMathematicalTypeArgumentBindersStrictlyEqual'] is True
                and e['implementationDataInstanceKernelEqual'] is True
                and e['binderImplementationDifferenceAccountedFor'] is True,
                'Missing exact exposed/SMul evidence')
        pairs = e['instanceComparisons']
        require(len(pairs) == 3 and {r['IsScalarTowerArgumentIndex'] for r in pairs} == {3, 4, 5}
                and all(r['dataInstanceType'] == 'SMul' and r['isProofSubterm'] is False
                        and r['closedOverAllEightParameters'] is True
                        and r['closedDataInstanceTypesAndValuesKernelEqual'] is True
                        and r['allImplementationBindersDefaultLambdas'] is True for r in pairs),
                'Prior SMul data instance evidence incomplete')
    if packet_field and c['computationalValueEqualityChecked'] and not c['kernelValueEqual']:
        require(c['original'] == 'Iut.IsInitialThetaGlobalData.casesOn'
                and c['kernelPropositionalValueEquality'] is True, 'Unaccepted prior computational value mismatch')
        e = c['propositionalValueEqualityEvidence']
        require(e['kernelCheckedPropositionalValueEquality'] is True and e['hasSorryAx'] is False
                and e['extensionalArgumentCount'] == 12 and e['constructorFieldCount'] == 6
                and e['exactFullValueEquality'] and e['kernelCheckedEqualityProof']
                and set(e['axioms']) <= {'propext', 'Classical.choice', 'Quot.sound'},
                'Missing accepted casesOn full-value equality')


def dependency_evidence(unit):
    """Return actual accepted named targets only; proof elisions remain evidence.

    Raw typed maps supply source metadata and module hashes. They never override
    the actual compiler pair, in particular old proof 3 maps to target proof 2.
    This unit needs no prior proof-value resolver, and exports none.
    """
    constants, modules, descriptors = {}, {}, []
    for item in unit.get('dependencies', []):
        require(sha(item['typedMap']) == item['typedMapSha256'], 'Prior typed map changed')
        typed = load(item['typedMap'])
        require(typed['prefix'] == PREFIX, 'Prior wrapper namespace differs')
        require(item['status'] == 'accepted-kernel-audit', 'Prior dependency audit not accepted')
        for evidence in item['auditEvidence']:
            require(sha(evidence['path']) == evidence['sha256'], 'Prior audit evidence changed')
        audits = [e for e in item['auditEvidence'] if e.get('kind') == 'kernel-audit']
        receipts = [e for e in item['auditEvidence'] if e.get('kind') == 'ci-result']
        require(len(audits) == len(receipts) == 1, 'Need one kernel audit and scheduler receipt')
        audit, receipt = load(audits[0]['path']), load(receipts[0]['path'])
        volume_tate = item.get('acceptedCorrespondence', {}).get('unitKind') == 'volume-tate'
        packet_field = audit['schema'] == 'next-carrier-kernel-audit-v3' and not volume_tate
        require(packet_field or volume_tate or audit['schema'] == 'foundation-kernel-audit-v2', 'Unsupported prior audit schema')
        require(receipt['status'] == 'succeeded' and receipt['result']['exit_code'] == 0,
                'Prior kernel audit scheduler receipt not successful')
        snapshot = receipt['result']['snapshot']
        require(snapshot['workspace_mode'] == 'exclusive_worktree' and snapshot['snapshot_id'] is None,
                'Prior audit workspace mode differs')
        require(receipt['result']['review']['passed'] is True and audit['hasSorryAx'] is False
                and audit['allOwnedTypeValueClosuresStandardAxiomsOnly'] is True, 'Prior kernel/axiom review failed')
        env_key = 'NEXT_CARRIER_AUDIT_CONFIG' if packet_field or volume_tate else 'FOUNDATION_AUDIT_CONFIG'
        require(load(receipt['request']['environment'][env_key]) == audit['configuration'],
                'Prior output not bound to scheduler config')
        basename = 'next-carrier-kernel-audit.json' if packet_field or volume_tate else 'foundation-kernel-audit.json'
        require((Path(audit['configuration']['outputDir']) / basename).resolve() == Path(audits[0]['path']).resolve(),
                'Prior audit output path differs')
        comparisons = {c['original']: c for c in audit['comparisons']}
        require(len(comparisons) == len(audit['comparisons']), 'Duplicate prior original comparison')
        for c in comparisons.values():
            validate_prior_comparison(c, packet_field)
        accepted = set(item['acceptedConstantNames'])
        require(accepted == set(comparisons) and accepted, 'Accepted names differ from actual kernel comparisons')
        typed_constants = {c['originalName']: c for c in typed['constants']}
        require(accepted <= set(typed_constants), 'Accepted names absent from provenance map')
        if volume_tate:
            validate_volume_dependency(item, audit, receipt, comparisons)
        if packet_field:
            evidence = item['acceptedCorrespondence']
            require(sha(evidence['path']) == evidence['sha256'], 'Accepted correspondence changed')
            correspondence = load(evidence['path'])
            require(correspondence['schema'] == 'reference-packet-field-accepted-compiler-correspondence-v1'
                    and correspondence['status'] == 'accepted-kernel-audit'
                    and correspondence['job_id'] == receipt['job_id'] == 'ci-013658-36534ff1'
                    and correspondence['receiptSha256'] == receipts[0]['sha256']
                    and correspondence['auditSha256'] == audits[0]['sha256'], 'Correspondence is not accepted v4 evidence')
            named = {c['original']: c for c in correspondence['namedPairs']}
            require(len(named) == correspondence['actualNamedComparisons'] == len(comparisons) == 131
                    and set(named) == accepted, 'Correspondence actual named set differs')
            elisions = correspondence['proofValueResolutions']
            require(correspondence['sourceSelectedCount'] == 133
                    and correspondence['internalProofValueResolutions'] == len(elisions) == 2
                    and {c['original'] for c in elisions} == {'Iut.solvableClosure._proof_2', 'Iut.solvableClosure._proof_4'}
                    and all(c['standaloneTargetIdentity'] is None
                            and c['resolution'] == 'genuine-exported-original-proof-value'
                            and c['ownerTypeKernelEqual'] is True and c['ownerComputationalValueKernelEqual'] is True
                            for c in elisions), 'Elisions must remain genuine proof-value evidence without named identities')
            for name, pair in named.items():
                c = comparisons[name]
                require(all(pair[k] == c[k] for k in ['originalName', 'target', 'targetName', 'targetToSourceUniverseIndices']),
                        'Accepted actual compiler pair differs from audit')
        original_modules = {m['originalModule']: m for m in typed['modules']}
        for record in item['modules']:
            module = record['originalModule']
            expected = original_modules[module]
            require(record['wrappedModule'] == expected['wrappedModule'] == canonical_module(module), 'Noncanonical prior module')
            require(sha(record['path']) == record['sha256'] == expected['wrappedSha256'], 'Delivered Definitions differ from accepted bytes')
            require(module not in modules, 'Duplicate prior delivered module')
            modules[module] = record
        for name in sorted(accepted):
            c, actual = dict(typed_constants[name]), comparisons[name]
            require(c['originalModule'] in modules and project_name(name), 'Prior constant lacks delivered module')
            require(name not in constants, 'Duplicate accepted prior constant')
            if not packet_field and not volume_tate:
                require(c['wrappedName'] == actual['target'], 'Foundation map differs from actual target')
            c.update(wrappedName=actual['target'], wrappedNameExpr=actual.get('targetName', c['wrappedNameExpr']),
                     targetToSourceUniverseIndices=actual.get('targetToSourceUniverseIndices'),
                     mappingRole='prior-delivered', mappingStatus='accepted-actual-compiler-correspondence',
                     dependencyTypedMap=item['typedMap'], dependencyTypedMapSha256=item['typedMapSha256'],
                     dependencyAuditEvidence=item['auditEvidence'])
            constants[name] = c
        descriptors.append(item)
    return constants, modules, descriptors


def validate_volume_dependency(item, audit, receipt, comparisons):
    """Accept only the prior actual98; neither elided source proofs gets a Name."""
    evidence = item['acceptedCorrespondence']
    require(sha(evidence['path']) == evidence['sha256'], 'Volume correspondence changed')
    c = load(evidence['path'])
    require(c['schema'] == 'reference-volume-tate-accepted-compiler-correspondence-v1'
            and c['status'] == 'accepted-kernel-audit'
            and c['job_id'] == receipt['job_id'] == 'ci-013964-cce30c9e', 'Unaccepted volume final-v5 receipt')
    require(c['receiptSha256'] == sha(c['receipt']) and load(c['receipt']) == receipt
            and c['auditSha256'] == sha(c['audit']) and load(c['audit']) == audit,
            'Volume correspondence audit or receipt differs')
    require(c['sourceSelectedCount'] == c['sourceObligationsResolved'] == 100
            and c['actualNamedComparisons'] == c['selectedNamedComparisons'] == len(comparisons) == 98
            and c['unselectedNamedComparisons'] == 0 and c['internalProofValueResolutions'] == 2,
            'Volume actual named/proof-value partition differs')
    named = {r['original']: r for r in c['namedPairs']}
    require(set(named) == set(comparisons) == set(item['acceptedConstantNames']), 'Volume actual98 set differs')
    for name, pair in named.items():
        actual = comparisons[name]
        require(all(pair[k] == actual[k] for k in ['originalName', 'target', 'targetName', 'targetToSourceUniverseIndices']),
                'Volume actual structural correspondence differs: ' + name)
        require(actual['completeStructureMetadataEqual'] and actual['sourceAxiomInventoryMatchesAcceptedGraph'],
                'Volume complete structure or axiom inventory failed')
        if not actual['proofDeclaration'] and actual['sourceRecord']['valueExpr'] is not None:
            require(actual['computationalValueEqualityChecked'] and
                    (actual['kernelValueEqual'] or actual['kernelPropositionalValueEquality']), 'Volume full value not checked')
    elided = {'TateCurvesTheta.OrderedTateParameter.decidable._proof_1', 'TateCurvesTheta.PrimeToOrder.decidable._proof_1'}
    resolutions = {r['original']: r for r in c['proofValueResolutions']}
    require(set(resolutions) == elided and not set(named) & elided,
            'Volume elided proofs acquired named identities')
    require(all(r['standaloneTargetIdentity'] is None and r['resolution'] == 'genuine-exported-original-proof-value'
                and r['genuineOriginalValueInhabitsExactOriginalType'] is True
                and r['parentWholeValueEqualityRequired'] is True for r in resolutions.values()),
            'Volume proof elision evidence differs')


def validate_source_imports(module, imports, prior_modules):
    require(imports and len(imports) == len(set(imports)), 'Empty/duplicate reviewed source imports')
    for name in imports:
        require(all(c.isalnum() or c in '._' for c in name), 'Unsafe source import name')
        require(name.startswith(('Mathlib.', 'Init.', 'Lean.')) or name in MODULES or name in prior_modules,
                'Unclassified source dependency import: ' + name)
        require(name != module, 'Small source must not import its original module')


def validate_platform_imports(module, imports, prior_modules):
    require(imports and len(imports) == len(set(imports)), 'Empty/duplicate reviewed platform imports')
    allowed = {canonical_module(m) for m in MODULES if m != module} | {r['wrappedModule'] for r in prior_modules.values()}
    require(all(name.startswith('Mathlib.') or name in {'Lean.Elab.Tactic.Omega', 'Lean.Elab.Tactic.NormCast'} or name in allowed for name in imports),
            'Platform contains non-Definitions project dependency or unknown carrier')
    require(all(all(c.isalnum() or c in '._' for c in name) for name in imports), 'Unsafe platform import name')


def validate_import_graph(plans, prior_modules):
    edges = {module: set(plan['platform433Candidates']) & {canonical_module(m) for m in MODULES}
             for module, plan in plans.items()}
    active, done = set(), set()
    def visit(module):
        require(module not in active, 'Cyclic peer Definitions import: ' + module)
        if module in done:
            return
        active.add(module)
        for child in MODULES:
            if canonical_module(child) in edges[module]:
                visit(child)
        active.remove(module)
        done.add(module)
    for module in MODULES:
        validate_source_imports(module, plans[module]['source435Imports'], prior_modules)
        validate_platform_imports(module, plans[module]['platform433Candidates'], prior_modules)
        visit(module)
