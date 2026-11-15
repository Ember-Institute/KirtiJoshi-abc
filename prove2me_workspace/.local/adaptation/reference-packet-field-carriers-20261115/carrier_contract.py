"""Local evidence checks shared by the next-carrier offline generators.

No process launch, compilation, network access, or Git access. Only input files
are read. Lean names are compiler-supplied; this module does not discover names.
"""
import hashlib
import json
from pathlib import Path

MODULES = {
    'Iut.Cor312.Container': 'Container',
    'Iut.Cor312.HolomorphicHull': 'HolomorphicHull',
    'Iut.Cor312.ThetaData.GlobalField': 'GlobalField',
    'Iut.Cor312.ThetaData.PlacesOver': 'PlacesOver',
    'TateCurvesTheta.QParameter.Basic': 'QParameterBasic',
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
        require(audited['provenance'] == p and audited['workingSourceEqualsExactCommitBlob'] is True
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


def dependency_evidence(unit):
    """Load only explicitly accepted, byte-bound prior carrier constants.

    Prior map candidates do not establish presence. `acceptedConstantNames` must
    be the subset validated by a terminal kernel-audit output. The main agent
    supplies that acceptance; this generator binds all source evidence hashes.
    """
    constants = {}
    modules = {}
    descriptors = []
    for item in unit.get('dependencies', []):
        require(sha(item['typedMap']) == item['typedMapSha256'], 'Prior typed map changed')
        typed = load(item['typedMap'])
        require(typed['prefix'] == PREFIX, 'Prior wrapper namespace differs')
        require(item['status'] == 'accepted-kernel-audit', 'Prior dependency kernel audit not accepted')
        require(item['auditEvidence'], 'Prior dependency lacks audit evidence')
        for evidence in item['auditEvidence']:
            require(sha(evidence['path']) == evidence['sha256'], 'Prior audit evidence changed')
        audits = [e for e in item['auditEvidence'] if e.get('kind') == 'kernel-audit']
        receipts = [e for e in item['auditEvidence'] if e.get('kind') == 'ci-result']
        require(len(audits) == len(receipts) == 1, 'Prior dependency needs one kernel audit and one scheduler receipt')
        audit, receipt = load(audits[0]['path']), load(receipts[0]['path'])
        require(receipt['status'] == 'succeeded' and receipt['result']['exit_code'] == 0,
                'Prior kernel audit scheduler receipt is not successful')
        snapshot = receipt['result']['snapshot']
        require(snapshot['workspace_mode'] == 'exclusive_worktree' and snapshot['snapshot_id'] is None,
                'Prior audit workspace mode differs')
        require(receipt['result']['review']['passed'] is True and not audit['hasSorryAx']
                and audit['allOwnedTypeValueClosuresStandardAxiomsOnly'] is True,
                'Prior kernel/axiom review did not pass')
        config_path = receipt['request']['environment']['FOUNDATION_AUDIT_CONFIG']
        require(load(config_path) == audit['configuration'], 'Prior kernel output not bound to scheduler configuration')
        require((Path(audit['configuration']['outputDir']) / 'foundation-kernel-audit.json').resolve()
                == Path(audits[0]['path']).resolve(), 'Prior kernel output path differs from scheduler config')
        require(all(c['kernelTypeEqual'] and c['binderInfoPlacementEqual'] and c['allExpressionBinderInfoEqual']
                    and c['computationShapeEqual'] and c['instanceRegistryMatchesAcceptedGraph']
                    for c in audit['comparisons']), 'Prior kernel pair comparison failed')
        accepted = set(item['acceptedConstantNames'])
        require(accepted == {c['original'] for c in audit['comparisons']},
                'Prior accepted dependency names differ from actual compared constants')
        require(accepted, 'Prior dependency acceptance has no constants')
        typed_constants = {c['originalName']: c for c in typed['constants']}
        require(accepted <= set(typed_constants), 'Prior acceptance names absent from typed map')
        paths = {m['originalModule']: m for m in item['modules']}
        original_modules = {m['originalModule']: m for m in typed['modules']}
        for module, record in paths.items():
            require(module in original_modules, 'Prior module absent from typed map')
            expected = original_modules[module]
            require(record['wrappedModule'] == expected['wrappedModule'] == canonical_module(module), 'Noncanonical prior module replacement')
            require(sha(record['path']) == record['sha256'] == expected['wrappedSha256'], 'Actual delivered Definitions differs from typed map')
            require(module not in modules, 'Duplicate prior delivered module')
            modules[module] = record
        for name in sorted(accepted):
            c = dict(typed_constants[name])
            require(c['originalModule'] in modules and project_name(name), 'Accepted prior constant lacks delivered module')
            require(name not in constants, 'Duplicate accepted prior constant')
            c.update(mappingRole='prior-delivered', dependencyTypedMap=item['typedMap'],
                     dependencyTypedMapSha256=item['typedMapSha256'], dependencyAuditEvidence=item['auditEvidence'])
            constants[name] = c
        descriptors.append(item)
    return constants, modules, descriptors


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
    require(all(name.startswith('Mathlib.') or name in allowed for name in imports),
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
