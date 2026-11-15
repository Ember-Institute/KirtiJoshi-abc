#!/usr/bin/env python3
"""Validate this uncompiled scaffold and its accepted evidence without invoking tools."""
import ast
import difflib
import hashlib
import importlib.util
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
W = Path('/home/admin-wsl/Coq/abc/prove2me_workspace')
PRIOR = W / '.local/adaptation/reference-volume-tate-carriers-20261115'
INV = Path('/tmp/p2m-tate-theta-inventory-v5-20261115')
EXPORTER = Path('/tmp/p2m-tate-theta-tools-v5-20261115/QueryNextCarrierOriginalExprs.lean')

def read(p): return json.loads(p.read_text())
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def dump(p, x): p.write_text(json.dumps(x, indent=2, ensure_ascii=False) + '\n')
def require(x, label):
    if not x: raise ValueError(label)

script = HERE / 'prepare_audit_config.py'
ast.parse(script.read_text())
spec = importlib.util.spec_from_file_location('audit_config_scaffold', script)
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)
actual, evidence = module.accepted_prior()
inventory = read(INV / 'inventory.json')
export = read(INV / 'export-config.json')
dep = read(INV / 'dependency-closure.json')
require(sha(INV / 'inventory.json') == export['inventorySha256'], 'Inventory hash')
require(inventory['graphSha256'] == export['graphSha256'] == dep['graphSha256'], 'Graph hash bindings')
require(sha(Path(inventory['graph'])) == inventory['graphSha256'], 'Actual accepted graph hash')
require([m['module'] for m in inventory['modules']] == module.EXPECTED_MODULES, 'Four exact source module paths')
current = {d['name']: d for m in inventory['modules'] for d in m['declarations']}
private = {n for n, d in current.items() if d['isPrivate']}
selected = {n for n, d in current.items() if d['selectedForBundle']}
require(len(current) == 117 and len(selected) == 78 and len(private) == 6, '117/78/6 source dimensions')
require(not selected & private, 'No selected private constants')
require(sum(len(m['selectedSourceCommandCandidates']) for m in inventory['modules']) == 20, '20 exact source command roots')
require({'Iut.galPointMap_torsionBy', 'Iut.TateStructure.ofUnit_mul', 'Iut.TateStructure.ofUnit_one', 'Iut.TateStructure.ofUnit_inv'} <= selected, 'Four genuine helper proofs remain selected')
require(all(current[n]['module'] == 'TateCurvesTheta.TateCurve.Parametrization' for n in private), 'Private owner')
for n in selected:
    for field in ['directTypeDeps', 'directValueDeps', 'typeDeps', 'valueDeps']:
        require(not set(current[n][field]) & private, 'Selected closure references source private: ' + n)
require(all(r['nameExpr'] is None for r in export['records']), 'No inferred compiler Name components')
for d in current.values():
    require(not d['hasSorryAx'] and set(d['axioms']) <= module.ALLOWED_AXIOMS, 'Accepted graph axiom closure: ' + d['name'])
required = dep['requiredPriorActualPairs']
require(len(required) == 42 and set(dep['requiredPriorConstants']) == {r['original'] for r in required}, 'Required42 prior identities')
for r in required:
    a = actual[r['original']]
    require(a['target'] == r['target'] and a['sourceOwner'] == r['sourceOwner'], 'Required accepted identity: ' + r['original'])
    require(a['originalName'] == r['originalName'], 'Actual source structural Name: ' + r['original'])
    if r['targetName'] is not None:
        require(a['targetName'] == r['targetName'], 'Actual target structural Name: ' + r['original'])
require(len(actual) == dep['availableAcceptedNamedCount'] == 339, '339 accepted actual prior names')
require(dep['requiredPriorProofValueResolutions'] == [], 'No prior proof-value resolution required')
bundles = {r['wrappedModule']: r for r in dep['importedBundles']}
needed = {module.target_module(r['sourceOwner']) for r in required}
while True:
    expanded = set(needed)
    for n in needed:
        row = bundles[n]
        require(sha(Path(row['file'])) == row['sha256'], 'Prior bundle stable: ' + n)
        for line in Path(row['file']).read_text().splitlines():
            if line.startswith('import Definitions.'):
                expanded.add(line.removeprefix('import ').strip())
    if expanded == needed: break
    needed = expanded
for r in dep['priorEvidence']:
    require(sha(Path(r['path'])) == r['sha256'], 'Prior supplier evidence hash')
old = (PRIOR / 'AuditNextCarriers.lean').read_text()
new = (HERE / 'AuditNextCarriers.template.lean').read_text()
require(all(token not in new for token in ['installDecidable', 'exactDecidable', 'standardExpansions', 'proveGeneratedEliminatorEquality', 'IsUniformizer']), 'No previous unit compatibility paths')
require('kernelTermEq s!"original versus target computational value' in new, 'Strict full data-body kernel equality')
require(all(token in new for token in ['binderPlacement sourceType == binderPlacement targetType', 'structureShape info (inverseRelocated rs)', 'recursor rule {original}', 'excludedSourceNames.contains n', 'Accepted prior target Name is not unique at expected owner']), 'Retained strict metadata and actual Name guards')
export_old = (PRIOR / 'QueryNextCarrierOriginalExprs.lean').read_text()
export_new = EXPORTER.read_text()
def block(s, a, b): return s[s.index(a):s.index(b, s.index(a))]
require(block(export_old, 'abbrev AxiomCache', 'partial def binderInventory') == block(export_new, 'abbrev AxiomCache', 'partial def binderInventory'), 'Exporter cache-v2 unchanged')
require(block(export_old, 'def moduleOf', 'def standardAxioms') == block(export_new, 'def moduleOf', 'def standardAxioms'), 'Exporter indexed source owner unchanged')
require('Name.num' not in export_new or '.num p n => Json.arr' in export_new, 'Structural Name encoding')
require('Std.HashMap String (Array Name)' in export_new and 'matchingNames.size == 1' in export_new, 'Exporter actual Name display uniqueness')
for filename, before, after in [('auditor-from-accepted-v5.diff', old, new), ('exporter-from-accepted-cache-v2.diff', export_old, export_new)]:
    (HERE / filename).write_text(''.join(difflib.unified_diff(before.splitlines(True), after.splitlines(True), fromfile='accepted-prior/' + filename, tofile='tate-theta-draft/' + filename)))
dump(HERE / 'source-axiom-inventory.draft.json', {
    'schema': 'tate-theta-source-axiom-inventory-graph-draft-v1',
    'status': 'accepted-source-graph-evidence-current-platform-unit-not-compiled',
    'graphSha256': inventory['graphSha256'], 'inventorySha256': export['inventorySha256'],
    'standardAxioms': sorted(module.ALLOWED_AXIOMS), 'hasSorryAx': False,
    'newModuleCount': 4, 'newDeclarationCount': 117, 'newSelectedDeclarationCount': 78,
    'declarations': [{'name': n, 'nameExpr': None, 'nameResolutionStatus': 'pending-original-compiler-export',
                      'module': d['module'], 'selected': d['selectedForBundle'],
                      'isPrivate': d['isPrivate'], 'isInstance': d['isInstance'],
                      'axioms': d['axioms'], 'hasSorryAx': d['hasSorryAx']} for n, d in sorted(current.items())]})
dump(HERE / 'static-validation.json', {
    'schema': 'tate-theta-kernel-scaffold-static-validation-v1', 'status': 'static-checks-passed-not-compiled',
    'pythonAstParsed': True, 'acceptedPriorEvidenceVerified': True, 'acceptedPriorActualNamedCount': len(actual),
    'requiredPriorActualNamedCount': len(required), 'newSourceRecordCount': 117, 'newSelectedCount': 78, 'sourceCommandRootCount': 20,
    'privateUnselectedSourceRecords': sorted(private), 'sourcePrivateNamesRequiredBySelectedClosures': [],
    'expectedCurrentPublicMappingCount': 111, 'expectedTotalRelocationCount': 153,
    'allowedPriorModules': sorted(needed), 'priorCompatibilityPathsRemoved': True,
    'allSelectedNeedNamedComparisons': True, 'sourceProofValueElisionsConfigured': 0,
    'strictFullDataBodyKernelEquality': True, 'completeStructureAndRecursorMetadataChecks': True,
    'cacheV2AndIndexed435SourceOwnerUnchanged': True, 'actualCurrentCompilerNamesPending': True,
    'currentAuditConfigurationGenerated': False, 'currentComparisonsPerformed': False,
    'leanCompilationPerformed': False, 'ciSubmitted': False, 'mainWorkspaceEdited': False})
dump(HERE / 'provenance.json', {
    'schema': 'tate-theta-kernel-scaffold-provenance-v1',
    'acceptedAuditor': {'path': str(PRIOR / 'AuditNextCarriers.lean'), 'sha256': sha(PRIOR / 'AuditNextCarriers.lean'), 'job': 'ci-013964-cce30c9e'},
    'acceptedExporter': {'path': str(PRIOR / 'QueryNextCarrierOriginalExprs.lean'), 'sha256': sha(PRIOR / 'QueryNextCarrierOriginalExprs.lean'), 'acceptance': str(PRIOR / 'original-exprs-acceptance.json')},
    'draftExporter': {'path': str(EXPORTER), 'sha256': sha(EXPORTER)},
    'draftAuditorTemplate': {'path': str(HERE / 'AuditNextCarriers.template.lean'), 'sha256': sha(HERE / 'AuditNextCarriers.template.lean')},
    'generator': {'path': str(script), 'sha256': sha(script)},
    'currentInventory': {'path': str(INV / 'inventory.json'), 'sha256': sha(INV / 'inventory.json')},
    'currentDependencyClosure': {'path': str(INV / 'dependency-closure.json'), 'sha256': sha(INV / 'dependency-closure.json')},
    'priorEvidence': [{'path': str(p), 'sha256': sha(p)} for p in evidence],
    'modifications': ['Remove all previous-unit Decidable transport, source-proof expansions, instance equality exceptions and IsUniformizer extensional eliminator equality.',
                      'Require kernel definitional equality for every exported computational data body.',
                      'Keep all117 original records; exclude six unselected private actual Names from target mapping, reject their use during relocation.',
                      'Resolve legacy foundation target Name components from the actual platform environment by unique accepted display plus owner.',
                      'Require actual original Expr output and wrapper report before final configuration generation.']})
print(json.dumps({'status': 'static-checks-passed-not-compiled', 'acceptedPrior': 339, 'requiredPrior': 42, 'original': 117, 'selected': 78, 'excludedPrivate': 6, 'plannedRelocations': 153, 'priorModules': len(needed)}))
