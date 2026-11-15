#!/usr/bin/env python3
"""Prepare one private Orbicurve Definition offline. No API, CI, or Git calls."""
import sys
sys.dont_write_bytecode = True
import argparse
import hashlib
import json
from pathlib import Path

W = Path('/home/admin-wsl/Coq/abc/prove2me_workspace')
I = W / '.local/adaptation/reference-initial-theta-carriers-20261115'
D = Path('/tmp/p2m-initial-theta-final200-closure-v8-20261116/orbicurve70-dossier')
MODULE = 'Iut.Cor312.ThetaData.Orbicurve'
NAME = 'AbcAdaptation_Reference_Iut_Cor312_ThetaData_Orbicurve'
PROOF = 'Iut.OrbicurveDataSection.XK._proof_1'
TARGET = 'Definitions/Def_' + NAME + '.lean'
PACKET_SCHEMA = 'reference-orbicurve70-private-definition-delivery-v1'
READY_SCHEMA = 'reference-orbicurve70-private-definition-ready-v1'
GATES = ['new_leaf_modules', 'checks_axioms', 'wrapped_kernel_type_identity',
         'new_leaf_artifacts', 'import_audit', 'act1scene1', 'axiom_audit',
         'independent_readbacks', 'source_ledger_consumers', 'git_diff_check',
         'existing_mission_scope', 'final_frozen_review']
CI_GATES = GATES[:7]
COVERAGE = {'source': 71, 'resolved': 71, 'named': 70, 'proof': 1,
            'standard_proof': 0, 'source_proof_standalone_aliases': 0}
SCOPE = {'module': MODULE, 'scopeAll200': False, 'scopeAllFourModules': False,
         'fourModuleCorrespondenceAccepted': False, 'sourceProofStandaloneAliases': [],
         'pendingModules': ['Iut.Cor312.ThetaData.TateFamily',
                            'Iut.Cor312.ThetaData.LocalConditions',
                            'Iut.Cor312.ThetaData.Basic']}

def need(value, message):
    if not value:
        raise ValueError(message)

def read(path):
    return json.loads(Path(path).read_text())

def sha(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as stream:
        for block in iter(lambda: stream.read(1024**2), b''):
            h.update(block)
    return h.hexdigest()

def pin(path):
    return {'path': str(Path(path).resolve()), 'sha256': sha(path)}

def write(path, value):
    Path(path).write_text(json.dumps(value, ensure_ascii=False, indent=2) + '\n')

def verify_pin(binding):
    need(sha(binding['path']) == binding['sha256'], 'Changed input: ' + binding['path'])

def prepare(out):
    out = Path(out).resolve()
    need(out.is_relative_to('/tmp'), 'Output must remain under /tmp')
    out.mkdir(parents=True, exist_ok=True)
    dossier_path = D / 'orbicurve70-dossier.json'
    dossier = read(dossier_path)
    for key in ['actualReceipt', 'audit', 'auditSource', 'auditConfig',
                'currentInstalledTarget', 'originalNativeSource', 'sourceModuleView',
                'comparisonCoverage']:
        verify_pin(dossier[key])
    pins_path = D / 'current-input-pins.json'
    pins = read(pins_path)
    need(pins['inputCount'] == len(pins['inputs']) == 38, 'Expected38 actual audit pins')
    for path, digest in pins['inputs'].items():
        need(sha(path) == digest, 'Changed receipt input: ' + path)
    receipt = read(dossier['actualReceipt']['path'])
    q, result = receipt['request'], receipt['result']
    need(receipt['job_id'] == dossier['job_id'] == 'ci-015073-17773638' and
         receipt['status'] == 'succeeded' and result['exit_code'] == 0,
         'Actual Orbicurve audit receipt did not pass')
    need(q['workspace'] == str(W) and q['task_type'] == 'review' and q['target'] == 'file'
         and q['exclusive'] is True and result['actual_arguments'] == ['lean', q['parameters']['source']],
         'Wrong actual Orbicurve audit invocation')
    need(result['snapshot']['workspace_mode'] == 'exclusive_worktree' and
         result['snapshot']['snapshot_id'] is None and result['review']['passed'] is True,
         'Actual exclusive audit review did not pass')
    need(q['worktree_manifest']['input_hashes'] == pins['inputs'] and
         sha(W / q['parameters']['source']) == q['worktree_manifest']['source_sha256'],
         'Receipt input pins differ')
    need(0 < receipt['resources']['peak_rss_bytes'] <= 16 * 1024**3, 'Actual RSS exceeds16GiB')
    audit = read(dossier['audit']['path'])
    config = read(dossier['auditConfig']['path'])
    need(audit['activeOriginalModule'] == MODULE and audit['configuration'] == config,
         'Wrong audit/configuration binding')
    need(audit['requiredNamedComparedCount'] == 70 and
         audit['requiredProofValueResolutionCount'] == 1 and
         audit['requiredSourceDeclarationCount'] == audit['requiredResolvedCount'] == 71,
         'Wrong mandatory per-module coverage')
    need(audit['hasSorryAx'] is False and audit['allOwnedTypeValueClosuresStandardAxiomsOnly'] is True
         and audit['targetOnlyCompilerDeclarations'] == [], 'Unexpected axioms or target-only declarations')
    source_view = read(dossier['sourceModuleView']['path'])
    selected = {row['name']: row for row in source_view['records'] if row['selected']}
    comparisons = audit['comparisons']
    need(len(selected) == 71 and len(comparisons) == 70 and
         {row['original'] for row in comparisons} == set(selected) - {PROOF}, 'Incomplete named audit coverage')
    for row in comparisons:
        need(row['sourceRecord'] == selected[row['original']], 'Source record differs')
        for key in ['kernelTypeEqual', 'expandedOriginalTypeKernelEqual', 'computationShapeEqual',
                    'completeStructureMetadataEqual', 'sourceSignatureBinderInfoSerializationValidated',
                    'sourceTargetSignatureBinderInfoInventoryEqual',
                    'sourceTargetSignatureBinderInfoPlacementEqual', 'instanceRegistryMatchesAcceptedGraph',
                    'sourceAxiomInventoryMatchesAcceptedGraph']:
            need(row[key] is True, 'Failed actual comparison: ' + key)
        need(row['binderInfoComparisonScope'] ==
             'unexpanded-original-exported-signature-after-named-relocation-vs-actual-target-type',
             'Unexpected BinderInfo comparison scope')
        required = not row['sourceRecord']['isProposition'] and row['sourceRecord']['valueExpr'] is not None
        need(row['computationalValueEqualityChecked'] == row['kernelValueEqual'] == required,
             'Missing complete computational-value comparison')
        need(row['recursorRulesCompared'] == len(row['sourceRecord']['recursorRuleRhs']), 'Missing recursor rules')
    proofs = audit['proofValueResolutions']
    need(len(proofs) == 1 and proofs[0]['original'] == PROOF and
         proofs[0]['standaloneTargetIdentity'] is None and proofs[0]['sourceRecord'] == selected[PROOF],
         'Source proof must remain a genuine proof value with no target alias')
    for key in ['exactOriginalTypeKernelChecked', 'genuineOriginalValueInhabitsExactOriginalType',
                'sourceAxiomInventoryMatchesAcceptedGraph', 'expandedDependenciesHaveAllowedOwners',
                'sourceSignatureBinderInfoSerializationValidated', 'inferredTypeFullBinderInfoInventoryEqual',
                'inferredTypeFullBinderInfoPlacementEqual']:
        need(proofs[0][key] is True, 'Missing genuine source proof evidence: ' + key)
    need(next(row for row in comparisons if row['original'] == proofs[0]['parentOriginal'])['kernelValueEqual'] is True,
         'Missing complete parent data equality')
    wrapper_path, blind_path = I/'generated-wrapped/foundation-wrapper-report.json', I/'blind-readbacks.json'
    wrappers, blind = read(wrapper_path), read(blind_path)
    bundles = {row['definitionName']: row for row in wrappers['bundles']}
    generated = bundles[NAME]
    # Reuse the existing two-context/four-input policy without changing it.
    protocol = I / 'delivery.py'
    namespace = {'__name__': 'orbicurve70_read_only_protocol', '__file__': str(protocol)}
    exec(compile(protocol.read_text(), str(protocol), 'exec'), namespace)
    reviews = namespace['validate_independent_readbacks'](blind, bundles)
    rb = next(row for row in blind['bundles'] if row['definition_name'] == NAME)
    need(rb == read(D/'exact-orbicurve-readback.json'), 'Exact Orbicurve readback subset differs')
    code = (W/TARGET).read_text()
    need(sha(W/TARGET) == generated['sha256'] == rb['source_sha256'] ==
         '444de449e7732ec7fac98ad3bb69aa1d3af8d6e36b1a25325d2053416abb02e9', 'Native target bytes differ')
    need(Path(generated['path']).read_bytes() == (W/TARGET).read_bytes(), 'Wrapper bytes differ')
    need(sha(generated['payload']) == generated['payloadSha256'] and
         read(generated['payload']) == {'definition_name': NAME, 'code': code}, 'Generator payload differs')
    provenance = rb['provenance']
    need(rb['passed'] is True and provenance['fresh_context'] is True and
         provenance['input_only_formal_code'] is True and provenance['reviewer_id'] in reviews,
         'Independent readback is incomplete')
    need(sha(provenance['original_artifact']) == provenance['original_artifact_sha256'] and
         sha(generated['blindReadback']['path']) == provenance['input_sha256'] == generated['blindReadback']['sha256'],
         'Independent readback input changed')
    raw_rb = read(provenance['original_artifact'])['bundles'][provenance['original_bundle_index']]
    for key in ['en', 'zh-Hans', 'ja', 'pending_chinese_terms', 'declarations', 'ambiguities']:
        need(rb[key] == raw_rb[key], 'Original independent readback differs: ' + key)
    context_path, ledger_path = I/'paper-context.json', I/'SOURCE_LEDGER.json'
    context, ledger = read(context_path), read(ledger_path)
    paper = next(row for row in context['bundles'] if row['module'] == MODULE)
    need(paper['blocks_definition_delivery'] is False, 'Selected paper context blocks delivery')
    paper_subset = {key: value for key, value in context.items() if key in ['schema', 'language', 'purpose']}
    paper_subset['bundles'] = [paper]
    paper_subset['quotations'] = [row for row in context['quotations'] if row['id'] in paper['quotation_ids']]
    used_papers = {row['paper_id'] for row in paper_subset['quotations']}
    paper_subset['paper_sources'] = {key: value for key, value in context['paper_sources'].items() if key in used_papers}
    need({row['id'] for row in paper_subset['quotations']} == set(paper['quotation_ids']), 'Missing selected paper quotation')
    source_rows = [row for row in ledger['records'] if row['module'] == MODULE]
    need(len(source_rows) == 5 and {row['original'] for row in source_rows} == set(paper['selected_source_commands']),
         'Orbicurve source-command scope differs')
    owned_source = {decl['name']: decl for row in source_rows for decl in row['ownedSourceDeclarations'] if decl['selected']}
    need(set(owned_source) == set(selected), 'Ledger lacks an exact selected source declaration')
    need(all(row['actualConsumers'] and row['fidelity'] for row in source_rows), 'Source consumer/fidelity evidence missing')
    scope_ledger = {'schema': 'orbicurve70-source-consumers-and-actual-audit-bindings-v1',
        'status': 'per-module-audit-bound; final root review pending', 'module': MODULE,
        'sourceLedger': pin(ledger_path), 'sourceCommands': source_rows,
        'structures': [row for row in ledger['structures'] if row['module'] == MODULE],
        'bundle': next(row for row in ledger['bundles'] if row['module'] == MODULE),
        'kernelCoverage': COVERAGE, 'namedCorrespondence': [
            {'original': row['original'], 'target': row['target'], 'originalName': row['originalName'],
             'targetName': row['targetName'], 'audit': dossier['audit'], 'collection': 'comparisons'} for row in comparisons],
        'sourceProofValues': [{'original': PROOF, 'standaloneTargetIdentity': None,
            'parentOriginal': proofs[0]['parentOriginal'], 'audit': dossier['audit'],
            'collection': 'proofValueResolutions'}], 'sourceProofStandaloneAliases': [],
        'consumerScope': 'Accepted original graph edges only. This packet does not add mission-root graph edges.',
        'scope': SCOPE}
    write(out/'source-ledger.Orbicurve.json', scope_ledger)
    write(out/'paper-context.Orbicurve.json', paper_subset)
    write(out/'readback.Orbicurve.json', rb)
    need(len(rb['definition_title']) <= 200, 'Definition title exceeds the API limit')
    payload = {'definition_name': NAME, 'definition_title': rb['definition_title'], 'definition': code,
        'natural_language_statement': namespace['publication_statement'](rb, paper),
        'source': rb['source'], 'env': namespace['ENV'], 'private': True}
    write(out/'payload.json', payload)
    (out/'Definition.lean').write_bytes((W/TARGET).read_bytes())
    annotation_scope = {'signatureBinderInfoInventoryAndPlacementEqual': True,
        'signatureComparisonCount': 70,
        'signatureScope': 'unexpanded original exported signature after named relocation versus actual native target type',
        'computationalValueRawBinderInfoIdentityTested': False,
        'recursorRuleRawBinderInfoIdentityTested': False,
        'mathematicalComputationalValuesKernelDefinitionalEqual': 49,
        'recursorRulesKernelDefinitionalEqual': 2,
        'completeStructureMetadataEqual': 2,
        'autoParamSlotsCompared': 36, 'nonNullAutoParamExpressions': 0,
        'genuineSourceProofInferredTypeBinderInfoInventoryAndPlacementEqual': True,
        'explanation': 'The legacy allExpressionBinderInfoEqual flag is computed only from signature traversals. '
                       'Complete computational values and recursor rules passed kernelTermEq. '
                       'Kernel conversion uses proof irrelevance and does not establish raw BinderInfo identity.'}
    evidence_paths = [dossier_path, pins_path, Path(dossier['actualReceipt']['path']), Path(dossier['audit']['path']),
        Path(dossier['auditSource']['path']), Path(dossier['auditConfig']['path']), Path(dossier['sourceModuleView']['path']),
        Path(dossier['comparisonCoverage']['path']), wrapper_path, blind_path, context_path, ledger_path,
        I/'paper-context-validation.json', I/'accepted-prior-identity-map.json', I/'dependency-closure.json', protocol,
        Path(generated['path']), Path(generated['payload']), Path(generated['blindReadback']['path']),
        Path(provenance['original_artifact']), out/'source-ledger.Orbicurve.json', out/'paper-context.Orbicurve.json',
        out/'readback.Orbicurve.json', out/'payload.json', out/'Definition.lean']
    evidence_paths.extend(Path(row['original_artifact']) for row in reviews.values())
    evidence = {str(path.resolve()): sha(path) for path in evidence_paths}
    evidence.update(pins['inputs'])
    packet = {'schema': PACKET_SCHEMA, 'workspace': str(W), 'mission_id': namespace['MISSION'],
        'root_id': namespace['ROOT'], 'environment': namespace['ENV'], 'scope': namespace['SCOPE'],
        'root_graph_membership': False, 'canonicalC22Connected': False, 'visibility': 'private',
        'module_scope': SCOPE, 'kernel_coverage': COVERAGE, 'source_sha256': {TARGET: sha(W/TARGET)},
        'metadata_sha256': evidence, 'actual_kernel_receipt': dossier['actualReceipt'],
        'actual_kernel_job_id': receipt['job_id'], 'binder_info_scope': annotation_scope,
        'parent_foundation_definitions': 'Existing published dependencies; no parent publication or alias is included.',
        'publications': [{'tag': NAME, 'endpoint': '/submit-definition', 'payload': payload}],
        'verification': [], 'publication_post_limit': 1}
    write(out/'packet.json', packet)
    gates = {gate: gate in ['wrapped_kernel_type_identity', 'independent_readbacks'] for gate in GATES}
    ready = {'schema': READY_SCHEMA, 'passed': False, 'packet_sha256': sha(out/'packet.json'),
        'source_sha256': packet['source_sha256'], 'kernel_coverage': COVERAGE, 'module_scope': SCOPE,
        'gates': gates, 'ci_receipts': {gate: ([dossier['actualReceipt']['path']] if gate ==
            'wrapped_kernel_type_identity' else []) for gate in CI_GATES},
        'axiom_audit': {'sorryAx_found': False, 'unexpected_axioms': [],
            'scope': 'Orbicurve70 audit only; production AxiomAudit gate remains pending'},
        'gate_evidence': {gate: ([str(blind_path), str(out/'readback.Orbicurve.json')] if gate ==
            'independent_readbacks' else [str(out/'source-ledger.Orbicurve.json')] if gate ==
            'source_ledger_consumers' else []) for gate in GATES if gate not in CI_GATES},
        'evidence_sha256': evidence,
        'pending': [gate for gate, passed in gates.items() if not passed],
        'note': 'Fresh Ready remains false. Root must bind production receipts, consumer review, mission scope, '
                'Git whitespace check, and final frozen review before any delivery.'}
    write(out/'ready.json', ready)
    schema = {'$schema': 'https://json-schema.org/draft/2020-12/schema', 'title': READY_SCHEMA,
        'type': 'object', 'required': list(ready), 'properties': {
            'schema': {'const': READY_SCHEMA}, 'passed': {'type': 'boolean'},
            'packet_sha256': {'type': 'string', 'pattern': '^[0-9a-f]{64}$'},
            'kernel_coverage': {'const': COVERAGE}, 'module_scope': {'const': SCOPE},
            'gates': {'type': 'object', 'required': GATES, 'additionalProperties': False,
                      'properties': {gate: {'type': 'boolean'} for gate in GATES}},
            'ci_receipts': {'type': 'object', 'required': CI_GATES, 'additionalProperties': False,
                'properties': {gate: {'type': 'array', 'items': {'type': 'string'}} for gate in CI_GATES}},
            'pending': {'type': 'array', 'items': {'enum': GATES}},
            'source_sha256': {'type': 'object'}, 'axiom_audit': {'type': 'object'},
            'gate_evidence': {'type': 'object'}, 'evidence_sha256': {'type': 'object'}, 'note': {'type': 'string'}},
        'allOf': [{'if': {'properties': {'passed': {'const': True}}}, 'then': {'properties': {
            'gates': {'properties': {gate: {'const': True} for gate in GATES}}, 'pending': {'maxItems': 0},
            'ci_receipts': {'properties': {gate: {'minItems': 1} for gate in CI_GATES}}}}}]}
    write(out/'ready.schema.json', schema)
    return check(out)

def check(out):
    out = Path(out).resolve()
    packet, ready = read(out/'packet.json'), read(out/'ready.json')
    need(packet['schema'] == PACKET_SCHEMA and ready['schema'] == READY_SCHEMA, 'Wrong packet/Ready schema')
    need(packet['module_scope'] == ready['module_scope'] == SCOPE and
         packet['kernel_coverage'] == ready['kernel_coverage'] == COVERAGE, 'Wrong module scope or coverage')
    need(ready['packet_sha256'] == sha(out/'packet.json'), 'Packet/Ready hash mismatch')
    need(ready['passed'] is False, 'This prepare-only checker does not authorize Ready promotion')
    need(packet['source_sha256'] == ready['source_sha256'] == {TARGET: sha(W/TARGET)}, 'Native source changed')
    for path, digest in {**packet['metadata_sha256'], **ready['evidence_sha256']}.items():
        need(sha(path) == digest, 'Prepared evidence changed: ' + path)
    need(len(packet['publications']) == packet['publication_post_limit'] == 1, 'Expected one Definition')
    row = packet['publications'][0]
    need(row['tag'] == NAME and row['endpoint'] == '/submit-definition' and
         row['payload'] == read(out/'payload.json') and row['payload']['private'] is True and
         row['payload']['definition'] == (W/TARGET).read_text(), 'Publication payload differs')
    need(set(ready['gates']) == set(GATES) and
         ready['pending'] == [gate for gate in GATES if not ready['gates'][gate]], 'Ready gates differ')
    return {'schema': 'orbicurve70-offline-packet-check-v1', 'passed': True,
        'publicationReady': False, 'definitions': 1, 'kernelCoverage': COVERAGE,
        'currentAuditInputPins': 38, 'allCurrentPinsMatch': True,
        'exactOriginalReadbackReused': True, 'packet': pin(out/'packet.json'),
        'ready': pin(out/'ready.json'), 'payload': pin(out/'payload.json'),
        'pendingGates': ready['pending'], 'apiCalls': 0, 'compilerCalls': 0, 'gitCalls': 0}

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('command', choices=['prepare', 'check'])
    parser.add_argument('--out', type=Path, default=Path(__file__).resolve().parent)
    args = parser.parse_args()
    result = prepare(args.out) if args.command == 'prepare' else check(args.out)
    write(args.out/'offline-validation.json', result)
    print(json.dumps(result, ensure_ascii=False, indent=2))
