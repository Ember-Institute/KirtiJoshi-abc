#!/usr/bin/env python3
"""Assemble drafts from accepted AST ranges; no parser, Lean, CI, API, or Git calls."""
import sys
sys.dont_write_bytecode = True
import json
from pathlib import Path

ROOT = Path('/home/admin-wsl/Coq/abc')
OUT = Path('/tmp/p2m-main-numeric-helpers-v6-20261115')
BASE = ROOT / 'prove2me_workspace/.local/adaptation'
PREVIOUS = BASE / 'main-c22-numeric-reference-split-20261115'
sys.path.insert(0, str(PREVIOUS))
# Reuse the accepted earlier range/byte helpers. This is not a new extractor.
from generate_numeric import check, sha, hashed, load, lines, rng, walk

PARSER = BASE / 'reference-main-chain-parser-20261115'
PLAN = PARSER / 'c2-source-input-plan/main-proof-tree.json'
GRAPH = BASE / 'reference-extraction-20261115/c22-decl-graph.jsonl'
BUILD_PLAN = BASE / 'reference-extraction-20261115/source-build-plan.json'
PREFIX = 'AbcAdaptation.Reference'
REPO = 'https://github.com/lana-agents/iut'
COMMIT = '07cb1da58f6d428a670dbb5dd6093d428bcbcdd8'
SOURCE_MATHLIB = Path('/home/admin-wsl/Coq/mathlib4')
TARGET_MATHLIB = Path('/home/admin-wsl/Coq/mathlib4-0df444a')

IMPORTS = {
 'log_bound_ell': ['Mathlib.Analysis.SpecialFunctions.Log.Basic', 'Mathlib.Tactic.Linarith', 'Mathlib.Tactic.NormNum', 'Mathlib.Tactic.Positivity', 'Mathlib.Tactic.Ring'],
 'log_le_four_mul_sqrt_sqrt': ['Mathlib.Analysis.SpecialFunctions.Log.Basic', 'Mathlib.Analysis.Real.Sqrt', 'Mathlib.Algebra.Order.GroupWithZero.Basic', 'Mathlib.Tactic.Linarith', 'Mathlib.Tactic.NormNum', 'Mathlib.Tactic.Push', 'Mathlib.Tactic.Ring'],
 'log_le_half_of_pos': ['Mathlib.Analysis.SpecialFunctions.Log.Basic', 'Mathlib.Analysis.Real.Sqrt', 'Mathlib.Tactic.Linarith', 'Mathlib.Tactic.Ring'],
 'log_le_self_of_pos': ['Mathlib.Analysis.SpecialFunctions.Log.Basic', 'Mathlib.Tactic.Linarith'],
 'log_pi_le_two': ['Mathlib.Analysis.SpecialFunctions.Log.Basic', 'Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic', 'Mathlib.Analysis.Complex.ExponentialBounds', 'Mathlib.Tactic.Linarith', 'Mathlib.Tactic.NormNum', 'Mathlib.Tactic.Ring'],
 'log_pi_nonneg': ['Mathlib.Analysis.SpecialFunctions.Log.Basic', 'Mathlib.Analysis.Real.Pi.Bounds', 'Mathlib.Tactic.Linarith'],
 'sum_affine_quadratic': ['Mathlib.Data.Real.Basic', 'Mathlib.Data.Fintype.BigOperators', 'Mathlib.Tactic.Ring'],
}

def write_json(path, data):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(data, ensure_ascii=False, indent=2) + '\n')

def position(data, offset):
    before = data[:offset]
    return {'line': before.count(b'\n')+1, 'col': len(before.rsplit(b'\n', 1)[-1].decode()), 'offset': offset}

def extent(data, a, b):
    return {'start': position(data, a), 'end': position(data, b)}

def assemble(license_bytes, imports, contexts, selected, data, wrapped):
    notice = (b'/- Adaptation draft: exact original declaration retained; imports and surrounding\n'
              b'context reduced to numerical inputs. Compiler semantic identity is pending. -/\n')
    result = license_bytes + notice + ''.join('import '+m+'\n' for m in imports).encode() + b'\n'
    if wrapped:
        result += ('namespace '+PREFIX+'\n\n').encode()
    mappings = []
    for command in sorted(contexts + [selected], key=lambda c: c['commandIndex']):
        a, b = rng(command['range'])
        start = len(result)
        result += data[a:b]
        mappings.append({'originalCommandIndex': command['commandIndex'], 'originalRange': command['range'], 'generatedRange': extent(result, start, len(result)), 'sha256': hashed(data[a:b]), 'bytesIdentical': True})
        result += b'\n\n'
    if wrapped:
        result += ('end '+PREFIX+'\n').encode()
    return result, mappings

def main():
    check(OUT.resolve() == OUT and OUT.is_dir(), 'Unique task output directory required')
    acceptance = load(PARSER / 'parser-acceptance.json')
    review = load(PARSER / 'source-review/acceptance-review.json')
    check(acceptance['status'] == 'accepted' and review['status'] == 'accepted-for-parser-positions-only', 'Parser/source review missing')
    check(sha(PARSER / 'parser-ranges-result.json') == acceptance['receipt_sha256'] == review['resultSha256'], 'Parser receipt identity changed')
    check(review['noPanicOrErrorDiagnostics'] and review['exitCode'] == 0, 'Parser receipt not clean')
    check(review['workspaceMode'] == 'exclusive_worktree' and review['snapshotId'] is None, 'Parser workspace receipt changed')
    rows = {r['name']: r for r in lines(GRAPH) if r.get('record') == 'decl'}
    plan = load(PLAN)
    nodes = {r['name']: r for r in plan['sourceStandaloneMainCommands']}
    check(len(nodes) == 19, 'Expected actual 19 whole AST commands')
    builds = {r['module']: r for r in load(BUILD_PLAN)['input_modules']}
    parser_outputs = {r['module']: r for r in acceptance['outputs']}
    evidence_paths = [PLAN, GRAPH, BUILD_PLAN, PARSER/'parser-acceptance.json', PARSER/'parser-ranges-result.json', PARSER/'source-review/acceptance-review.json', PREVIOUS/'generate_numeric.py', PREVIOUS/'generate_root_only.py', PREVIOUS/'generate_from_small_oracles.py', PREVIOUS/'ExtractSmallNumericOracle.lean', PREVIOUS/'QueryNumericSourceFacts.lean', ROOT/'prove2me_workspace/lean-toolchain', ROOT/'prove2me_workspace/lake-manifest.json']
    evidence_paths += [Path(r['path']) for r in acceptance['outputs']]
    import_evidence = []
    for module in sorted({m for values in IMPORTS.values() for m in values}):
        entry = {'module': module, 'selectionBasis': 'Named declarations in compiler externalDependencies plus original tactic syntax; no umbrella Mathlib import', 'compilerVerifiedSufficiency': 'pending'}
        for label, directory in [('source', SOURCE_MATHLIB), ('target', TARGET_MATHLIB)]:
            p = directory / (module.replace('.', '/')+'.lean')
            check(p.is_file(), 'Missing precise '+label+' import '+module)
            entry[label] = {'path': str(p), 'sha256': sha(p)}
        import_evidence.append(entry)
    entries = []
    facts_sources = []
    oracle_configs = []
    for short, imports in IMPORTS.items():
        name = 'Iut.'+short
        node, graph = nodes[name], rows[name]
        check(node['typeDeps'] == node['valueDeps'] == graph['typeDeps'] == graph['valueDeps'] == [], 'Project dependency appeared')
        check(graph['hasSorryAx'] is False and not graph['isPrivate'] and set(graph['axioms']) <= {'propext','Classical.choice','Quot.sound'}, 'Original graph axiom/privacy change')
        check(bool(node['actualConsumers']), 'Producer has no actual original consumer')
        for consumer in node['actualConsumers']:
            check(consumer['edge'] == 'value' and name in rows[consumer['consumer']]['valueDeps'], 'Original typed consumer edge not supported by compiler graph')
        module = node['module']
        output = parser_outputs[module]
        check(sha(output['path']) == output['sha256'], 'Parser output changed')
        facts = lines(output['path'])
        source, = [r for r in facts if r['kind'] == 'source']
        check(source['acceptedGraphSha256'] == sha(GRAPH), 'Parser accepted graph changed')
        check(facts[-1]['kind'] == 'summary' and facts[-1]['status'] == 'success', 'Missing parser summary')
        data = Path(node['coordinateSource']).read_bytes()
        check(hashed(data) == node['normalizedSha256'] == source['normalizedSha256Expected'], 'Source byte identity changed')
        check(data == Path(node['source']).read_bytes().replace(b'\r\n',b'\n'), 'Normalized source mismatch')
        commands = {r['commandIndex']:r for r in facts if r['kind']=='command'}
        index, = node['owningCommandIndices']
        command = commands[index]
        check(command['generationIssue'] is None and command['isDeclaration'], 'Unsupported atomic declaration')
        check(command['range'] == node['commandRange'], 'Whole command AST range differs')
        a, b = rng(command['range'])
        raw_command = data[a:b]
        check(hashed(raw_command) == node['wholeCommandSha256'] and raw_command.decode() == node['commandText'], 'Whole command byte mismatch')
        proof_range, = node['proofRanges']
        p, q = rng(proof_range)
        binding, = node['bindingRanges']
        n0, n1 = rng(binding)
        check(a <= n0 < n1 < p < q == b and data[n0:n1].decode() == short, 'Binding/proof AST bounds invalid')
        proof = data[p:q]
        signature = data[n1:p]
        type_start = min(s['range']['start']['offset'] for s in node['signatureSyntax'] if s['range'])
        explicit_signature = data[type_start:p]
        check(type_start >= n1, 'Signature start outside declaration')
        build = builds[module]
        original = Path(build['source']).read_bytes()
        check(hashed(original) == build['original_sha256'] and hashed(data) == build['sha256'], 'Repository build plan source changed')
        mirror = build['configuration_mirror']; insertion = mirror['text'].encode(); at = mirror['insertion_original_offset']
        check(data[at:at+len(insertion)] == insertion and at+len(insertion) <= a, 'Semantic option inverse mapping invalid')
        oa, ob = a-len(insertion), b-len(insertion)
        inverse = data[:at]+data[at+len(insertion):]
        check(inverse[:ob] == original[:ob] and original[oa:ob] == raw_command, 'Repository prefix/command not byte-identical')
        original_range = extent(original, oa, ob)
        url = REPO+'/blob/'+COMMIT+'/'+graph['sourceFile']+'#L'+str(original_range['start']['line'])+'-L'+str(original_range['end']['line'])
        # Retain original numerical contexts. Only the Theorem110 open NumberField
        # and AG/TG variable commands are omitted; graph type/value deps are empty.
        # The resulting compiler Expr equality remains explicitly pending.
        retained = [0,1,3,4,28] if module.endswith('Corollary22') else [0,1,3,4,21]
        if module.endswith('Corollary22'):
            retained.insert(4,5)  # exact original `open Finset Real`
        contexts = [commands[i] for i in retained]
        import_nodes = [s for s in walk(source['headerSyntax']) if s['syntaxKind']=='Lean.Parser.Module.import']
        first_import = min(s['range']['start']['offset'] for s in import_nodes)
        license_bytes = data[:first_import]
        check(b'Copyright (c) 2026 The iut contributors.' in license_bytes and b'Apache 2.0' in license_bytes, 'Missing original copyright/license')
        files = {}
        for label, wrapped in [('rootOnly', False), ('wrapped',True)]:
            generated, mappings = assemble(license_bytes, imports, contexts, command, data, wrapped)
            directory = 'RootOnly' if not wrapped else 'Drafts'
            path = OUT / directory / ('Numeric_Iut_'+short+'.lean')
            path.parent.mkdir(exist_ok=True)
            path.write_bytes(generated)
            selected_mapping, = [r for r in mappings if r['originalCommandIndex']==index]
            ga, gb = rng(selected_mapping['generatedRange'])
            check(generated[ga:gb] == raw_command and generated[ga+p-a:ga+q-a] == proof and generated[ga+n1-a:ga+p-a] == signature, 'Generated command/proof/signature bytes changed')
            files[label] = {'path':str(path), 'sha256':sha(path), 'bytes':len(generated), 'commandMappings':mappings, 'targetCommandBytesIdentical':True, 'proofBytesIdentical':True, 'signatureAfterBindingBytesIdentical':True, 'proofRange':extent(generated,ga+p-a,ga+q-a), 'signatureRange':extent(generated,ga+n1-a,ga+p-a), 'bindingRange':extent(generated,ga+n0-a,ga+n1-a)}
        source_map_path = OUT / 'OriginalCommands' / (name.replace('.','_')+'.json')
        write_json(source_map_path, {'selectedNode':node,'wholeCommandAST':command,'retainedContextAST':contexts, 'omittedActiveContextAST':[commands[i] for i in [5,6]] if module.endswith('Theorem110') else [], 'typedCompilerGraphDeclaration':graph})
        body_path = OUT/'OriginalCommands'/(name.replace('.','_')+'.command.lean')
        body_path.write_bytes(raw_command)
        signature_path = OUT/'OriginalCommands'/(name.replace('.','_')+'.signature.lean.txt')
        signature_path.write_bytes(explicit_signature)
        source_facts = {'source':node['source'], 'normalizedSha256':node['normalizedSha256'], 'module':module,'name':name}
        facts_sources.append(source_facts)
        oracle_config = {'files':[{'module':module, 'source':files['rootOnly']['path'], 'file':graph['sourceFile'], 'sourceSha256':files['rootOnly']['sha256'], 'normalizedSha256':files['rootOnly']['sha256']}], 'outputDir':str(OUT/'PendingOracleOutputs'/short), 'namePrefixes':[], 'options':[{'name':'relaxedAutoImplicit','type':'bool','value':False},{'name':'maxSynthPendingDepth','type':'nat','value':3}], 'failFast':True}
        config_path = OUT/'PendingCIConfigs'/('small-source-'+short+'.json')
        write_json(config_path, oracle_config)
        oracle_configs.append({'name':name,'config':str(config_path),'extractor':str(PREVIOUS/'ExtractSmallNumericOracle.lean'), 'environmentVariable':'REFERENCE_STAGE2_CONFIG','status':'not-submitted'})
        entries.append({'originalName':name, 'wrappedName':PREFIX+'.'+name,'originalModule':module,'typeDeps':[],'valueDeps':[],'actualOriginalConsumers':node['actualConsumers'],'canonicalConsumerConnected':False,'imports':imports, 'originalAxioms':graph['axioms'],'originalHasSorryAx':False,'originalSourceNameExpr':node['actualSourceNameExpr'], 'parserCommandIndex':index, 'originalSource':{'path':str(build['source']), 'sha256':hashed(original),'range':original_range,'url':url}, 'effectiveSource':{'path':node['source'],'coordinateSource':node['coordinateSource'],'sha256':hashed(data),'range':command['range'],'bindingRange':binding,'proofRange':proof_range}, 'repositoryInverseMapping':{'configurationInsertionOffset':at,'configurationInsertionBytes':len(insertion),'configurationInsertionSha256':hashed(insertion),'inversePrefixThroughTargetByteIdentical':True,'inverseWholeFileByteIdentical':inverse==original,'laterCompatibilityFix':build.get('compatibility_fix')}, 'identities':{'wholeCommandSha256':hashed(raw_command),'proofIncludingAssignmentSha256':hashed(proof),'signatureAfterBindingSha256':hashed(signature),'explicitSignatureSha256':hashed(explicit_signature)}, 'metadata':{'path':str(source_map_path),'sha256':sha(source_map_path)},'originalCommandCopy':str(body_path),'explicitSignatureCopy':str(signature_path),'files':files,'retainedContextCommandIndices':retained,'omittedActiveContextCommandIndices':[5,6] if module.endswith('Theorem110') else [],'pending':['original actual compiler Expr export','small-source re-elaboration/InfoTree acceptance','original/small/wrapped compiler type equality','target exact-text compilation','wrapped axiom/sorryAx audit','canonical consumer integration']})
    write_json(OUT/'PendingCIConfigs/original-source-facts.json',{'outputDir':str(OUT/'PendingOriginalExprOutputs'),'sources':facts_sources})
    (OUT/'LICENSE').write_bytes((ROOT/'refer/iut/LICENSE').read_bytes())
    manifest = {'schema':'main-numeric-helpers-v6-draft-v1','status':'source-bound-static-drafts-CI-pending','compilation':'not-run','mcpCI':'not-called','API':'not-called','git':'not-called','mainWorkspaceWrites':False,'sourceRepository':REPO,'sourceCommit':COMMIT,'sourceCompiler':'4.35.0-rc3','sourceMathlibRev':load(BUILD_PLAN)['mathlib_rev'],'targetCompiler':(ROOT/'prove2me_workspace/lean-toolchain').read_text().strip(),'targetMathlib':'0df444a','parserJobId':acceptance['job_id'],'sourceReviewScope':review['limit'],'existingAssemblyC2FinalIncluded':False,'reusedRangeHelpers':str(PREVIOUS/'generate_numeric.py'),'newExtractor':False,'inputs':[{'path':str(p),'sha256':sha(p)} for p in evidence_paths], 'preciseImportSourceEvidence':import_evidence,'entries':entries,'pendingSmallSourceConfigs':oracle_configs,'pendingOriginalFacts':{'config':str(OUT/'PendingCIConfigs/original-source-facts.json'),'environmentVariable':'NUMERIC_SOURCE_FACTS_CONFIG','extractor':str(PREVIOUS/'QueryNumericSourceFacts.lean'),'status':'not-submitted'},'license':{'path':str(OUT/'LICENSE'),'sha256':sha(OUT/'LICENSE'),'noticeCopiedByteExactly':True}}
    write_json(OUT/'manifest.json',manifest)
    write_json(OUT/'SOURCE_LEDGER.json',{'status':manifest['status'],'entries':[{'producer':e['wrappedName'],'originalSource':e['originalSource'],'actualOriginalConsumers':e['actualOriginalConsumers'],'canonicalConsumerConnected':False,'scope':'Pure real inequalities or finite-sum polynomial identity; no pending theta interfaces','fidelity':'Whole original command, explicit signature, and proof bytes preserved; namespace wrapper added outside the whole command; semantic compiler identity pending','identities':e['identities']} for e in entries]})
    write_json(OUT/'static-identity-report.json',{'status':'passed-static-byte-checks-only','entries':[{'name':e['originalName'],'identities':e['identities'],'originalRepositoryEffectiveCommandEqual':True,'rootOnlyCommandProofSignatureEqual':True,'wrappedCommandProofSignatureEqual':True,'compilerIdentity':'pending'} for e in entries]})
    print(json.dumps({'status':manifest['status'],'out':str(OUT),'theorems':len(entries),'leanDrafts':2*len(entries),'originalExpr':'pending'},ensure_ascii=False))

if __name__ == '__main__':
    main()
