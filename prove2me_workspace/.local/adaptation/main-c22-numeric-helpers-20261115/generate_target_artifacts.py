#!/usr/bin/env python3
"""Seven numeric platform drafts from accepted whole AST and actual source types.
No Lean, CI, API, Git, source oracle, or source-text command parser is invoked.
"""
import sys
sys.dont_write_bytecode = True
import argparse
import json
from pathlib import Path

ROOT = Path('/home/admin-wsl/Coq/abc')
ADAPT = ROOT/'prove2me_workspace/.local/adaptation'
PREVIOUS = ADAPT/'main-c22-numeric-reference-split-20261115'
sys.path.insert(0, str(PREVIOUS))
from generate_numeric import check, sha, hashed, load, lines, rng, walk, apply, accept_ci

DEFAULT_BASE = ADAPT/'main-c22-numeric-helpers-20261115'
DEFAULT_OUT = Path('/tmp/p2m-main-numeric-integration-v6-20261115')
ALLOWED_AXIOMS = {'propext','Classical.choice','Quot.sound'}
PREFIX = 'AbcAdaptation.Reference'

def write_json(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, ensure_ascii=False, indent=2)+'\n')

def name_text(value):
    if not value:
        return ''
    return (name_text(value[0])+'.' if value[0] else '')+str(value[2])

def expr_walk(value):
    if isinstance(value, dict):
        yield value
        for child in value.values():
            yield from expr_walk(child)
    elif isinstance(value, list):
        for child in value:
            yield from expr_walk(child)

def signature_spec(expr):
    result = []
    while expr['kind'] == 'forall':
        type_expr = expr['type']
        if type_expr['kind'] == 'const':
            category = name_text(type_expr['name'])
            check(category in ['Real','Nat'], 'Unexpected numeric binder type')
        else:
            check(type_expr['kind'] == 'app', 'Unexpected premise shape')
            category = 'Prop'  # The audit checks this on the original and both target types.
        result.append({'name':name_text(expr['name']),'binderInfo':expr['binder'],'typeCategory':category})
        expr = expr['body']
    return result

def replace_once(text, old, new):
    check(text.count(old) == 1, 'Audit template anchor changed: '+old[:80])
    return text.replace(old, new, 1)

SIGNATURE_FUNCTION = '''def signatureJson (type : Expr) (expected : Array (String × String)) : MetaM Json :=
  forallTelescope type fun xs result => do
    unless xs.size == expected.size do throwError "Source-derived signature binder count differs"
    let mut rows := #[]
    for index in [:xs.size] do
      let decl ← xs[index]!.fvarId!.getDecl
      let (expectedInfo, expectedCategory) := expected[index]!
      unless decl.binderInfo == (← checked (decodeBinder expectedInfo)) do
        throwError "Source-derived signature BinderInfo differs at {index}"
      match expectedCategory with
      | "Real" =>
        unless ← Meta.isDefEq decl.type (mkConst `Real) do
          throwError "Expected Real signature parameter {index}"
      | "Nat" =>
        unless ← Meta.isDefEq decl.type (mkConst `Nat) do
          throwError "Expected Nat signature parameter {index}"
      | "Prop" =>
        unless ← isProp decl.type do throwError "Expected proposition premise {index}"
      | _ => throwError "Unknown source-derived signature type category"
      rows := rows.push (Json.mkObj [("name", toJson decl.userName.toString),
        ("binderInfo", toJson (reprStr decl.binderInfo)),
        ("typeCategory", toJson expectedCategory),
        ("type", toJson (← ppExpr decl.type).pretty)])
    unless ← isProp result do throwError "Expected a proposition result"
    return Json.mkObj [("binders", Json.arr rows),
      ("signatureBinderInfo", toJson (expected.map (·.1))),
      ("result", toJson (← ppExpr result).pretty)]

'''

def render_audit(template, names, entry, spec):
    original = entry['originalName']; short = original.split('.')[-1]
    wrapped = PREFIX+'.'+original; slug = wrapped.replace('.','_')
    theorem_module = 'Theorems.Thm_'+slug; solution_module = 'Solutions.Sol_'+slug
    result = replace_once(template, 'import Theorems.Thm_AbcAdaptation_Reference_Iut_assembly', 'import '+theorem_module)
    result = replace_once(result, 'import Solutions.Sol_AbcAdaptation_Reference_Iut_assembly', 'import '+solution_module)
    a = result.index('def signatureJson ')
    b = result.index('def audit ', a)
    result = result[:a]+SIGNATURE_FUNCTION+result[b:]
    result = replace_once(result, 'def audit (original wrapped theoremModule solutionModule : Name) (realCount : Nat) : TermElabM Unit := do',
        'def audit (original wrapped theoremModule solutionModule : Name)\n    (signatureBinders : Array (String × String)) (expectedSourceModule expectedSourceSha : String) : TermElabM Unit := do')
    result = replace_once(result, 'unless records.size == 2 do throwError "Expected exactly two source records"',
        'unless records.size == 7 do throwError "Expected exactly seven source records"')
    expected_names = '#['+', '.join(json.dumps(n) for n in names)+']'
    result = replace_once(result, 'for name in #["Iut.assembly", "Iut.c2_final"] do', 'for name in '+expected_names+' do')
    result = replace_once(result,
        '  let expectedSourceModule := if original == `Iut.assembly then\n    "Iut.Implication.Theorem110" else "Iut.Implication.Corollary22"\n', '')
    result = replace_once(result, 'unless sourceSha.length == 64 do throwError "Missing source checksum"',
        'unless sourceSha == expectedSourceSha do throwError "Original source checksum differs"')
    for label in ['sourceType','targetType','solutionType']:
        result = replace_once(result, 'signatureJson '+label+' realCount', 'signatureJson '+label+' signatureBinders')
    # Keep full closed Kernel.check/Kernel.isDefEq and every old axiom/import gate.
    # Missing or changed standard constants are diagnosed rather than relocated.
    result = replace_once(result,
        '  for name in type.getUsedConstants do\n    let _ ← checked (requireStandardName name)\n',
        '  for name in type.getUsedConstants do\n    let _ ← checked (requireStandardName name)\n    unless env.contains name do\n      throwError "Standard constant unavailable in platform for {label}: {name}; no relocation permitted"\n')
    result = replace_once(result, 'throwError "Kernel type comparison failed: {label}"',
        'throwError "Kernel type comparison failed: {label}; original constants are not renamed. Left: {left}; right: {right}"')
    result = replace_once(result, '("allExpressionBinderInfoEqual", toJson true),',
        '("allExpressionBinderInfoEqual", toJson true),\n    ("signatureBinderInfoPreserved", toJson true),\n    ("standardConstantRelocations", Json.arr #[]),')
    pairs = '#['+', '.join('('+json.dumps(r['binderInfo'])+', '+json.dumps(r['typeCategory'])+')' for r in spec)+']'
    call = ('NumericTypeAudit.audit `'+original+' `'+wrapped+' `'+theorem_module+' `'+solution_module+' '+pairs+' '+json.dumps(entry['originalModule'])+' '+json.dumps(entry['effectiveSource']['sha256']))
    result = replace_once(result,
        'NumericTypeAudit.audit `Iut.assembly `AbcAdaptation.Reference.Iut.assembly `Theorems.Thm_AbcAdaptation_Reference_Iut_assembly `Solutions.Sol_AbcAdaptation_Reference_Iut_assembly 11', call)
    return result

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--base', type=Path, default=DEFAULT_BASE)
    ap.add_argument('--out', type=Path, default=DEFAULT_OUT)
    args = ap.parse_args(); base=args.base.resolve(); out=args.out.resolve()
    out.mkdir(parents=True, exist_ok=True)
    manifest_path=base/'manifest.json'; manifest=load(manifest_path)
    source_expr_path=base/'source-facts/original-exprs.json'; original=load(source_expr_path)
    source_result_path=base/'original-seven-facts-result.json'
    ci=accept_ci(source_result_path, 'ci-015163-070e492c')
    check(ci['resources']['peak_rss_bytes'] <= 16*1024**3, 'Original type export exceeds 16GiB')
    check(original['schema']=='numeric-source-original-expr-v1' and original['compilerVersion']=='4.35.0-rc3', 'Original actual Expr schema/compiler differs')
    entries=manifest['entries']; names=[e['originalName'] for e in entries]
    check(len(names)==len(set(names))==7, 'Expected seven selected original declarations')
    records={r['name']:r for r in original['records']}
    check(set(records)==set(names) and len(original['records'])==7, 'Actual source record set mismatch')
    config_path=Path(ci['request']['environment']['NUMERIC_SOURCE_FACTS_CONFIG']); config=load(config_path)
    check(Path(config['outputDir']) == source_expr_path.parent, 'Original output/config directory mismatch')
    check(len(config['sources'])==7 and {r['name'] for r in config['sources']}==set(names), 'Original source config set mismatch')
    keywords=lines(base/'source-facts/keywords.jsonl')
    template_path=PREVIOUS/'AuditAssembly.lean'; template=template_path.read_text()
    generation=[]; source_constants=[]; allfiles=[]
    for entry in entries:
        name=entry['originalName']; short=name.split('.')[-1]; full=PREFIX+'.'+name; slug=full.replace('.','_'); record=records[name]
        check(entry['typeDeps']==entry['valueDeps']==[], 'Selected type/value project dependencies changed')
        check(record['sourceSha256']==entry['effectiveSource']['sha256'] and record['module']==entry['originalModule'], 'Actual type not bound to original source')
        check(record['nameExpr']==entry['originalSourceNameExpr'] and set(record['axioms'])<=ALLOWED_AXIOMS, 'Actual name/axiom source mismatch')
        check(record['levelParams']==[], 'Unexpected universe parameters in numeric helper')
        spec=signature_spec(record['elaboratedExpr'])
        constants=sorted({name_text(v['name']) for v in expr_walk(record['elaboratedExpr']) if v.get('kind') in ['const','proj']})
        check(not any(n.startswith(('Iut.','Genl.','AbcAdaptation.','Definitions.','Theorems.','Solutions.')) for n in constants), 'Project constant in actual source type')
        metadata_path=base/'OriginalCommands'/(name.replace('.','_')+'.json')
        check(sha(metadata_path)==entry['metadata']['sha256'], 'Whole AST metadata changed')
        metadata=load(metadata_path); node=metadata['selectedNode']; ast=metadata['wholeCommandAST']
        check(node['name']==name and ast['range']==entry['effectiveSource']['range']==node['commandRange'], 'Whole AST/name mapping mismatch')
        data=Path(node['coordinateSource']).read_bytes()
        check(hashed(data)==record['sourceSha256'], 'Original normalized source changed')
        a,b=rng(node['commandRange']); command=data[a:b]
        check(hashed(command)==node['wholeCommandSha256']==entry['identities']['wholeCommandSha256'], 'Original whole command changed')
        binding,=node['bindingRanges']; n0,n1=rng(binding)
        proof_range,=node['proofRanges']; p,q=rng(proof_range)
        check(q==b and data[n0:n1].decode()==short, 'Binding/proof whole AST mismatch')
        proof=data[p:q]; signature=data[n1:p]
        check(hashed(proof)==entry['identities']['proofIncludingAssignmentSha256'] and hashed(signature)==entry['identities']['signatureAfterBindingSha256'], 'Original proof/signature changed')
        keyword,=[r for r in keywords if r['kind']=='keyword' and r['name']==name]
        x,y=rng(keyword['keywordRange'])
        atoms=[s for s in walk(ast['commandSyntax']) if s.get('atom') in ['lemma','theorem'] and s.get('range') and rng(s['range'])==(x,y)]
        check(len(atoms)==1 and a<=x<y<=n0<n1<p and data[x:y].decode()==keyword['keyword'], 'Source keyword/whole AST mismatch')
        docs=[s for s in walk(ast['commandSyntax']) if s['syntaxKind']=='Lean.Parser.Command.docComment']
        check(len(docs)<=1, 'Unexpected documentation AST')
        wrapped_path=base/'Drafts'/('Numeric_Iut_'+short+'.lean'); wrapped=wrapped_path.read_bytes()
        check(hashed(wrapped)==entry['files']['wrapped']['sha256'], 'Integrated wrapper changed')
        mapped,=[m for m in entry['files']['wrapped']['commandMappings'] if m['originalCommandIndex']==entry['parserCommandIndex']]
        wa,wb=rng(mapped['generatedRange']); check(wrapped[wa:wb]==command, 'Integrated command differs from original')
        preamble=apply(wrapped,[(wa,wb,b'')])
        def renamed_command(new_name, stub):
            edits=[(x-a,y-a,b'theorem'),(n0-a,n1-a,new_name.encode())]
            if docs:
                da,db=rng(docs[0]['range']); edits.append((da-a,db-a,b''))
            if stub: edits.append((p-a,b-a,b':= by\n  sorry'))
            return apply(command,edits)
        formal=renamed_command(full,True); solution_command=renamed_command('solution',False)
        theorem_bytes=preamble+formal+b'\n'; solution_bytes=preamble+solution_command+b'\n'
        check(solution_bytes.endswith(proof+b'\n'), 'Solution proof bytes changed')
        removed_doc_bytes = sum(rng(d['range'])[1]-rng(d['range'])[0] for d in docs)
        def signature_offsets(new_name):
            start = n1-a + len(b'theorem')-(y-x) + len(new_name.encode())-(n1-n0) - removed_doc_bytes
            return start, start+(p-n1)
        ss,se=signature_offsets('solution'); ts,te=signature_offsets(full)
        check(solution_command[ss:se]==signature and formal[ts:te]==signature, 'Generated theorem/solution signature bytes differ')
        check(solution_command[se:]==proof, 'Generated solution proof range differs')
        # Only parser binding, keyword, documentation, and intentional theorem-stub edits.
        theorem_module='Theorems.Thm_'+slug; solution_module='Solutions.Sol_'+slug
        payload={'theorem_name':full,'preamble':preamble.decode(),'formal_statement':formal.decode(),'solution':solution_bytes.decode()}
        files={}
        for label,path,contents in [('theorem',out/(theorem_module.replace('.','/')+'.lean'),theorem_bytes),('solution',out/(solution_module.replace('.','/')+'.lean'),solution_bytes),('payload',out/'payloads'/(slug+'.json'),(json.dumps(payload,ensure_ascii=False,indent=2)+'\n').encode())]:
            path.parent.mkdir(parents=True,exist_ok=True);path.write_bytes(contents)
            files[label]={'path':str(path),'sha256':sha(path),'bytes':len(contents)}; allfiles.append(files[label])
        audit_path=out/'Audits'/('Audit_'+slug+'.lean');audit_path.parent.mkdir(exist_ok=True)
        audit_path.write_text(render_audit(template,names,entry,spec))
        files['audit']={'path':str(audit_path),'sha256':sha(audit_path),'bytes':audit_path.stat().st_size};allfiles.append(files['audit'])
        generation.append({'originalName':name,'theoremName':full,'theoremModule':theorem_module,'solutionModule':solution_module,'signatureSpecificationFromActualSourceExpr':spec,'originalCommandSha256':hashed(command),'originalProofSha256':hashed(proof),'originalSignatureSha256':hashed(signature),'finalSolutionProofBytesIdentical':True,'finalSignatureBytesIdenticalAfterBinding':True,'generatedSignatureByteOffsets':{'theorem':[len(preamble)+ts,len(preamble)+te],'solution':[len(preamble)+ss,len(preamble)+se]},'generatedSolutionProofByteOffsets':[len(preamble)+se,len(preamble)+len(solution_command)],'sourceCompilerExprInputSha256':sha(source_expr_path),'actualSourceRecord':record,'originalKeywordRange':keyword['keywordRange'],'sourceCommandRange':node['commandRange'],'sourceBindingRange':binding,'sourceProofRange':proof_range,'targetAuditEnvironment':{'NUMERIC_ORIGINAL_EXPR_FILE':str(source_expr_path),'NUMERIC_AUDIT_OUTPUT_DIR':str(out/'PendingAuditOutputs')},'files':files,'actualOriginalConsumers':entry['actualOriginalConsumers'],'canonicalConsumerConnected':False,'targetCompilation':'pending','kernelOriginalTargetSolutionIdentity':'pending','targetAxiomAudit':'pending','granularity':'candidate; root decides whether log_pi_nonneg remains inline in an existing consumer'})
        source_constants.append({'name':name,'actualSourceTypeConstants':constants,'standardConstantRelocations':[],'targetAvailabilityAndMeaning':'pending target kernel audit; missing/changed standard constants cause failure; no substitution'})
    (out/'LICENSE').write_bytes((base/'LICENSE').read_bytes())
    report={'schema':'numeric-helpers-target-artifact-draft-v1','status':'generated-from-actual-source-types-target-CI-pending','noCompilation':True,'noCI':True,'noAPI':True,'noGit':True,'sourceRootOnlyOracleRequested':False,'sourceRootOnlyOracleReason':'No project type/value references; use original actual type + original proof bytes + full closed target kernel equality and axiom checks','sourceFactsJobId':ci['job_id'],'sourceFactsResources':ci['resources'],'sourceFactsInput':{'path':str(source_expr_path),'sha256':sha(source_expr_path)},'inputs':[{'path':str(p),'sha256':sha(p)} for p in [manifest_path,source_result_path,source_expr_path,config_path,base/'source-facts/keywords.jsonl',template_path,PREVIOUS/'generate_numeric.py']],'nodes':generation,'generatedFiles':allfiles,'standardConstantPolicy':'Identity only; no source/target standard constant relocation','kernelAndAxiomAudits':'drafts generated, not run','canonicalConsumers':'original typed edges only; target integration pending'}
    write_json(out/'generation-manifest.json',report)
    write_json(out/'source-type-constant-inventory.json',{'status':'actual-source-constants-listed-target-kernel-pending','nodes':source_constants})
    write_json(out/'SOURCE_LEDGER.json',{'status':report['status'],'sourceRepository':manifest['sourceRepository'],'sourceCommit':manifest['sourceCommit'],'entries':[{'producer':n['theoremName'],'source':e['originalSource'],'actualOriginalConsumers':n['actualOriginalConsumers'],'canonicalConsumerConnected':False,'proofSha256':n['originalProofSha256'],'scope':'Pure real inequality or finite-sum polynomial identity','fidelity':'Original signature/proof bytes preserved; original actual compiler type bound; target kernel/axiom validation pending'} for n,e in zip(generation,entries)]})
    print(json.dumps({'status':report['status'],'out':str(out),'nodes':len(generation),'generatedLeanFiles':21,'sourceFactsJob':ci['job_id'],'newSourceOracle':False},ensure_ascii=False))

if __name__=='__main__':
    main()
