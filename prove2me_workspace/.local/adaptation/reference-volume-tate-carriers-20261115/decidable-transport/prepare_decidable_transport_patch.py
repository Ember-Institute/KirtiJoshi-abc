#!/usr/bin/env python3
"""Write a receipt-bound closed core transport and exact two proof resolutions."""
from pathlib import Path
import argparse
import hashlib
import json

HERE=Path(__file__).resolve().parent
B=Path('/home/admin-wsl/Coq/abc/prove2me_workspace/.local/adaptation/reference-volume-tate-carriers-20261115')
PROOFS=['TateCurvesTheta.OrderedTateParameter.decidable._proof_1','TateCurvesTheta.PrimeToOrder.decidable._proof_1']


def sha(path):return hashlib.sha256(Path(path).read_bytes()).hexdigest()
def load(path):return json.loads(Path(path).read_text())
def dump(path,data):Path(path).write_text(json.dumps(data,ensure_ascii=False,indent=2)+'\n')

def replace_once(text,before,after):
    assert text.count(before)==1,(before,text.count(before))
    return text.replace(before,after,1)

def receipt(path,job=None):
    value=load(path)
    assert value['status']=='succeeded' and value['result']['exit_code']==0
    assert value['result']['snapshot']['workspace_mode']=='exclusive_worktree'
    assert value['result']['snapshot']['snapshot_id'] is None
    assert value['resources']['peak_rss_bytes']<=16*1024**3
    if job:assert value['job_id']==job
    return value

def binding(path):return {'path':str(Path(path).resolve()),'sha256':sha(path),'contents':load(path)}

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--audit-source',type=Path,default=B/'AuditNextCarriers.lean')
    ap.add_argument('--base-config',type=Path,default=B/'audit-config.json')
    ap.add_argument('--unit-dir',type=Path,default=B)
    ap.add_argument('--support-closure',type=Path)
    ap.add_argument('--support-receipt',type=Path)
    ap.add_argument('--output',type=Path,default=HERE/'AuditNextCarriers.Decidable435Transport.lean')
    ap.add_argument('--config-output',type=Path,default=HERE/'audit-config.decidable435-transport.json')
    args=ap.parse_args()
    assert args.output.resolve().parent==HERE and args.config_output.resolve().parent==HERE
    source=args.audit_source.read_text()
    result=replace_once(source,'  targetPrefix : Name\n','  targetPrefix : Name\n  standardExpansions : Array (Name × (List Name × Expr))\n')
    result=replace_once(result,'    let target ← relocated rs original\n','''    if let some expansion := rs.standardExpansions.find? (·.1 == original) then
      let levels ← (← arrayField j "levels").mapM decodeLevel
      unless levels.size == expansion.2.1.length do
        throw "Universe arity differs in genuine source value expansion"
      return expansion.2.2.instantiateLevelParams expansion.2.1 levels.toList
    let target ← relocated rs original
''')
    result=replace_once(result,'  return ⟨result, projectPrefixes, sourcePrefixes, targetPrefix⟩\n','  return ⟨result, projectPrefixes, sourcePrefixes, targetPrefix, #[]⟩\n')
    fragment=(HERE/'DecidableMissingSupport.lean.fragment').read_text()+'\n'+(HERE/'Decidable435Transport.lean.fragment').read_text()
    result=replace_once(result,'def compareRecord (rs : Relocations)',fragment+'\n\ndef compareRecord (rs : Relocations)')
    result=replace_once(result,'''      propositionalValueEquality ← proveGeneratedEliminatorEquality rs allowedOwners
        original sourceType sourceValue targetValue
''','''      if exactDecidableTransportInstances.contains original then
        propositionalValueEquality ← proveExactDecidableTransportEquality rs allowedOwners
          original sourceType sourceValue targetValue
      else
        propositionalValueEquality ← proveGeneratedEliminatorEquality rs allowedOwners
          original sourceType sourceValue targetValue
''')
    result=replace_once(result,'  let rs ← readRelocations config\n','  let (rs, standardTransportEvidence) ← installDecidable435Transport (← readRelocations config) config\n')
    result=replace_once(result,'  let directImports :=', '''  let (rs, proofResolutionReports) ← installExactDecidableSourceProofs rs allowedOwners source config
  let directImports :=''')
    result=replace_once(result,'  let mut requiredCount := 0\n','  let mut requiredCount := 0\n  let mut requiredNamedCount := 0\n  let mut resolvedProofNames : Array Name := #[]\n')
    result=replace_once(result,'    let targetName ← checked (relocated rs original)\n','''    if exactDecidableSourceProofNames.contains original then
      unless selected && proofResolutionReports.any (fun row => (stringField row "original").toOption == some original.toString) do
        throwError "Unvalidated mandatory genuine source proof {original}"
      requiredCount := requiredCount + 1
      resolvedProofNames := resolvedProofNames.push original
      continue
    let targetName ← checked (relocated rs original)
''')
    result=replace_once(result,'    comparisons := comparisons.push (← compareRecord rs allowedOwners record (← getConstInfo targetName))\n','''    comparisons := comparisons.push (← compareRecord rs allowedOwners record (← getConstInfo targetName))
    if selected then requiredNamedCount := requiredNamedCount + 1
''')
    result=replace_once(result,'  let mut targetOnly := #[]\n','''  unless resolvedProofNames.size == exactDecidableSourceProofNames.size &&
      requiredNamedCount == (← checked (config.getObjValAs? Nat "expectedNamedSelectedCount")) &&
      proofResolutionReports.size == (← checked (config.getObjValAs? Nat "expectedProofValueResolutionCount")) do
    throwError "Named/proof-resolution dimensions differ from actual configured inventory"
  for resolution in proofResolutionReports do
    let parent ← checked (stringField resolution "parentOriginal")
    let parents := comparisons.filter fun row => (stringField row "original").toOption == some parent
    unless parents.size == 1 do throwError "Missing mandatory whole-value parent comparison {parent}"
    let parentReport := parents[0]!
    unless (← checked (parentReport.getObjValAs? Bool "computationalValueEqualityChecked")) &&
        ((← checked (parentReport.getObjValAs? Bool "kernelValueEqual")) ||
         (← checked (parentReport.getObjValAs? Bool "kernelPropositionalValueEquality"))) do
      throwError "Genuine proof resolution parent has no kernel whole-value equality {parent}"
  let mut targetOnly := #[]
''')
    result=replace_once(result,'  let output ← checked (stringField config "outputDir")\n','''  let expectedTargetOnly ← checked (arrayField config "expectedTargetOnlyCompilerDeclarations")
  unless targetOnly.size == expectedTargetOnly.size && targetOnly.all expectedTargetOnly.contains do
    throwError "Actual target-only compiler declarations differ from genuine platform facts"
  let output ← checked (stringField config "outputDir")
''')
    result=replace_once(result,'    ("configuration", config), ("requiredComparedCount", toJson requiredCount),','''    ("configuration", config), ("standardRepresentationTransport", standardTransportEvidence),
    ("requiredComparedCount", toJson requiredCount),
    ("requiredNamedComparedCount", toJson requiredNamedCount),
    ("requiredProofValueResolutionCount", toJson proofResolutionReports.size),
    ("proofValueResolutions", Json.arr proofResolutionReports),''')
    args.output.write_text(result)
    summary={'source':str(args.audit_source),'sourceSha256':sha(args.audit_source),'candidate':str(args.output),'sha256':sha(args.output),'status':'draft-not-compiled'}
    if args.support_closure is not None:
        assert args.support_receipt is not None,'--support-receipt is required with --support-closure'
        source_receipt=args.unit_dir/'decidable-standard-original-result.json'
        platform_receipt=args.unit_dir/'decidable-platform-result.json'
        # Root may archive files under another exact name; resolve by accepted job id.
        if not platform_receipt.exists():
            found=[p for p in args.unit_dir.glob('*result.json') if load(p).get('job_id')=='ci-013907-b9f0843a']
            assert len(found)==1;platform_receipt=found[0]
        receipt(source_receipt,'ci-013901-2c932c62');receipt(platform_receipt,'ci-013907-b9f0843a');receipt(args.support_receipt,'ci-013924-3a1c20d9')
        source_facts=args.unit_dir/'decidable-standard-source-facts.json'
        platform_facts=args.unit_dir/'decidable-platform-facts.json'
        std=load(source_facts);platform=load(platform_facts);closure=load(args.support_closure)
        assert std['compiler']=='4.35.0-rc3' and platform['compiler']=='4.33.1' and closure['compiler']=='4.35.0-rc3'
        assert closure['schema']=='decidable-standard-source-closure-v1' and closure['recordCount']==len(closure['records'])
        originals=load(args.unit_dir/'original-exprs.json');rows={r['name']:r for r in originals['records']}
        target_rows={r['name']:r for r in platform['records']}
        config=load(args.base_config)
        for proof in PROOFS:
            r=rows[proof];assert r['selected'] and r['isProposition'] and r['constantKind']=='theorem' and not r['isInstance']
            assert 'AbcAdaptation.Reference.'+proof not in target_rows
            aux=target_rows['AbcAdaptation.Reference.'+proof.removesuffix('._proof_1')+'._aux_1']
            assert aux['kind']=='definition','target auxiliary is data; it cannot identify the source proof'
        prior_map=config['projectMap'];removed=[r for r in prior_map if r['original'] in PROOFS]
        assert len(removed)==len(PROOFS) and all(r['required'] for r in removed)
        config['projectMap']=[r for r in prior_map if r['original'] not in PROOFS]
        config['expectedNamedSelectedCount']=config['expectedSelectedCount']-len(PROOFS)
        config['expectedProofValueResolutionCount']=len(PROOFS)
        current_targets={r['target'] for r in config['projectMap']}
        target_only=sorted(n for n in target_rows if n.startswith('AbcAdaptation.Reference.') and n not in current_targets)
        config['expectedTargetOnlyCompilerDeclarations']=target_only
        config['targetOnlyCompilerProvenance']=[{'target':n,'actualCompilerRecord':target_rows[n],
            'sourceParentOriginal':n.removeprefix('AbcAdaptation.Reference.').rsplit('.',1)[0],
            'targetIdentityForSourceProof':False,'ownerAxiomAuditRequired':True,
            'wholeParentValueEqualityRequired':True} for n in target_only]
        config['proofValueResolutions']=[{'original':n,'standaloneTargetIdentity':None,'sourceRecord':rows[n],'parentOriginal':n.rsplit('.',1)[0],'resolution':'genuine-exported-original-proof-value'} for n in PROOFS]
        config['decidableStandardCompatibility']={
            'sourceFacts':binding(source_facts),'sourceReceipt':binding(source_receipt),
            'platformFacts':binding(platform_facts),'platformReceipt':binding(platform_receipt),
            'supportClosure':binding(args.support_closure),'supportReceipt':binding(args.support_receipt),
            'policy':'actual source standard bodies only; preserve actual Boolean/reflection; two proof values have no standalone target identities; both complete parent values require kernel equality'}
        for p in [source_facts,source_receipt,platform_facts,platform_receipt,args.support_closure,args.support_receipt,args.unit_dir/'original-exprs.json']:
            config['inputEvidence'].append({'path':str(p.resolve()),'sha256':sha(p)})
        dump(args.config_output,config)
        summary.update(config=str(args.config_output),configSha256=sha(args.config_output),expectedOriginalSelected=config['expectedSelectedCount'],expectedNamedSelected=config['expectedNamedSelectedCount'],expectedProofResolutions=len(PROOFS),projectMapCount=len(config['projectMap']))
    else:
        summary['configuration']='Pass --support-closure and --support-receipt after genuine closure query succeeds.'
    print(json.dumps(summary,indent=2))


if __name__=='__main__':main()
