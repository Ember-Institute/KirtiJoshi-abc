#!/usr/bin/env python3
"""Build the draft from the current main auditor; no compilation or main writes."""
from pathlib import Path
import hashlib,json,difflib
HERE=Path(__file__).resolve().parent
SOURCE=Path('/home/admin-wsl/Coq/abc/prove2me_workspace/.local/adaptation/reference-packet-field-carriers-20261115/AuditNextCarriers.lean')
s=SOURCE.read_text();base=s
def replace(a,b):
 global s
 assert s.count(a)==1,(a,s.count(a));s=s.replace(a,b)
replace('structure Relocations where\n', (HERE/'ProofResolutionDeclarations.lean.fragment').read_text()+'\nstructure Relocations where\n')
replace('  targetPrefix : Name\n','  targetPrefix : Name\n  elisions : Array ProofElision\n')
a=s.index('partial def decodeExpr (rs : Relocations)');b=s.index('def readRelocations',a)
s=s[:a]+(HERE/'ProofResolutionDecoder.lean.fragment').read_text()+'\n'+(HERE/'ProofResolutionEvidence.lean.fragment').read_text()+'\n'+s[b:]
replace('def readRelocations (config : Json) : MetaM Relocations := do','def readRelocations (config : Json) (records : Array Json) : MetaM Relocations := do\n  let elisions ← readProofElisions config records')
replace('''        unless sourcePrefixes.any (·.isPrefixOf original) && target == targetPrefix ++ original do
          throwError "Unexpected project relocation {original} -> {target}"''','''        let exactApprovedRename := original == approvedRenamedOriginal && target == approvedRenamedTarget
        unless sourcePrefixes.any (·.isPrefixOf original) &&
            (target == targetPrefix ++ original || exactApprovedRename) do
          throwError "Unexpected project relocation {original} -> {target}"
        if elisions.any (·.original == original) then
          throwError "Elided original proof must not claim a named target {original}"''')
replace('  return ⟨result, projectPrefixes, sourcePrefixes, targetPrefix⟩','''  unless result.size == (← checked (config.getObjValAs? Nat "expectedNamedMappingCount")) do
    throwError "Named relocation count differs"
  unless result.any (fun row => row.original == approvedRenamedOriginal && row.target == approvedRenamedTarget) do
    throwError "Approved generated helper rename is missing"
  return ⟨result, projectPrefixes, sourcePrefixes, targetPrefix, elisions⟩''')
replace('def compareRecord (rs : Relocations)',(HERE/'ProofResolutionValidation.lean.fragment').read_text()+'\ndef compareRecord (rs : Relocations)')
replace('  let rs ← readRelocations config','  let rs ← readRelocations config records')
replace('  let mut requiredCount := 0','''  let mut requiredCount := 0
  let mut namedRequiredCount := 0
  let mut proofResolutionReports : Array Json := #[]
  let mut resolvedProofNames : Array Name := #[]
  let expectedNamedSelectedCount ← checked (config.getObjValAs? Nat "expectedNamedSelectedCount")
  let expectedElidedProofCount ← checked (config.getObjValAs? Nat "expectedElidedProofCount")
  unless expectedNamedSelectedCount == 131 && expectedElidedProofCount == 2 &&
      expectedSelectedCount == expectedNamedSelectedCount + expectedElidedProofCount &&
      rs.elisions.size == expectedElidedProofCount do
    throwError "This reviewed resolution requires131 named +2 proof obligations =133 selected originals"''')
replace('''    let selected ← checked (record.getObjValAs? Bool "selected")
    let targetName ← checked (relocated rs original)
    if selected then requiredCount := requiredCount + 1''','''    let selected ← checked (record.getObjValAs? Bool "selected")
    if selected then requiredCount := requiredCount + 1
    if let some elision := rs.elisions.find? (·.original == original) then
      unless selected && elision.record == record do
        throwError "Approved proof resolution lost its exact selected original record {original}"
      proofResolutionReports := proofResolutionReports.push (← validateProofElision rs allowedOwners elision)
      resolvedProofNames := resolvedProofNames.push original
      continue
    let targetName ← checked (relocated rs original)
    if selected then namedRequiredCount := namedRequiredCount + 1''')
replace('  unless requiredCount == expectedSelectedCount do throwError "Mandatory selected count differs from config"','''  unless requiredCount == expectedSelectedCount do throwError "Mandatory selected count differs from config"
  unless namedRequiredCount == expectedNamedSelectedCount &&
      proofResolutionReports.size == expectedElidedProofCount &&
      approvedProofElisions.all resolvedProofNames.contains do
    throwError "Named versus genuine-proof resolution accounting differs"
  let ownerComparisons := comparisons.filter fun row =>
    (stringField row "original").toOption == some proofParent.toString
  unless ownerComparisons.size == 1 &&
      (← checked (ownerComparisons[0]!.getObjValAs? Bool "kernelTypeEqual")) &&
      (← checked (ownerComparisons[0]!.getObjValAs? Bool "kernelValueEqual")) &&
      !(← checked (ownerComparisons[0]!.getObjValAs? Bool "proofDeclaration")) do
    throwError "Internal proof resolutions require full owning solvableClosure type/value equivalence"
  proofResolutionReports := proofResolutionReports.map fun row => Json.mkObj [
    ("proofResolution", row), ("ownerTypeKernelEqual", toJson true),
    ("ownerComputationalValueKernelEqual", toJson true),
    ("coveredByOriginalOwner", encodeName proofParent)]''')
replace('("configuration", config), ("requiredComparedCount", toJson requiredCount),','''("configuration", config), ("requiredComparedCount", toJson namedRequiredCount),
    ("requiredSourceDeclarationCount", toJson requiredCount),
    ("requiredEliminatedInternalProofCount", toJson proofResolutionReports.size),
    ("requiredResolvedCount", toJson (namedRequiredCount + proofResolutionReports.size)),
    ("eliminatedInternalProofResolutions", Json.arr proofResolutionReports),
    ("internalProofRenames", ← checked (field config "internalProofRenames")),''')
replace('logInfo s!"Next carrier audit: {requiredCount} mandatory exact types; {comparisons.size} total original/target pairs; {ownedReports.size} artifact-owned axiom closures"','logInfo s!"Next carrier audit: {namedRequiredCount} mandatory named exact types +{proofResolutionReports.size} genuine original proof resolutions ={requiredCount} selected originals; {comparisons.size} total named pairs; {ownedReports.size} artifact-owned axiom closures"')
out=HERE/'AuditNextCarriers.lean';out.write_text(s)
(HERE/'audit-helper-resolution.diff').write_text(''.join(difflib.unified_diff(base.splitlines(True),s.splitlines(True),fromfile='main/AuditNextCarriers.lean',tofile='draft/AuditNextCarriers.lean')))
manifest={'schema':'next-carrier-helper-audit-draft-v4','status':'draft-not-compiled','base':{'path':str(SOURCE),'sha256':hashlib.sha256(base.encode()).hexdigest()},'draft':{'path':str(out),'sha256':hashlib.sha256(out.read_bytes()).hexdigest()},'config':{'path':str(HERE/'audit-config.json'),'sha256':hashlib.sha256((HERE/'audit-config.json').read_bytes()).hexdigest()}}
(HERE/'draft-manifest.json').write_text(json.dumps(manifest,indent=2)+'\n');print(json.dumps(manifest,indent=2))
