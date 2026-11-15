#!/usr/bin/env python3
from pathlib import Path
import json,hashlib,difflib
HERE=Path(__file__).resolve().parent
UNIT=Path('/home/admin-wsl/Coq/abc/prove2me_workspace/.local/adaptation/reference-packet-field-carriers-20261115')
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
s=(UNIT/'AuditNextCarriers.lean').read_text();base=s
def replace(a,b):
 global s
 assert s.count(a)==1,(a,s.count(a));s=s.replace(a,b)
replace('def compareRecord (rs : Relocations) (record : Json) (target : ConstantInfo) : MetaM Json := do',(HERE/'GeneratedEliminatorEquality.lean.fragment').read_text()+'\ndef compareRecord (rs : Relocations) (allowedOwners : Array Name) (record : Json) (target : ConstantInfo) : MetaM Json := do')
replace('  let mut comparedValue := false','  let mut comparedValue := false\n  let mut definitionallyEqualValue := false\n  let mut propositionalValueEquality := Json.null')
replace('''    kernelTermEq s!"original versus target computational value {original}" sourceValue targetValue
    comparedValue := true''','''    -- Both values and their exact common type were kernel-checked above.
    let definitionallyEqual ← match Kernel.isDefEq (← getEnv) {} sourceValue targetValue with
      | .ok equal => pure equal
      | .error exception => throwKernelException exception
    if definitionallyEqual then
      definitionallyEqualValue := true
    else
      propositionalValueEquality ← proveGeneratedEliminatorEquality rs allowedOwners
        original sourceType sourceValue targetValue
    comparedValue := true''')
replace('("computationShapeEqual", toJson true), ("kernelValueEqual", toJson comparedValue),','''("computationShapeEqual", toJson true), ("kernelValueEqual", toJson definitionallyEqualValue),
    ("computationalValueEqualityChecked", toJson comparedValue),
    ("kernelPropositionalValueEquality", toJson (propositionalValueEquality != Json.null)),
    ("propositionalValueEqualityEvidence", propositionalValueEquality),''')
replace('compareRecord rs record (← getConstInfo targetName)','compareRecord rs allowedOwners record (← getConstInfo targetName)')
out=HERE/'AuditNextCarriers.lean';out.write_text(s)
(HERE/'generated-eliminator-equality.diff').write_text(''.join(difflib.unified_diff(base.splitlines(True),s.splitlines(True),fromfile='main/AuditNextCarriers.lean',tofile='v5/AuditNextCarriers.lean')))
c=json.loads((UNIT/'audit-config.json').read_text());entries=c['internalProofEvidence']['files'];old=[row for row in entries if row['path']==str(UNIT/'audit-config.json')];assert len(old)==1
archive=UNIT/'attempts/kernel-audit-v1/audit-config.json';assert sha(archive)==old[0]['sha256'];old[0]['path']=str(archive)
configout=HERE/'audit-config.json';configout.write_text(json.dumps(c,indent=2,ensure_ascii=False)+'\n')
manifest={'schema':'next-carrier-generated-eliminator-equality-draft-v5','status':'draft-not-compiled','base':{'path':str(UNIT/'AuditNextCarriers.lean'),'sha256':hashlib.sha256(base.encode()).hexdigest()},'draft':{'path':str(out),'sha256':sha(out)},'config':{'path':str(configout),'sha256':sha(configout)},'onlyConfigChange':'internalProofEvidence.files previous baseline config now names immutable attempts/kernel-audit-v1/audit-config.json with unchanged hash'}
(HERE/'draft-manifest.json').write_text(json.dumps(manifest,indent=2)+'\n');print(json.dumps(manifest,indent=2))
