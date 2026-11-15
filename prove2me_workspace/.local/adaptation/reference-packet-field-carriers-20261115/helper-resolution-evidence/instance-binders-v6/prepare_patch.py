#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,difflib
HERE=Path(__file__).resolve().parent
UNIT=Path('/home/admin-wsl/Coq/abc/prove2me_workspace/.local/adaptation/reference-packet-field-carriers-20261115')
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
s=(UNIT/'AuditNextCarriers.lean').read_text();base=s
def replace(a,b):
 global s
 assert s.count(a)==1,(a,s.count(a));s=s.replace(a,b)
replace('def compareRecord (rs : Relocations)',(HERE/'InternalInstanceBinderComparison.lean.fragment').read_text()+'\ndef compareRecord (rs : Relocations)')
replace('''  unless binderInventory sourceType == binderInventory targetType do
    throwError "Full type BinderInfo inventory differs for {original}"
  unless binderPlacement sourceType == binderPlacement targetType do
    throwError "BinderInfo placement inside the type differs for {original}"
  kernelTypeEq s!"original versus target type {original}" sourceType targetType''','''  -- The exact full kernel type check precedes any internal-implementation
  -- accounting. A binder exception cannot make a different type pass.
  kernelTypeEq s!"original versus target type {original}" sourceType targetType
  let rawBinderInventoryEqual := binderInventory sourceType == binderInventory targetType
  let rawBinderPlacementEqual := binderPlacement sourceType == binderPlacement targetType
  let mut internalBinderEvidence := Json.null
  if !rawBinderInventoryEqual || !rawBinderPlacementEqual then
    internalBinderEvidence ← compareInternalInstanceBinders original target.name sourceType targetType''')
replace('''    ("allExpressionBinderInfoEqual", toJson true),
    ("binderInfoPlacementEqual", toJson true),''','''    ("allExpressionBinderInfoEqual", toJson rawBinderInventoryEqual),
    ("binderInfoPlacementEqual", toJson rawBinderPlacementEqual),
    ("exposedBinderInfoEqual", toJson true),
    ("implementationDataInstanceKernelEqual", if internalBinderEvidence == Json.null then Json.null else toJson true),
    ("binderImplementationDifferenceAccountedFor", toJson (internalBinderEvidence != Json.null)),
    ("internalBinderImplementationEvidence", internalBinderEvidence),''')
out=HERE/'AuditNextCarriers.lean';out.write_text(s)
configout=HERE/'audit-config.json';configout.write_bytes((UNIT/'audit-config.json').read_bytes())
(HERE/'internal-instance-binders.diff').write_text(''.join(difflib.unified_diff(base.splitlines(True),s.splitlines(True),fromfile='main/AuditNextCarriers.lean',tofile='v6/AuditNextCarriers.lean')))
j={'schema':'next-carrier-internal-instance-binder-draft-v6','status':'draft-not-compiled','base':{'path':str(UNIT/'AuditNextCarriers.lean'),'sha256':hashlib.sha256(base.encode()).hexdigest()},'draft':{'path':str(out),'sha256':sha(out)},'config':{'path':str(configout),'sha256':sha(configout)},'configChange':False,'scope':'exact approved helper3->actual2 only; whole typeeq first; strict8parameter domains+3type arguments; each3data SMul instances independently kernel-equal after closure over8parameters'}
(HERE/'draft-manifest.json').write_text(json.dumps(j,indent=2)+'\n');print(json.dumps(j,indent=2))
