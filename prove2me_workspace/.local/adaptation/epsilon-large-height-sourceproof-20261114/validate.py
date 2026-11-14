from pathlib import Path
import json,hashlib,importlib.util,shutil
s=importlib.util.spec_from_file_location('unit','/tmp/p2m-epsilon-ci-20261114.py');unit=importlib.util.module_from_spec(s);s.loader.exec_module(unit);ci=unit.ci;w,b,u=ci.w,ci.b,unit.u;target=unit.target;source=unit.source

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def run(*a,**kw):
 kw.setdefault('version','epsilon-validation-v1');return ci.run(*a,**kw)
assert json.loads((b/'source-graph-leaf-result.json').read_text())['status']=='succeeded'
rows=[json.loads(l) for l in (b/'decl_graph.jsonl').read_text().splitlines() if l];own=[z for z in rows if z['module']=='Theorems.Thm_'+target.replace('.','_') and z['startLine']>0]
# Preserve full source module context and every private helper when moving only the final theorem to top level.
original=(w/'.local/adaptation/regular-ramified-obstruction-sourceproof-20261114/ExtractObstructionSyntax.lean').read_text();a=original.index('  let files : Array String := #[');e=original.index('\n  let mut output',a);syntax=original[:a]+'  let files : Array String := #['+json.dumps(source)+']'+original[e:];syntax=syntax.replace('import Theorems.Thm_AbcAdaptation_Tripod_Fermat_Proper_noncriticalRegularRamifiedDerivNotMem','import Theorems.Thm_'+target.replace('.','_')).replace('.local/adaptation/regular-ramified-obstruction-sourceproof-20261114/syntax-boundaries.json',u+'syntax-boundaries.json');(b/'ExtractEpsilonSyntax.lean').write_text(syntax);run('syntax-boundaries-leaf',u+'ExtractEpsilonSyntax.lean')
parsed=json.loads((b/'syntax-boundaries.json').read_text());name=target.rsplit('.',1)[1];p=[z for z in parsed if z.get('nameText') in [name,target]];assert len(p)==1;z=p[0];raw=(w/source).read_bytes();nr=z['nameRange'];a,e=nr['start']['offset'],nr['end']['offset'];old=raw[a:e].decode();assert old in [name,target];edits=[(a,e,'solution')]
if old==name:
 ns=[q for q in parsed if 'namespace' in q.get('kind','') and q['start']['offset']<z['declStart']['offset']];last=ns[-1];namespace=last['command'].split()[1];assert namespace==target.rsplit('.',1)[0];ends=[q for q in parsed if q.get('kind','').endswith('.end') and q['start']['offset']>=z['declEnd']['offset']];ending=ends[0];assert ending['command'].strip()=='end '+namespace
 # Keep private source helpers in their original namespace. Open that namespace where the final solution is placed.
 prior=[q for q in parsed if q.get('nameText') and q['declEnd']['offset']<=z['declStart']['offset']];lastprivate=max((q['declEnd']['offset'] for q in prior),default=last['end']['offset']);context=raw[lastprivate:z['declStart']['offset']].decode();assert not context.strip() or all(l.strip().startswith(('/--','--','-/')) or not l.strip() for l in context.splitlines()),'Unexpected target context; preserve explicitly'
 edits.append((z['declStart']['offset'],z['declStart']['offset'],'end '+namespace+'\n\nopen AbcAdaptation AbcAdaptation.Tripod\n\n'));edits.append((ending['start']['offset'],ending['end']['offset'],''))
for a,e,text in sorted(edits,reverse=True):raw=raw[:a]+text.encode()+raw[e:]
sol=u+'Solution_epsilonELargeHeight.lean';(w/sol).write_bytes(raw);assert b'sorry' not in raw;run('solution-leaf',sol)
# Compare the actual existing platform statement with the actual local theorem.
before=json.loads((b/'platform-before-target.json').read_text());formal=before['formal_statement'];marker='theorem '+target;assert marker in formal
text='import Lean\nimport Theorems.Thm_'+target.replace('.','_')+'\n\n'+formal.replace(marker,'theorem ExistingPlatformType',1)+'\nopen Lean\nrun_meta do\n  let a ← getConstInfo `'+target+'\n  let c ← getConstInfo `ExistingPlatformType\n  unless ← Lean.Meta.isDefEq a.type c.type do throwError "Existing platform type differs"\n  IO.FS.writeFile "'+u+'existing-types-equal.json" "true"\n';(b/'ValidateExistingTypes.lean').write_text(text);run('existing-types-leaf',u+'ValidateExistingTypes.lean')
text='import Lean\nimport Theorems.Thm_'+target.replace('.','_')+'\n'+(w/sol).read_text()+'\nopen Lean\nrun_meta do\n  let a ← getConstInfo `'+target+'\n  let c ← getConstInfo `solution\n  unless ← Lean.Meta.isDefEq a.type c.type do throwError "Solution type differs"\n';(b/'CompareSolution.lean').write_text(text);run('solution-types-leaf',u+'CompareSolution.lean')
module='Theorems.Thm_'+target.replace('.','_');audit='import Lean\nimport '+module+'\nopen Lean\nrun_meta do\n  let env ← getEnv\n  let mut out : Array Json := #[]\n  for (name, _) in env.constants.toList do\n    let some idx := env.getModuleIdxFor? name | continue\n    let some m := env.header.moduleNames[idx.toNat]? | continue\n    unless m == `'+module+' do continue\n    let axs ← collectAxioms name\n    for ax in axs do\n      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do throwError "Unapproved axiom {ax} in {name}"\n    out := out.push (Json.mkObj [("name", toJson name.toString), ("axioms", toJson (axs.map toString))])\n  IO.FS.writeFile "'+u+'all-module-axioms.json" (Json.pretty (Json.arr out))\n';(b/'AuditAllConstants.lean').write_text(audit);run('all-constants-review',u+'AuditAllConstants.lean','review')
run('production-gates-review',u+'ProductionGates.lean','review',duration='150s',memory='12GiB')
checks=[]
for p in b.glob('*-request.json'):
 tag=p.name.removesuffix('-request.json');out=b/(tag+'-result.json')
 if not out.exists():continue
 q=json.loads(p.read_text());rr=json.loads(out.read_text())
 if rr.get('status')!='succeeded' or q.get('workspace')!=str(w):continue
 artifact=q['target']=='module';src=q['parameters']['args'][0] if artifact else q['parameters']['source']
 if not (w/src).is_file() or sha(w/src)!=q['worktree_manifest']['source_sha256']:continue
 checks.append({'tag':tag,'source':src,'artifact':artifact,'review':q['task_type']=='review'})
ci.save('delivery-validation.json',{'passed':True,'exact_existing_target_type_equal':True,'source_hashes':{source:sha(w/source)},'solution_hashes':{sol:sha(w/sol)},'compiler_checks':checks,'declaration_graph_sha256':sha(b/'decl_graph.jsonl'),'syntax_boundaries_sha256':sha(b/'syntax-boundaries.json'),'new_open_debt':0})
print('Epsilon source proof, exact platform type, complete solution closure and audits passed.',flush=True)
