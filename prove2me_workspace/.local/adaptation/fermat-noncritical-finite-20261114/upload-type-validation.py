from pathlib import Path
import importlib.util,json,hashlib
w=Path('/home/admin-wsl/Coq/abc/prove2me_workspace');b=w/'.local/adaptation/fermat-noncritical-finite-20261114'
s=importlib.util.spec_from_file_location('riemann_ci','/tmp/p2m-finite-ci-20261114.py');ci=importlib.util.module_from_spec(s);s.loader.exec_module(ci);ci=ci.ci
original_run=ci.run
def run(*args,**kwargs):
 kwargs.setdefault('version','finite-v3');return original_run(*args,**kwargs)
ci.run=run
for tag in ['closed-axioms-review','reduction-axioms-leaf']:
 x=json.loads((b/(tag+'-result.json')).read_text());assert x['status']=='succeeded'
ci.run('source-graph-leaf','.local/adaptation/fermat-noncritical-finite-20261114/ExtractFiniteGraph.lean')
rows=[json.loads(t) for t in (b/'decl_graph.jsonl').read_text().splitlines() if t.strip()];by={x['name']:x for x in rows};pre='AbcAdaptation.Tripod.Fermat.Proper.'
new=['noncriticalRegularRamifiedDerivNotMem','noncriticalDerivativeBadPlacesFinite'];existing=['noncriticalRamificationFinite'];defs=['FermatCurveDerivationEtale','FermatCurveDerivationPolynomial','FermatCurveDerivationBasic']
# Audit actual Names from the elaborated environment, including private/generated helpers.
audit='import Lean\n'+ '\n'.join('import Definitions.Def_'+n for n in defs)+'\nopen Lean\nrun_meta do\n  let mut rows : Array Json := #[]\n'
audit+='  let modules : Array Name := #['+', '.join('`Definitions.Def_'+n for n in defs)+']\n'
audit+='  let env ← getEnv\n  for (n, _) in env.constants.toList do\n    let some idx := env.getModuleIdxFor? n | continue\n    let some m := env.header.moduleNames[idx.toNat]? | continue\n    unless modules.contains m do continue\n    let axs ← collectAxioms n\n    for ax in axs do\n      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do throwError "Unapproved axiom {ax} in {n}"\n    rows := rows.push (Json.mkObj [("name", toJson n.toString), ("axioms", toJson (axs.map toString))])\n  IO.FS.writeFile ".local/adaptation/fermat-noncritical-finite-20261114/all-definition-axioms.json" (Json.pretty (Json.arr rows))\n'
f='.local/adaptation/fermat-noncritical-finite-20261114/AuditAllDefinitions.lean';(w/f).write_text(audit);ci.run('all-definitions-axioms-review',f,'review')
preamble='import Definitions.Def_FermatProperCarrier\n'+'\n'.join('import Definitions.Def_'+n for n in defs)+'\n\nset_option autoImplicit false\nopen scoped IntermediateField\nopen AbcAdaptation.Tripod.Fermat.Proper'
items=[]
for n in new:
 row=by[pre+n];assert row['kind']=='theorem' and row['module']=='Theorems.Thm_'+(pre+n).replace('.','_')
 source_lines=(w/(row['module'].replace('.','/')+'.lean')).read_text().splitlines()
 declaration='\n'.join(source_lines[row['startLine']-1:row['endLine']])
 marker='theorem '+n
 assert declaration.count(marker)==1 and 'sorry' in declaration
 declaration=declaration.replace(marker,'theorem '+pre+n,1)
 items.append({'theorem_name':pre+n,'preamble':preamble,'formal_statement':declaration})
ci.save('upload-problem-items.json',items)
code=preamble+'\n\n'+'\n\n'.join(x['formal_statement'] for x in items)+'\n\nset_option pp.fullNames true\nset_option pp.funBinderTypes true\nopen Lean\nrun_meta do\n  let mut rows : Array Json := #[]\n'
for n in new:
 code+='  let info ← getConstInfo `'+pre+n+'\n  let fmt ← Lean.Meta.ppExpr info.type\n  rows := rows.push (Json.mkObj [("name", Json.str "'+pre+n+'"), ("type", Json.str fmt.pretty)])\n'
code+='  IO.FS.writeFile ".local/adaptation/fermat-noncritical-finite-20261114/upload-elaborated-types.json" (Json.pretty (Json.arr rows))\n'
f='.local/adaptation/fermat-noncritical-finite-20261114/ValidateElaboratedTypes.lean';(w/f).write_text(code);ci.run('elaborated-types-leaf',f)
got={x['name']:x['type'] for x in json.loads((b/'upload-elaborated-types.json').read_text())};assert all(got[pre+n]==by[pre+n]['elaboratedType'] for n in new)
# Source spans come from the elaborated environment. Only the known theorem identifier is replaced.
for n in existing:
 row=by[pre+n];path=w/(row['module'].replace('.','/')+'.lean');lines=path.read_text().splitlines();decl='\n'.join(lines[row['startLine']-1:row['endLine']]);prefix='theorem '+n;assert decl.count(prefix)==1,(n,decl[:100]);decl=decl.replace(prefix,'theorem solution',1)
 imports=[l for l in lines if l.startswith('import ')];assert not any('Thm_'+(pre+n).replace('.','_') in l for l in imports)
 text='\n'.join(imports)+'\n\nset_option autoImplicit false\nopen scoped IntermediateField\nopen AbcAdaptation.Tripod.Fermat.Proper\n\n'+decl+'\n'
 text='import Definitions.Def_FermatCurveFieldZerosPoles\n'+text
 assert 'sorry' not in text
 target='.local/adaptation/fermat-noncritical-finite-20261114/Solution_'+n+'.lean';(w/target).write_text(text);ci.run('solution-'+n+'-leaf',target,memory='6GiB' if list((b/'attempts').glob('solution-'+n+'-leaf-v*-result.json')) else '16GiB')
# Published child modules have minimal preambles; local child modules import more facts.
# Check the complete submitted proof using inline copies of those exact published child statements.
solution=(b/'Solution_noncriticalRamificationFinite.lean').read_text()
solution_imports=[line for line in solution.splitlines() if line.startswith('import ') and not line.startswith('import Theorems.')]
solution_body='\n'.join(line for line in solution.splitlines() if not line.startswith('import '))
import_lines=list(dict.fromkeys([line for line in preamble.splitlines() if line.startswith('import ')]+solution_imports))
mirror='\n'.join(import_lines)+'\n\nset_option autoImplicit false\nopen scoped IntermediateField\nopen AbcAdaptation.Tripod.Fermat.Proper\n\n'+'\n\n'.join(item['formal_statement'] for item in items)+'\n\n'+solution_body+'\n\n#print axioms solution\n'
f='.local/adaptation/fermat-noncritical-finite-20261114/ValidatePublishedChildContext.lean';(w/f).write_text(mirror);ci.run('published-child-context-leaf',f)
ci.save('published-child-context-validation.json',{'passed':True,'source_sha256':hashlib.sha256((w/f).read_bytes()).hexdigest(),'solution_sha256':hashlib.sha256((b/'Solution_noncriticalRamificationFinite.lean').read_bytes()).hexdigest(),'proof_value_import':'Definitions.Def_FermatCurveFieldZerosPoles','method':'Exact uploaded Open statements/preambles are inlined into a fresh file; local Theorems modules are excluded. The complete solution is checked with its explicit closed proof dependency.'})
# Verify the three already-published target types against the exact local declarations.
imports='import Lean\n'+'\n'.join('import Theorems.Thm_'+(pre+n).replace('.','_') for n in existing)+'\n\nset_option autoImplicit false\nopen scoped IntermediateField\n'
code=imports
for n in existing:
 old=json.loads((b/('platform-before-'+n+'.json')).read_text());formal=old['formal_statement'];prefix='theorem '+pre+n;assert formal.startswith(prefix);code+='\n'+'theorem PlatformAudit_'+n+formal[len(prefix):]+'\n'
code+='\nopen Lean\nrun_meta do\n'
for n in existing:
 code+='  let a ← getConstInfo `'+pre+n+'\n  let p ← getConstInfo `PlatformAudit_'+n+'\n  unless ← Lean.Meta.isDefEq a.type p.type do throwError "Original platform target type differs: '+n+'"\n'
code+='  IO.FS.writeFile ".local/adaptation/fermat-noncritical-finite-20261114/existing-types-equal.json" "true"\n';f='.local/adaptation/fermat-noncritical-finite-20261114/ValidateExistingTypes.lean';(w/f).write_text(code);ci.run('existing-types-leaf',f)
ci.run('production-gates-review','.local/adaptation/fermat-noncritical-finite-20261114/ProductionGates.lean','review',duration='150s',memory='12GiB')
ci.save('upload-validation.json',{'passed':True,'elaborated_types_equal':True,'new_theorem_count':len(new),'upload_problem_items_sha256':hashlib.sha256((b/'upload-problem-items.json').read_bytes()).hexdigest(),'existing_target_types_definitionally_equal':True,'definition_hashes':{'Definitions/Def_'+n+'.lean':hashlib.sha256((w/('Definitions/Def_'+n+'.lean')).read_bytes()).hexdigest() for n in defs},'source_theorem_hashes':{pre+n:hashlib.sha256((w/('Theorems/Thm_'+(pre+n).replace('.','_')+'.lean')).read_bytes()).hexdigest() for n in existing+new},'source_graph_sha256':hashlib.sha256((b/'decl_graph.jsonl').read_bytes()).hexdigest(),'method':'Prove2Me compiled declaration graph and exact source theorem spans preserve explicit valuation-subring coercions in exported Open statements; re-elaborated printed types are compared to original compiled types, and Lean.Meta.isDefEq checks the existing target. No regex declaration splitting.'})
print('Finite-ramification exact children, submitted proof body, existing target type and production gates validated.',flush=True)
