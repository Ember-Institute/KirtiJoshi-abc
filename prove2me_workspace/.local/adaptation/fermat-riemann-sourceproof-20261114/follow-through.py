from pathlib import Path
import json,runpy,time,importlib.util,hashlib
w=Path('/home/admin-wsl/Coq/abc/prove2me_workspace');b=w/'.local/adaptation/fermat-riemann-sourceproof-20261114'
s=importlib.util.spec_from_file_location('ci','/tmp/p2m-riemann-sourceproof-ci-20261114.py');ci=importlib.util.module_from_spec(s);s.loader.exec_module(ci)
while True:
 p=b/'sourceproof-closed-review-result.json'
 if p.exists():
  assert json.loads(p.read_text())['status']=='succeeded';break
 time.sleep(15)
for n in ['riemannRochFiniteDimensional','riemannRochDimensionUpperBound','riemannRochEventuallyLinear','polarPresentationExists']:
 f='Theorems/Thm_AbcAdaptation_Tripod_Fermat_Proper_'+n+'.lean';ci.run('derived-'+n+'-leaf',f,memory='6GiB');ci.run('derived-'+n+'-artifact',f,artifact=True)
ci.run('source-closure-review','Solutions/Checks_FermatRiemannSourceClosure.lean','review',memory='8GiB')
ci.run('source-graph-leaf','.local/adaptation/fermat-riemann-sourceproof-20261114/ExtractSourceProofGraph.lean')
pre='AbcAdaptation.Tripod.Fermat.Proper.';names=['functionZeroPoleDegrees','riemannPolarApproximation','riemannBasisPowerLowerBound'];mods=['FermatCurveFieldDegree','FermatFunctionFiberDegrees','FermatRiemannPolarApproximation','FermatRiemannBasisPowers']
rows=[json.loads(l) for l in (b/'decl_graph.jsonl').read_text().splitlines() if l.strip()];by={r['name']:r for r in rows}
for n in names:
 row=by[pre+n];f=w/(row['module'].replace('.','/')+'.lean');lines=f.read_text().splitlines();decl='\n'.join(lines[row['startLine']-1:row['endLine']]);marker='theorem '+n;assert decl.count(marker)==1;decl=decl.replace(marker,'theorem solution',1);imports=[l for l in lines if l.startswith('import ')];assert not any('Thm_'+(pre+n).replace('.','_') in l for l in imports);text='\n'.join(imports)+'\n\nset_option autoImplicit false\nopen scoped IntermediateField\nopen AbcAdaptation.Tripod.Fermat.Proper\n\n'+decl+'\n';assert 'sorry' not in text;out='.local/adaptation/fermat-riemann-sourceproof-20261114/Solution_'+n+'.lean';(w/out).write_text(text);ci.run('solution-'+n+'-leaf',out)
# Existing platform signatures and the elaborated local types are compared inside Lean.
text='import Lean\n'+ '\n'.join('import Theorems.Thm_'+(pre+n).replace('.','_') for n in names)+'\nopen scoped IntermediateField\nset_option autoImplicit false\n'
for n in names:
 old=json.loads((b/('platform-before-'+n+'.json')).read_text());marker='theorem '+pre+n;decl=old['formal_statement'];assert decl.startswith(marker);text+='\n'+'theorem PlatformTarget_'+n+decl[len(marker):]+'\n'
text+='\nopen Lean\nrun_meta do\n'
for n in names:text+='  let a ← getConstInfo `'+pre+n+'\n  let b ← getConstInfo `PlatformTarget_'+n+'\n  unless ← Lean.Meta.isDefEq a.type b.type do throwError "Target type differs: '+n+'"\n'
text+='  IO.FS.writeFile ".local/adaptation/fermat-riemann-sourceproof-20261114/platform-types-equal.json" "true"\n';f='.local/adaptation/fermat-riemann-sourceproof-20261114/ValidatePlatformTypes.lean';(w/f).write_text(text);ci.run('exact-platform-types-leaf',f)
# Check axioms of all new definition constants, including private helpers.
text='import Lean\n'+ '\n'.join('import Definitions.Def_'+n for n in mods)+'\nopen Lean\nrun_meta do\n  let mods : Array Name := #['+', '.join('`Definitions.Def_'+n for n in mods)+']\n  let env ← getEnv\n  let mut rows : Array Json := #[]\n  for (n, _) in env.constants.toList do\n    let some idx := env.getModuleIdxFor? n | continue\n    let some m := env.header.moduleNames[idx.toNat]? | continue\n    unless mods.contains m do continue\n    let axs ← collectAxioms n\n    for ax in axs do\n      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do throwError "Unexpected axiom {ax} in {n}"\n    rows := rows.push (Json.mkObj [("name", toJson n.toString), ("axioms", toJson (axs.map toString))])\n  IO.FS.writeFile ".local/adaptation/fermat-riemann-sourceproof-20261114/all-definition-axioms.json" (Json.pretty (Json.arr rows))\n';f='.local/adaptation/fermat-riemann-sourceproof-20261114/AuditAllDefinitions.lean';(w/f).write_text(text);ci.run('all-new-definition-axioms-review',f,'review',memory='8GiB')
(w/'.local/adaptation/fermat-riemann-sourceproof-20261114/ProductionGates.lean').write_text((w/'.local/adaptation/fermat-riemann-20261113/ProductionGates.lean').read_text());ci.run('production-gates-review','.local/adaptation/fermat-riemann-sourceproof-20261114/ProductionGates.lean','review',duration='150s',memory='12GiB')
ci.save('sourceproof-validation.json',{'passed':True,'exact_platform_types_equal':True,'closed_transitive_consumers':['riemannRochFiniteDimensional','riemannRochDimensionUpperBound','riemannRochEventuallyLinear','polarPresentationExists'],'definition_hashes':{'Definitions/Def_'+n+'.lean':hashlib.sha256((w/('Definitions/Def_'+n+'.lean')).read_bytes()).hexdigest() for n in mods},'theorem_hashes':{pre+n:hashlib.sha256((w/('Theorems/Thm_'+(pre+n).replace('.','_')+'.lean')).read_bytes()).hexdigest() for n in names},'declaration_graph_sha256':hashlib.sha256((b/'decl_graph.jsonl').read_bytes()).hexdigest(),'method':'Elaborated declaration graph source spans, exact source theorem identifier substitution, and Lean.Meta.isDefEq. All compilers scheduled by main agent with exclusive workspace.'})
print('All source proof, transitive closure, exact types, and production gates passed.',flush=True)
