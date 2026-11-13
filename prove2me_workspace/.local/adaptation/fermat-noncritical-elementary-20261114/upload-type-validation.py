from pathlib import Path
import importlib.util,json,hashlib
w=Path('/home/admin-wsl/Coq/abc/prove2me_workspace');b=w/'.local/adaptation/fermat-noncritical-elementary-20261114'
s=importlib.util.spec_from_file_location('riemann_ci','/tmp/p2m-elementary-ci-20261114.py');ci=importlib.util.module_from_spec(s);s.loader.exec_module(ci);ci=ci.ci
original_run=ci.run
def run(*args,**kwargs):
 kwargs.setdefault('version','elementary-v1');return original_run(*args,**kwargs)
ci.run=run
for tag in ['closed-axioms-review','reduction-axioms-leaf']:
 x=json.loads((b/(tag+'-result.json')).read_text());assert x['status']=='succeeded'
ci.run('source-graph-leaf','.local/adaptation/fermat-noncritical-elementary-20261114/ExtractElementaryGraph.lean')
rows=[json.loads(t) for t in (b/'decl_graph.jsonl').read_text().splitlines() if t.strip()];by={x['name']:x for x in rows};pre='AbcAdaptation.Tripod.Fermat.Proper.'
new=['noncriticalPolynomialOrderAtRegularPoint','noncriticalPolynomialOrderAtPole','noncriticalInverseRamification'];existing=['noncriticalElementaryCompositionRamification'];defs=['FermatNoncriticalElementarySource']
# Audit actual Names from the elaborated environment, including private/generated helpers.
audit='import Lean\n'+ '\n'.join('import Definitions.Def_'+n for n in defs)+'\nopen Lean\nrun_meta do\n  let mut rows : Array Json := #[]\n'
audit+='  let modules : Array Name := #['+', '.join('`Definitions.Def_'+n for n in defs)+']\n'
audit+='  let env ← getEnv\n  for (n, _) in env.constants.toList do\n    let some idx := env.getModuleIdxFor? n | continue\n    let some m := env.header.moduleNames[idx.toNat]? | continue\n    unless modules.contains m do continue\n    let axs ← collectAxioms n\n    for ax in axs do\n      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do throwError "Unapproved axiom {ax} in {n}"\n    rows := rows.push (Json.mkObj [("name", toJson n.toString), ("axioms", toJson (axs.map toString))])\n  IO.FS.writeFile ".local/adaptation/fermat-noncritical-elementary-20261114/all-definition-axioms.json" (Json.pretty (Json.arr rows))\n'
f='.local/adaptation/fermat-noncritical-elementary-20261114/AuditAllDefinitions.lean';(w/f).write_text(audit);ci.run('all-definitions-axioms-review',f,'review')
preamble='\n'.join('import Definitions.Def_'+n for n in defs)+'\n\nset_option autoImplicit false\nopen Polynomial\nopen scoped IntermediateField\nopen AbcAdaptation\nopen AbcAdaptation.Tripod.Fermat.Proper'
items=[]
for n in new:
 row=by[pre+n];assert row['kind']=='theorem' and row['module']=='Theorems.Thm_'+(pre+n).replace('.','_')
 source_lines=(w/(row['module'].replace('.','/')+'.lean')).read_text().splitlines()
 declaration='\n'.join(source_lines[row['startLine']-1:row['endLine']]);marker='theorem '+n
 assert declaration.count(marker)==1 and 'sorry' in declaration
 items.append({'theorem_name':pre+n,'preamble':preamble,'formal_statement':declaration.replace(marker,'theorem '+pre+n,1)})
ci.save('upload-problem-items.json',items)
code='\n'.join('import Theorems.Thm_'+(pre+n).replace('.','_') for n in new)+'\n'+preamble+'\n\n'+'\n\n'.join(x['formal_statement'].replace('theorem '+x['theorem_name'],'theorem ExportTarget_'+x['theorem_name'].removeprefix(pre),1) for x in items)+'\n\nset_option pp.fullNames true\nset_option pp.funBinderTypes true\nopen Lean\nrun_meta do\n  let mut rows : Array Json := #[]\n'
for n in new:
 code+='  let info ← getConstInfo `ExportTarget_'+n+'\n  let original ← getConstInfo `'+pre+n+'\n  unless ← Lean.Meta.isDefEq info.type original.type do throwError "Exported source target type differs: '+n+'"\n  let fmt ← Lean.Meta.ppExpr info.type\n  rows := rows.push (Json.mkObj [("name", Json.str "'+pre+n+'"), ("type", Json.str fmt.pretty)])\n'
code+='  IO.FS.writeFile ".local/adaptation/fermat-noncritical-elementary-20261114/upload-elaborated-types.json" (Json.pretty (Json.arr rows))\n'
code+='  IO.FS.writeFile ".local/adaptation/fermat-noncritical-elementary-20261114/export-types-equal.json" "true"\n'
f='.local/adaptation/fermat-noncritical-elementary-20261114/ValidateElaboratedTypes.lean';(w/f).write_text(code);ci.run('elaborated-types-leaf',f)
assert json.loads((b/'export-types-equal.json').read_text()) is True
# Source spans come from the elaborated environment. Only the known theorem identifier is replaced.
for n in existing:
 row=by[pre+n];path=w/(row['module'].replace('.','/')+'.lean');lines=path.read_text().splitlines();decl='\n'.join(lines[row['startLine']-1:row['endLine']]);prefix='theorem '+n;assert decl.count(prefix)==1,(n,decl[:100]);decl=decl.replace(prefix,'theorem solution',1)
 imports=[l for l in lines if l.startswith('import ')];assert not any('Thm_'+(pre+n).replace('.','_') in l for l in imports)
 text='\n'.join(imports)+'\n\nset_option autoImplicit false\nopen scoped IntermediateField\nopen AbcAdaptation.Tripod.Fermat.Proper\n\n'+decl+'\n'
 if n=='noncriticalElementaryCompositionRamification':
  helpers=sorted([r for r in rows if r['module']==row['module'] and r['startLine']>0 and r['name'].split('.')[-1] in ['poly_spec','mob_spec']],key=lambda r:r['startLine'])
  assert len(helpers)==2
  helper_text='\n\n'.join('\n'.join(lines[r['startLine']-1:r['endLine']]) for r in helpers)
  header='\n'.join(line for line in lines[:helpers[0]['startLine']-1] if not line.startswith('import '))
  # Source namespace/open commands before helper1 are retained verbatim; no target declaration occurs there.
  assert 'theorem ' not in header and 'lemma ' not in header
  text='\n'.join(imports)+'\n'+header+'\n'+helper_text+'\n\nend NoncriticalElementarySource\nend AbcAdaptation.Tripod.Fermat.Proper\n\nopen AbcAdaptation\nopen AbcAdaptation.Tripod.Fermat.Proper\nopen AbcAdaptation.Tripod.Fermat.Proper.NoncriticalElementarySource\nopen AbcAdaptation.Tripod.Fermat.Proper.NoncriticalP1\n\n'+decl+'\n'
  ci.save('solution-source-closure.json',{'method':'Compiler declaration graph exact helper ranges and source scope header; target name substitution only','helpers':helpers,'parent':row,'own_target_imported':False})
 assert 'sorry' not in text
 target='.local/adaptation/fermat-noncritical-elementary-20261114/Solution_'+n+'.lean';(w/target).write_text(text);ci.run('solution-'+n+'-leaf',target)
# Check the complete source helper closure under exact published child statements.
solution=(b/'Solution_noncriticalElementaryCompositionRamification.lean').read_text()
imports=list(dict.fromkeys([line for line in preamble.splitlines() if line.startswith('import ')]+[line for line in solution.splitlines() if line.startswith('import ') and not line.startswith('import Theorems.')]))
body='\n'.join(line for line in solution.splitlines() if not line.startswith('import '))
mirror='\n'.join(imports)+'\n\nsection PublishedChildStatements\nset_option autoImplicit false\nopen Polynomial\nopen scoped IntermediateField\nopen AbcAdaptation\nopen AbcAdaptation.Tripod.Fermat.Proper\n\n'+'\n\n'.join(item['formal_statement'] for item in items)+'\n\nend PublishedChildStatements\n\n'+body+'\n\n#print axioms solution\n'
f='.local/adaptation/fermat-noncritical-elementary-20261114/ValidatePublishedChildContext.lean';(w/f).write_text(mirror);ci.run('published-child-context-leaf',f)
# Verify the three already-published target types against the exact local declarations.
imports='import Lean\n'+'\n'.join('import Theorems.Thm_'+(pre+n).replace('.','_') for n in existing)+'\n\nset_option autoImplicit false\nopen Polynomial\nopen scoped IntermediateField\nopen AbcAdaptation\nopen AbcAdaptation.Tripod.Fermat.Proper\n'
code=imports
for n in existing:
 old=json.loads((b/('platform-before-'+n+'.json')).read_text());formal=old['formal_statement'];prefix='theorem '+pre+n;assert formal.count(prefix)==1;code+='\n'+formal.replace(prefix,'theorem PlatformAudit_'+n,1)+'\n'
code+='\nopen Lean\nrun_meta do\n'
for n in existing:
 code+='  let a ← getConstInfo `'+pre+n+'\n  let p ← getConstInfo `PlatformAudit_'+n+'\n  unless ← Lean.Meta.isDefEq a.type p.type do throwError "Original platform target type differs: '+n+'"\n'
code+='  IO.FS.writeFile ".local/adaptation/fermat-noncritical-elementary-20261114/existing-types-equal.json" "true"\n';f='.local/adaptation/fermat-noncritical-elementary-20261114/ValidateExistingTypes.lean';(w/f).write_text(code);ci.run('existing-types-leaf',f)
ci.run('production-gates-review','.local/adaptation/fermat-noncritical-elementary-20261114/ProductionGates.lean','review',duration='150s',memory='12GiB')
ci.save('upload-validation.json',{'passed':True,'elaborated_types_equal':True,'new_theorem_count':len(new),'additional_leaf_checks':[{'tag':'published-child-context-leaf','source':'.local/adaptation/fermat-noncritical-elementary-20261114/ValidatePublishedChildContext.lean','sorry':True}],'upload_problem_items_sha256':hashlib.sha256((b/'upload-problem-items.json').read_bytes()).hexdigest(),'existing_target_types_definitionally_equal':True,'definition_hashes':{'Definitions/Def_'+n+'.lean':hashlib.sha256((w/('Definitions/Def_'+n+'.lean')).read_bytes()).hexdigest() for n in defs},'source_theorem_hashes':{pre+n:hashlib.sha256((w/('Theorems/Thm_'+(pre+n).replace('.','_')+'.lean')).read_bytes()).hexdigest() for n in existing+new},'source_graph_sha256':hashlib.sha256((b/'decl_graph.jsonl').read_bytes()).hexdigest(),'method':'Prove2Me declaration graph and source spans, elaborated type printing, and Lean.Meta.isDefEq for existing platform targets. No regex declaration splitting.'})
print('Elementary source children, helper closure solution, original target type and production gates validated.',flush=True)
