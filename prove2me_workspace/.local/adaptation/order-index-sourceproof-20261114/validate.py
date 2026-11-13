from pathlib import Path
import json,hashlib,importlib.util
s=importlib.util.spec_from_file_location('unit','/tmp/p2m-order-proof-ci-20261114.py');unit=importlib.util.module_from_spec(s);s.loader.exec_module(unit);ci=unit.ci;w=ci.w;b=ci.b
pre='AbcAdaptation.Tripod.Fermat.Proper.';names=unit.names;urel='.local/adaptation/order-index-sourceproof-20261114/'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def run(*a,**kw):
 kw.setdefault('version','order-validation-v1');return ci.run(*a,**kw)
assert json.loads((b/'source-graph-leaf-result.json').read_text())['status']=='succeeded'
rows=[json.loads(l) for l in (b/'decl_graph.jsonl').read_text().splitlines() if l];by={x['name']:x for x in rows}
mods=['Definitions.Def_FermatNoncriticalOrderSource']+['Theorems.Thm_'+(pre+n).replace('.','_') for n in names]
audit='import Lean\n'+'\n'.join('import '+m for m in mods)+'\nopen Lean\nrun_meta do\n  let mods : Array Name := #['+', '.join('`'+m for m in mods)+']\n  let env ← getEnv\n  let mut out : Array Json := #[]\n  for (name, _) in env.constants.toList do\n    let some idx := env.getModuleIdxFor? name | continue\n    let some m := env.header.moduleNames[idx.toNat]? | continue\n    unless mods.contains m do continue\n    let axs ← collectAxioms name\n    for ax in axs do\n      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do throwError "Unapproved axiom {ax} in {name}"\n    out := out.push (Json.mkObj [("name", toJson name.toString), ("axioms", toJson (axs.map toString))])\n  IO.FS.writeFile "'+urel+'all-definition-axioms.json" (Json.pretty (Json.arr out))\n'
(b/'AuditAllDefinitions.lean').write_text(audit)
for n in names:
 row=by[pre+n];lines=(w/(row['module'].replace('.','/')+'.lean')).read_text().splitlines()
 visited=set();todo=[pre+n];same=[]
 while todo:
  x=todo.pop()
  if x in visited:continue
  visited.add(x);z=by.get(x)
  if not z or z['module']!=row['module']:continue
  todo+=z['typeDeps']+z['valueDeps']
  if x!=pre+n and z['startLine']>0:same.append(z)
 same.sort(key=lambda z:z['startLine']);blocks=[]
 for z in same+[row]:
  text='\n'.join(lines[z['startLine']-1:z['endLine']])
  if z['name']==pre+n:
   assert text.count('theorem '+n)==1;text=text.replace('theorem '+n,'theorem solution',1)
  blocks.append(text)
 imports=[l for l in lines if l.startswith('import ')]
 text='\n'.join(imports)+'\n\nset_option autoImplicit false\nopen AbcAdaptation\nopen Polynomial\nopen AbcAdaptation.Tripod.Fermat.Proper\n\n'+'\n\n'.join(blocks)+'\n'
 assert 'sorry' not in text and ('import Theorems.Thm_'+(pre+n).replace('.','_')) not in text
 (b/('Solution_'+n+'.lean')).write_text(text)
 (b/('helper-closure-'+n+'.json')).write_text(json.dumps(same,ensure_ascii=False,indent=2)+'\n')
typecheck='import Lean\n'+'\n'.join('import '+m for m in mods[1:])+'\nset_option autoImplicit false\nopen AbcAdaptation\nopen AbcAdaptation.Tripod.Fermat.Proper\n'
for n in names:
 old=json.loads((b/('platform-before-'+n+'.json')).read_text());formal=old['formal_statement'];marker='theorem '+pre+n;assert formal.count(marker)==1
 typecheck+='\nsection\n'+old.get('preamble','').replace('import ','-- imported above: ')+'\n'+formal.replace(marker,'theorem PlatformTarget_'+n,1)+'\nend\n'
typecheck+='\nopen Lean\nrun_meta do\n'
for n in names:
 typecheck+='  let a ← getConstInfo `'+pre+n+'\n  let b ← getConstInfo `PlatformTarget_'+n+'\n  unless ← Lean.Meta.isDefEq a.type b.type do throwError "Platform target differs: '+n+'"\n'
typecheck+='  IO.FS.writeFile "'+urel+'existing-types-equal.json" "true"\n';(b/'ValidateExistingTypes.lean').write_text(typecheck)
# Rebuild the concrete downstream consumers to remove cached transitive sorry dependencies.
consumers=['noncriticalElementaryCompositionRamification','noncriticalCompositionRamification']
consumercheck='\n'.join('import Theorems.Thm_'+(pre+n).replace('.','_') for n in consumers)+'\nopen AbcAdaptation.Tripod.Fermat.Proper\n'+'\n'.join('#print axioms '+n for n in consumers)+'\n'
(b/'CheckClosedConsumers.lean').write_text(consumercheck)
run('all-definitions-axioms-review',urel+'AuditAllDefinitions.lean','review')
for n in names:run('solution-'+n+'-leaf',urel+'Solution_'+n+'.lean')
run('existing-types-leaf',urel+'ValidateExistingTypes.lean')
for n in consumers:
 f='Theorems/Thm_'+(pre+n).replace('.','_')+'.lean';run(n+'-consumer-leaf',f,memory='6GiB');run(n+'-consumer-artifact',f,artifact=True)
run('closed-consumers-review',urel+'CheckClosedConsumers.lean','review')
run('production-gates-review',urel+'ProductionGates.lean','review',duration='150s',memory='12GiB')
checks=[]
for p in sorted(b.glob('*-request.json')):
 tag=p.name.removesuffix('-request.json');z=b/(tag+'-result.json')
 if not z.exists():continue
 q=json.loads(p.read_text());z=json.loads(z.read_text())
 if z.get('status')!='succeeded':continue
 artifact=q['target']=='module';source=q['parameters']['args'][0] if artifact else q['parameters']['source']
 checks.append({'tag':tag,'source':source,'review':q['task_type']=='review','artifact':artifact})
ci.save('sourceproof-validation.json',{'passed':True,'exact_platform_types_equal':True,'definition_hashes':{'Definitions/Def_FermatNoncriticalOrderSource.lean':sha(w/'Definitions/Def_FermatNoncriticalOrderSource.lean')},'theorem_hashes':{pre+n:sha(w/('Theorems/Thm_'+(pre+n).replace('.','_')+'.lean')) for n in names},'solution_hashes':{urel+'Solution_'+n+'.lean':sha(b/('Solution_'+n+'.lean')) for n in names},'declaration_graph_sha256':sha(b/'decl_graph.jsonl'),'compiler_checks':checks,'method':'Compiler declaration graph and exact source spans, private helper proof closure, actual platform types checked by Lean.Meta.isDefEq; all new module constants and concrete downstream consumers checked against standard axioms.'})
print('Order/index sourceproof validation passed.',flush=True)
