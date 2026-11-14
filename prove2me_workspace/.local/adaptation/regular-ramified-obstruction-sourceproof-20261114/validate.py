from pathlib import Path
import importlib.util,json,hashlib,shutil,copy
sp=importlib.util.spec_from_file_location('unit','/tmp/p2m-obstruction-ci-20261114.py');unit=importlib.util.module_from_spec(sp);sp.loader.exec_module(unit);ci=unit.ci;w=ci.w;b=ci.b;u='.local/adaptation/regular-ramified-obstruction-sourceproof-20261114/';names=unit.names;dag=unit.dag

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def save(n,x):ci.save(n,x)
def run(*a,**kw):
 kw.setdefault('version','obstruction-validation-v6');return ci.run(*a,**kw)
if __name__=='__main__':
 assert json.loads((b/'source-graph-leaf-result.json').read_text())['status']=='succeeded'
 rows=[json.loads(l) for l in (b/'decl_graph.jsonl').read_text().splitlines() if l];by={r['name']:r for r in rows};files=['Definitions/Def_FermatCurveFieldUniformizer.lean']+[n['file'] for n in dag['nodes']]
 # Parse commands with the built project's parser; declarations and namespace commands have exact byte offsets.
 original=(w/'.local/adaptation/northcott-sourceproof-20261114/ExtractNorthcottSyntax.lean').read_text()
 first=original.index('  let files : Array String := #[');end=original.index('\n  let mut output',first)
 syntax=original[:first]+'  let files : Array String := #['+', '.join(json.dumps(f) for f in files)+']'+original[end:]
 syntax=syntax.replace('  let env ← getEnv','  let env ← getEnv\n  let env := Parser.parserExtension.activateScoped env `IntermediateField\n  let env := Parser.parserExtension.activateScoped env `IntermediateField.algebraAdjoinAdjoin')
 syntax=syntax.replace('import Theorems.Thm_AbcAdaptation_Tripod_boundedDegreeFiniteness','import Theorems.Thm_'+unit.target.replace('.','_')).replace('.local/adaptation/northcott-sourceproof-20261114/syntax-boundaries.json',u+'syntax-boundaries.json')
 needle='    for cmd in syntaxModule[1].getArgs do\n'
 replacement=needle+'      if cmd.isOfKind ``Command.namespace || cmd.isOfKind ``Command.end then\n        output := output.push (Json.mkObj [("file", toJson file), ("kind", toJson cmd.getKind.toString), ("command", toJson (String.Pos.Raw.extract input (cmd.getPos?.getD 0) (cmd.getTailPos?.getD 0))), ("start", posJson ctx.fileMap (cmd.getPos?.getD 0)), ("end", posJson ctx.fileMap (cmd.getTailPos?.getD 0))])\n'
 assert needle in syntax;syntax=syntax.replace(needle,replacement);(b/'ExtractObstructionSyntax.lean').write_text(syntax)
 run('syntax-boundaries-leaf',u+'ExtractObstructionSyntax.lean')
 parsed=json.loads((b/'syntax-boundaries.json').read_text());formals={};solution_rows=[]
 for name in names:
  row=by[name];file=row['module'].replace('.','/')+'.lean';raw=(w/file).read_bytes();short=name.rsplit('.',1)[1];c=[z for z in parsed if z['file']==file and z.get('nameText')==short];assert len(c)==1,(name,c);z=c[0]
  nr=z['nameRange'];a,e=nr['start']['offset'],nr['end']['offset'];assert raw[a:e].decode()==short
  ns=[q for q in parsed if q['file']==file and 'namespace' in q.get('kind','') and q['start']['offset']<z['declStart']['offset']];assert ns;last=ns[-1];namespace=last['command'].split()[1];assert namespace==name.rsplit('.',1)[0]
  es=[q for q in parsed if q['file']==file and q.get('kind','').endswith('.end') and q['start']['offset']>=z['declEnd']['offset']];assert es;ending=es[0];assert ending['command'].strip()=='end '+namespace
  prefix_names=['AbcAdaptation','AbcAdaptation.Tripod','AbcAdaptation.Tripod.Fermat','AbcAdaptation.Tripod.Fermat.Proper','AbcAdaptation.Tripod.Fermat.Proper.CurveDeriv']
  edits=[(a,e,'solution'),(last['start']['offset'],last['end']['offset'],'section\nopen '+' '.join(prefix_names)),(ending['start']['offset'],ending['end']['offset'],'end')]
  data=raw
  for start,stop,value in sorted(edits,reverse=True):data=data[:start]+value.encode()+data[stop:]
  text=data.decode();assert 'sorry' not in text;sol='Solution_'+name.removeprefix('AbcAdaptation.Tripod.Fermat.Proper.').replace('.','_')+'.lean';(b/sol).write_text(text)
  # Query actual module universe parameters through a small kernel script instead of inventing implicit binders.
  levels=row.get('universeParams',[]);assert all(x.replace('_','').isalnum() for x in levels)
  imports=[l for l in (w/file).read_text().splitlines() if l.startswith('import ') and not l.startswith('import Theorems.')]
  preamble='\n'.join(imports)+'\nset_option autoImplicit false\nopen scoped IntermediateField IntermediateField.algebraAdjoinAdjoin\n'+('universe '+' '.join(levels)+'\n' if levels else '')
  context_start=last['end']['offset'];context_end=z['declStart']['offset'];context=raw[context_start:context_end]
  prior=[q for q in parsed if q['file']==file and q.get('nameText') is not None and context_start<=q['declStart']['offset'] and q['declEnd']['offset']<=context_end]
  for q in sorted(prior,key=lambda q:q['declStart']['offset'],reverse=True):
   aa,ee=q['declStart']['offset']-context_start,q['declEnd']['offset']-context_start;context=context[:aa]+context[ee:]
  preamble='\n'.join(imports)+'\nset_option autoImplicit false\nopen Polynomial\nopen scoped IntermediateField\nopen '+' '.join(prefix_names)+'\n'+context.decode()+'\n'
  formal=(raw[z['declStart']['offset']:a]+name.encode()+raw[e:z['valStart']['offset']]).decode().strip()+' := by sorry';formals[name]={'source':file,'preamble':preamble,'formal_statement':formal,'syntax':z,'elaboratedType':row['elaboratedType'],'universeParams':levels,'statement_method':'Exact Lean AST source statement plus retained section-variable and notation context; no pretty-printer coercion reconstruction.'}
  solution_rows.append({'name':name,'source':u+sol,'source_sha256':sha(b/sol),'theorem_imports':['Theorems.Thm_'+v.replace('.','_') for v in next(n for n in dag['nodes'] if n['theorem_name']==name)['direct_node_dependencies']]})
 save('compiler-formals.json',formals);save('solution-inventory.json',solution_rows)
 # Check every constant, including private declarations, generated helpers and their complete transitive axioms.
 mods=['Definitions.Def_FermatCurveFieldUniformizer']+[n['module'] for n in dag['nodes']]
 audit='import Lean\n'+'\n'.join('import '+m for m in mods)+'\nopen Lean\nrun_meta do\n  let mods : Array Name := #['+', '.join('`'+m for m in mods)+']\n  let env ← getEnv\n  let mut out : Array Json := #[]\n  for (name, _) in env.constants.toList do\n    let some idx := env.getModuleIdxFor? name | continue\n    let some m := env.header.moduleNames[idx.toNat]? | continue\n    unless mods.contains m do continue\n    let axs ← collectAxioms name\n    for ax in axs do\n      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do throwError "Unapproved axiom {ax} in {name}"\n    out := out.push (Json.mkObj [("name", toJson name.toString), ("axioms", toJson (axs.map toString))])\n  IO.FS.writeFile "'+u+'all-module-axioms.json" (Json.pretty (Json.arr out))\n';(b/'AuditAllDefinitions.lean').write_text(audit)
 run('all-module-axioms-review',u+'AuditAllDefinitions.lean','review')
 for s in solution_rows:
  short=s['name'].removeprefix('AbcAdaptation.Tripod.Fermat.Proper.').replace('.','_');run('solution-'+short+'-leaf',s['source'])
  # Type comparison lives in an isolated module importing the solution alone; it never supplies a proof.
  inspect='import Lean\n'+'\n'.join('import '+m for m in mods)+'\n\n'+(w/s['source']).read_text()+'\nopen Lean\nrun_meta do\n  let a ← getConstInfo `'+s['name']+'\n  let c ← getConstInfo `solution\n  unless ← Lean.Meta.isDefEq a.type c.type do throwError "Solution type differs"\n'
  # Importing the target would duplicate private helper names? Separate module prefix prevents kernel collisions.
  f='CompareSolution_'+short+'.lean';(b/f).write_text(inspect);run('type-solution-'+short+'-leaf',u+f)
 # Validate compiler-generated platform statement types without adding them to the proof closure.
 checks='import Lean\n'+'\n'.join('import '+m for m in mods)+'\nopen scoped IntermediateField IntermediateField.algebraAdjoinAdjoin\n'
 levels=[]
 for i,name in enumerate(names):
  context='\n'.join(l for l in formals[name]['preamble'].splitlines() if not l.startswith('import '));checks+='\nsection\n'+context+'\n'+formals[name]['formal_statement'].replace('theorem '+name,'theorem PlatformType_'+str(i),1)+'\nend\n'
 before=json.loads((b/'platform-before-target.json').read_text());assert ('theorem '+unit.target) in before['formal_statement'];checks+='\nopen AbcAdaptation AbcAdaptation.Tripod.Fermat.Proper\n'+before['formal_statement'].replace('theorem '+unit.target,'theorem ExistingPlatformType',1)+'\nopen Lean\nrun_meta do\n'
 for i,name in enumerate(names):checks+='  let a ← getConstInfo `'+name+'\n  let c ← getConstInfo `PlatformType_'+str(i)+'\n  unless ← Lean.Meta.isDefEq a.type c.type do throwError "Platform type differs '+name+'\nOriginal: {a.type}\nExported: {c.type}"\n'
 checks+='  let a ← getConstInfo `'+unit.target+'\n  let c ← getConstInfo `ExistingPlatformType\n  unless ← Lean.Meta.isDefEq a.type c.type do throwError "Existing target differs"\n  IO.FS.writeFile "'+u+'existing-types-equal.json" "true"\n';(b/'ValidateExistingTypes.lean').write_text(checks);run('existing-types-leaf',u+'ValidateExistingTypes.lean')
 # Rebuild the existing finiteness consumer after the local obstruction closes.
 name='AbcAdaptation.Tripod.Fermat.Proper.noncriticalRamificationFinite';f='Theorems/Thm_'+name.replace('.','_')+'.lean';run('finite-consumer-leaf',f,memory='6GiB');run('finite-consumer-artifact',f,artifact=True)
 text='import Theorems.Thm_'+name.replace('.','_')+'\n#print axioms '+name+'\n';(b/'ClosedFiniteConsumer.lean').write_text(text);run('finite-consumer-review',u+'ClosedFiniteConsumer.lean','review')
 run('production-gates-review',u+'ProductionGates.lean','review',duration='150s',memory='12GiB')
 checks=[]
 for p in sorted(b.glob('*-request.json')):
  tag=p.name.removesuffix('-request.json');dest=b/(tag+'-result.json')
  if not dest.exists():continue
  q=json.loads(p.read_text());z=json.loads(dest.read_text())
  if z.get('status')!='succeeded' or q.get('workspace')!=str(w):continue
  artifact=q['target']=='module';source=q['parameters']['args'][0] if artifact else q['parameters']['source']
  if not (w/source).is_file() or q['worktree_manifest']['source_sha256']!=sha(w/source):continue
  checks.append({'tag':tag,'source':source,'review':q['task_type']=='review','artifact':artifact})
 save('delivery-validation.json',{'passed':True,'exact_existing_target_type_equal':True,'all_new_formals_type_equal':True,'source_hashes':{f:sha(w/f) for f in files},'solution_hashes':{s['source']:s['source_sha256'] for s in solution_rows},'compiler_checks':checks,'declaration_graph_sha256':sha(b/'decl_graph.jsonl'),'compiler_formals_sha256':sha(b/'compiler-formals.json'),'syntax_boundaries_sha256':sha(b/'syntax-boundaries.json'),'new_open_mathematical_obligations':0})
 print('Obstruction sourceproof, all solution types, axioms and production gates passed.',flush=True)
