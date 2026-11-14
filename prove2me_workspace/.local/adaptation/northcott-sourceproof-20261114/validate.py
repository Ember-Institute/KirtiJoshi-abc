from pathlib import Path
import importlib.util,json,hashlib,shutil
s=importlib.util.spec_from_file_location('unit','/tmp/p2m-northcott-ci-20261114.py');unit=importlib.util.module_from_spec(s);s.loader.exec_module(unit);ci=unit.ci;w=ci.w;b=ci.b;urel='.local/adaptation/northcott-sourceproof-20261114/';pre=unit.pre;names=unit.new_names+['boundedDegreeFiniteness']
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def run(*a,**kw):
 kw.setdefault('version','northcott-validation-v1');return ci.run(*a,**kw)
assert json.loads((b/'ascii-source-graph-leaf-result.json').read_text())['status']=='succeeded'
rows=[json.loads(l) for l in (b/'decl_graph.jsonl').read_text().splitlines() if l];by={r['name']:r for r in rows}
mods=['Definitions.Def_TripodNorthcottInputs','Definitions.Def_TripodNorthcottComposition']+['Theorems.Thm_'+(pre+n).replace('.','_') for n in names]
syntax=r'''import Lean
import Theorems.Thm_AbcAdaptation_Tripod_boundedDegreeFiniteness
open Lean Elab Parser
partial def findKind? (stx : Syntax) (k : SyntaxNodeKind) : Option Syntax :=
  if stx.getKind == k then some stx else stx.getArgs.findSome? (findKind? · k)
def posJson (fm : FileMap) (p : String.Pos.Raw) : Json :=
  let pos := fm.toPosition p
  Json.mkObj [("line", toJson pos.line), ("col", toJson pos.column), ("offset", toJson p.byteIdx)]
def rangeJson (fm : FileMap) (stx? : Option Syntax) : Json :=
  match stx?.bind fun s => do pure (← s.getPos?, ← s.getTailPos?) with
  | some (s, e) => Json.mkObj [("start", posJson fm s), ("end", posJson fm e)]
  | none => Json.null
run_meta do
  let env ← getEnv
  let files : Array String := #[FILES]
  let mut output : Array Json := #[]
  for file in files do
    let input ← IO.FS.readFile file
    let ctx := Parser.mkInputContext input file
    let syntaxModule ← Parser.testParseModule env file input
    for cmd in syntaxModule[1].getArgs do
      let some decl := findKind? cmd ``Command.declaration | continue
      let some declId := findKind? decl ``Command.declId | continue
      let valStx := (findKind? decl ``Command.declValSimple).orElse fun _ =>
        findKind? decl ``Command.declValEqns
      let some ds := decl.getPos? | continue
      let some de := decl.getTailPos? | continue
      output := output.push (Json.mkObj [
        ("file", toJson file), ("nameText", toJson declId[0].getId.toString),
        ("declStart", posJson ctx.fileMap ds), ("declEnd", posJson ctx.fileMap de),
        ("nameRange", rangeJson ctx.fileMap (some declId[0])),
        ("valStart", (valStx.bind (·.getPos?)).map (posJson ctx.fileMap ·) |>.getD Json.null),
        ("docstring", rangeJson ctx.fileMap (findKind? cmd ``Command.docComment))])
  IO.FS.writeFile "OUTPUT" (Json.pretty (Json.arr output))
'''
files=[m.replace('.','/')+'.lean' for m in mods]
syntax=syntax.replace('FILES',', '.join(json.dumps(f,ensure_ascii=False) for f in files)).replace('OUTPUT',urel+'syntax-boundaries.json');(b/'ExtractNorthcottSyntax.lean').write_text(syntax)
audit='import Lean\n'+'\n'.join('import '+m for m in mods)+'\nopen Lean\nrun_meta do\n  let mods : Array Name := #['+', '.join('`'+m for m in mods)+']\n  let env ← getEnv\n  let mut out : Array Json := #[]\n  for (name, _) in env.constants.toList do\n    let some idx := env.getModuleIdxFor? name | continue\n    let some m := env.header.moduleNames[idx.toNat]? | continue\n    unless mods.contains m do continue\n    let axs ← collectAxioms name\n    for ax in axs do\n      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do throwError "Unapproved axiom {ax} in {name}"\n    out := out.push (Json.mkObj [("name", toJson name.toString), ("axioms", toJson (axs.map toString))])\n  IO.FS.writeFile "'+urel+'all-module-axioms.json" (Json.pretty (Json.arr out))\n';(b/'AuditAllDefinitions.lean').write_text(audit)
run('syntax-boundaries-leaf',urel+'ExtractNorthcottSyntax.lean')
syntax_rows=json.loads((b/'syntax-boundaries.json').read_text());generated=[];payload_formals={}
for n in names:
 fq=pre+n;row=by[fq];source=row['module'].replace('.','/')+'.lean';raw=(w/source).read_bytes()
 candidates=[z for z in syntax_rows if z['file']==source and z['nameText'] in [n.rsplit('.',1)[-1],fq]];assert len(candidates)==1,(n,candidates);z=candidates[0]
 start=z['declStart']['offset'];end=z['declEnd']['offset'];v=z['valStart']['offset'];nr=z['nameRange'];a=nr['start']['offset'];e=nr['end']['offset']
 assert raw[a:e].decode()==z['nameText'];assert start<=a<e<=v<=end
 imports=[l for l in (w/source).read_text().splitlines() if l.startswith('import ')]
 common='\n'.join(imports)+'\n\nset_option autoImplicit false\nopen NumberField Polynomial\nopen scoped Classical\nopen AbcAdaptation\nopen AbcAdaptation.Tripod\nopen AbcAdaptation.Tripod.Northcott\n\n'
 sol=(raw[start:a]+b'solution'+raw[e:end]).decode();sol=common+sol+'\n';assert 'sorry' not in sol;f='Solution_'+n.replace('.','_')+'.lean';(b/f).write_text(sol);generated.append(f)
 # Remove only the exact compiler parser's doc-comment range from the formal statement.
 formal=raw[start:a]+fq.encode()+raw[e:v]
 doc=z['docstring']
 if doc:
  ds,de=doc['start']['offset'],doc['end']['offset'];assert start<=ds<de<=a;formal=formal[:ds-start]+formal[de-start:]
 formal=formal.decode().strip()+' := by sorry';pure_preamble='\n'.join(l for l in common.splitlines() if not l.startswith('import Theorems.'))+'\n';payload_formals[fq]={'formal_statement':formal,'preamble':pure_preamble,'source':source,'syntax':z}
(b/'compiler-formals.json').write_text(json.dumps(payload_formals,ensure_ascii=False,indent=2)+'\n')
# Platform-node formals must import only Definitions/Mathlib. Remove mathematical proof-only imports.
formals='import Lean\n'+'\n'.join('import '+m for m in mods)+'\nset_option autoImplicit false\nopen NumberField Polynomial\nopen scoped Classical\nopen AbcAdaptation\nopen AbcAdaptation.Tripod\nopen AbcAdaptation.Tripod.Northcott\n'
for i,n in enumerate(names):
 fq=pre+n;f=payload_formals[fq]['formal_statement'];assert ('theorem '+fq) in f
 formals+='\nsection\n'+f.replace('theorem '+fq,'theorem CompilerTarget_'+str(i),1)+'\nend\n'
parent=json.loads((b/'platform-before-boundedDegreeFiniteness.json').read_text());marker='theorem '+pre+'boundedDegreeFiniteness';assert parent['formal_statement'].count(marker)==1
formals+='\n'+parent['formal_statement'].replace(marker,'theorem PublishedExistingParent',1)+'\nopen Lean\nrun_meta do\n'
for i,n in enumerate(names):
 formals+='  let a ← getConstInfo `'+pre+n+'\n  let c ← getConstInfo `CompilerTarget_'+str(i)+'\n  unless ← Lean.Meta.isDefEq a.type c.type do throwError "Compiler formal differs '+n+'"\n'
formals+='  let p ← getConstInfo `'+pre+'boundedDegreeFiniteness\n  let q ← getConstInfo `PublishedExistingParent\n  unless ← Lean.Meta.isDefEq p.type q.type do throwError "Published parent differs"\n  IO.FS.writeFile "'+urel+'existing-types-equal.json" "true"\n';(b/'ValidateExistingTypes.lean').write_text(formals)
# Bind the independent readbacks to actual compiler owners and spans; preserve the original blind data.
blind_path=Path('/tmp/p2m-northcott-blind-20261114/readbacks.json');shutil.copy2(blind_path,b/'blind-readbacks-original.json')
rb=json.loads(Path('/tmp/p2m-northcott-delivery-next-20261114/final-readbacks-draft.json').read_text());quote=Path('/tmp/p2m-northcott-delivery-next-20261114/mochizuki-quotation.md').read_text().strip();inputs={}
mapping=json.loads((b/'ascii-renaming.json').read_text())['mapping']
for rr in rb['declarations']:
 original=rr['declaration'];rr['declaration']=mapping.get(original,original);rr['original_declaration']=original
 gr=by[rr['declaration']];rel=gr['module'].replace('.','/')+'.lean';inputs[rel]=sha(w/rel);rr['path']=rel;rr['source_file_sha256']=inputs[rel];rr['compiler_name']=gr['name'];rr['compiler_source_span']={'startLine':gr['startLine'],'endLine':gr['endLine']};rr['elaboratedType']=gr['elaboratedType'];rr['en_source_quote']=quote;rr['en_source_quote_ledger_binding']={'file':'mochizuki-quotation.md','sha256':sha(b/'mochizuki-quotation.md'),'quote_id':'N1','scope':'Direct general finiteness context; no claim of paper metric identity or numbered polynomial implementation helpers.'}
formulas=json.loads(Path('/tmp/p2m-northcott-display-formulas-20261114.json').read_text())
for rr in rb['declarations']:
 f=formulas[rr['declaration'].rsplit('.',1)[1]];rr['main_formula']=f
 for lang in ['en','zh_Hans','ja']:rr[lang]+='\n\n$$\n'+f+'\n$$'
rb['input_file_sha256']=inputs;rb['compiler_bound']=True;(b/'final-readbacks.json').write_text(json.dumps(rb,ensure_ascii=False,indent=2)+'\n')
run('all-module-axioms-review',urel+'AuditAllDefinitions.lean','review')
for f in generated:run('solution-'+f.removeprefix('Solution_').removesuffix('.lean')+'-leaf',urel+f)
run('existing-types-leaf',urel+'ValidateExistingTypes.lean')
run('production-gates-review',urel+'ProductionGates.lean','review',duration='150s',memory='12GiB')
checks=[];latest={}
for p in sorted(b.glob('*-request.json')):
 tag=p.name.removesuffix('-request.json');dest=b/(tag+'-result.json')
 if not dest.exists():continue
 q=json.loads(p.read_text());rr=json.loads(dest.read_text())
 if rr.get('status')!='succeeded' or q.get('workspace')!=str(w):continue

 if tag.startswith('rename-'):continue
 artifact=q['target']=='module';source=q['parameters']['args'][0] if artifact else q['parameters']['source']
 path=w/source
 if not path.exists() or q['worktree_manifest']['source_sha256']!=sha(path):continue
 key=(source,q['task_type'],artifact);stamp=rr.get('finished_at',0)
 if key not in latest or stamp>latest[key][0]:latest[key]=(stamp,{'tag':tag,'source':source,'review':q['task_type']=='review','artifact':artifact})
checks=[v[1] for v in latest.values()]
source_hashes={f:sha(w/f) for f in files};solutions={urel+f:sha(b/f) for f in generated}
ci.save('delivery-validation.json',{'passed':True,'exact_existing_target_type_equal':True,'all_new_formals_type_equal':True,'readbacks_compiler_bound':True,'new_open_mathematical_obligations':0,'source_hashes':source_hashes,'solution_hashes':solutions,'compiler_checks':checks,'declaration_graph_sha256':sha(b/'decl_graph.jsonl'),'compiler_formals_sha256':sha(b/'compiler-formals.json'),'readbacks_sha256':sha(b/'final-readbacks.json'),'syntax_boundaries_sha256':sha(b/'syntax-boundaries.json')})
print('Northcott sourceproof compiler validation passed.',flush=True)
