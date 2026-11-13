from pathlib import Path
import ast,json,socket,hashlib,copy,subprocess,sys
w=Path('/home/admin-wsl/Coq/abc/prove2me_workspace');b=w/'.local/adaptation/fermat-proper-canonical-20261113';base=json.loads((b/'base-request.json').read_text());base['session_id']='p2m-fermat-proper-upload-types-20261113'
def save(n,x):(b/n).write_text(json.dumps(x,ensure_ascii=False,indent=2)+'\n')
source=Path('/tmp/p2m-proper-canonical-ci-main-20261113.py').read_text().replace("tag.startswith('renamed-')", "(tag=='graph-leaf' or tag.startswith('renamed-'))")
for node in ast.parse(source).body:
 if isinstance(node,ast.FunctionDef) and node.name in ['rpc','wait','run']:exec(compile(ast.Module(body=[node],type_ignores=[]),'<main-ci-protocol>','exec'),globals())
# This run is sequentially invoked only after the source/child/solution checks reach terminal success.
for tag in ['closed-compositions-review','canonical-solution-leaf','canonical-solution-artifact','canonical-reduction-axioms']:
 x=json.loads((b/(tag+'-result.json')).read_text());assert x['status']=='succeeded',tag
helper='.local/adaptation/fermat-proper-canonical-20261113/ExtractCanonicalGraph.lean';base['worktree_manifest']['input_hashes'][helper]=hashlib.sha256((w/helper).read_bytes()).hexdigest();run('graph-leaf',helper)
rows=[json.loads(line) for line in (b/'decl_graph.jsonl').read_text().splitlines() if line.strip()];byname={x['name']:x for x in rows}
pre='AbcAdaptation.Tripod.Fermat.Proper.'
names=[pre+n for n in ['modelExists','placesDiscrete','residuesFinite','affineIdentification','noncriticalSelection','cuspsFinite','polarPresentationExists','canonicalDivisorExists','infinityDivisorExists','planeAdjunctionExists','cuspGeneratorsExists','canonicalDivisorDegree','localCompactness','avoidanceRegularity','embeddingBoundsToSet','canonicalHeightIdentification','belyiHeightRelation','divisorDegreeHeightComparison','belyiDifferentConductorComparison','cuspConductorHeightComparison']]
defmods=['FermatProperCarrier','FermatProperComposition','FermatProperDivisorHeight','FermatProperDivisorComposition','FermatLocalBelyi','FermatLocalBelyiComposition','FermatBelyiComparisons','FermatCanonicalBelyiComposition']
preamble='\n'.join('import Definitions.Def_'+n for n in defmods)+'\n\nset_option autoImplicit false'
items=[]
for name in names:
 row=byname[name];assert row['kind']=='theorem' and row['startLine']>0,(name,row)
 assert row['module']=='Theorems.Thm_'+name.replace('.','_'),row
 items.append({'theorem_name':name,'preamble':preamble,'formal_statement':'theorem '+name+' : '+row['elaboratedType']+' := by sorry'})
save('upload-problem-items.json',items)
body=preamble+'\n\n'+'\n\n'.join(x['formal_statement'] for x in items)+'\n\nset_option pp.fullNames true\nopen Lean\nrun_meta do\n  let mut rows : Array Json := #[]\n'
for name in names:
 body+='  let info ← getConstInfo `'+name+'\n  let fmt ← Lean.Meta.ppExpr info.type\n  rows := rows.push (Json.mkObj [("name", Json.str "'+name+'"), ("type", Json.str fmt.pretty)])\n'
body+='  IO.FS.writeFile ".local/adaptation/fermat-proper-canonical-20261113/upload-elaborated-types.json" (Json.pretty (Json.arr rows))\n'
f='.local/adaptation/fermat-proper-canonical-20261113/UploadStatements.lean';(w/f).write_text(body);base['worktree_manifest']['input_hashes'][f]=hashlib.sha256((w/f).read_bytes()).hexdigest();run('upload-statement-types-leaf',f)
staged={x['name']:x['type'] for x in json.loads((b/'upload-elaborated-types.json').read_text())};assert set(staged)==set(names)
differences={n:{'source':byname[n]['elaboratedType'],'upload':staged[n]} for n in names if byname[n]['elaboratedType']!=staged[n]};save('upload-type-differences.json',differences);assert not differences,differences
save('upload-validation.json',{'passed':True,'elaborated_types_equal':True,'theorem_count':len(names),'source':'Platform scripts/extract_decl_graph.lean adapted for these compiled modules, plus elaborated type printing; no regex-based declaration extraction.','source_graph_sha256':hashlib.sha256((b/'decl_graph.jsonl').read_bytes()).hexdigest(),'staged_source_sha256':hashlib.sha256((w/f).read_bytes()).hexdigest(),'definition_hashes':{'Definitions/Def_'+n+'.lean':hashlib.sha256((w/('Definitions/Def_'+n+'.lean')).read_bytes()).hexdigest() for n in defmods},'items_sha256':hashlib.sha256((b/'upload-problem-items.json').read_bytes()).hexdigest(),'theorem_source_hashes':{n:hashlib.sha256((w/('Theorems/Thm_'+n.replace('.','_')+'.lean')).read_bytes()).hexdigest() for n in names}})
print('All 20 exact upload statements compiled and elaborated types match their source declarations.',flush=True)
