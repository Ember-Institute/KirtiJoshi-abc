#!/usr/bin/env python3
"""Static draft audit. No scheduler, compiler, API, network, or Git calls."""
import ast,difflib,hashlib,json,sys
from pathlib import Path
P=Path(__file__).resolve().parent
PREVIOUS=Path('/home/admin-wsl/Coq/abc/prove2me_workspace/.local/adaptation/reference-volume-tate-carriers-20261115')
INVENTORY=Path('/tmp/p2m-tate-theta-inventory-v5-20261115')
sys.dont_write_bytecode=True
sys.path.insert(0,str(P))
from carrier_contract import MODULES,CONTEXT_IMPORTS,load,sha,dependency_evidence,validate_import_graph
from wrap_carriers import name_parts,encode_parts,add_prefix,name_text
checks=[]
def ck(x,s):
 if not x:raise AssertionError(s)
 checks.append(s)
for f in sorted(P.glob('*.py')):ast.parse(f.read_text());checks.append('Python syntax '+f.name)
ck(len(MODULES)==4,'Exactly four source modules')
source=(P/'QueryNextCarrierOriginalExprs.lean').read_text();prior=(PREVIOUS/'QueryNextCarrierOriginalExprs.lean').read_text()
for a,b in [('def cachedAxioms','partial def binderInventory'),('def moduleOf','def standardAxioms')]:
 ck(source[source.index(a):source.index(b)]==prior[prior.index(a):prior.index(b)],'Preserved accepted exporter '+a)
ck('let matches 'not in source and 'let matchingNames 'in source,'Exporter avoids matches keyword')
ck('let actualOwned := sourceEnv.constants.fold'in source and 'matchingNames.size == 1'in source,'Exporter resolves unique actual owned Names')
ck('("nameExpr", encodeName name)'in source,'Exporter emits actual structural Names')
ck('let name ← checked (decodeName (← checked (field entry "nameExpr")))'not in source,'Exporter accepts pending actual Names')
parts=[('str','_private'),('str','TateCurvesTheta'),('num',0),('str','helper')];value=encode_parts(parts)
ck(name_parts(value)==parts and name_parts(add_prefix(value))[-4:]==parts,'Numeric0 Name component survives prefixing')
ck(name_text(value)=='_private.TateCurvesTheta.0.helper','Structural Name display diagnostic')
unit=load(PREVIOUS/'bound-unit-config.json');c=load(PREVIOUS/'accepted-compiler-correspondence.json');typed_path=PREVIOUS/'generated-wrapped/typed-original-source-wrapped-map.json';typed=load(typed_path);workspace=PREVIOUS.parents[2]
unit['dependencies'].append({'status':'accepted-kernel-audit','typedMap':str(typed_path),'typedMapSha256':sha(typed_path),'acceptedConstantNames':[r['original']for r in c['namedPairs']],
 'acceptedCorrespondence':{'unitKind':'volume-tate','path':str(PREVIOUS/'accepted-compiler-correspondence.json'),'sha256':sha(PREVIOUS/'accepted-compiler-correspondence.json')},
 'auditEvidence':[{'kind':'kernel-audit','path':c['audit'],'sha256':c['auditSha256']},{'kind':'ci-result','path':c['receipt'],'sha256':c['receiptSha256']}],
 'modules':[{'originalModule':m['originalModule'],'wrappedModule':m['wrappedModule'],'path':str(workspace/'Definitions'/(m['wrappedModule'].split('.')[-1]+'.lean')),'sha256':sha(workspace/'Definitions'/(m['wrappedModule'].split('.')[-1]+'.lean'))}for m in typed['modules']]})
constants,modules,_=dependency_evidence(unit);ck(len(constants)==339 and len(modules)==15,'Three accepted prior units339 actual names15modules')
closure=load(INVENTORY/'dependency-closure.json');ck(len(closure['requiredPriorActualPairs'])==42,'Required42 actual pairs')
for r in closure['requiredPriorActualPairs']:ck(constants[r['original']]['wrappedName']==r['target'],'Actual required identity '+r['original'])
ck(not closure['requiredPriorProofValueResolutions'],'No prior proof-value resolver required')
rows=load(INVENTORY/'imports.json');plans={}
for row in rows:
 plans[row['module']]={k:list(row[k])for k in ['source435Imports','platform433Candidates']}
 for name in CONTEXT_IMPORTS.get(row['module'],[]):
  for key in ['source435Imports','platform433Candidates']:
   if name not in plans[row['module']][key]:plans[row['module']][key].append(name)
validate_import_graph(plans,modules);checks.append('Precise source/platform import graph and acyclic peer Definitions')
for s in load(INVENTORY/'unit-config.json')['sources']:ck(not s['provenance'].get('sourceOverridden',False),'No source override '+s['module'])
for row in load(P/'reuse-provenance.json')['inputs']:
 ck(sha(row['source'])==row['sourceSha256'],'Accepted reusable input stable '+row['file'])
patches=P/'diffs';patches.mkdir(exist_ok=True)
for row in load(P/'reuse-provenance.json')['inputs']:
 f=P/row['file']
 if f.exists() and f.read_bytes()!=Path(row['source']).read_bytes():
  text=''.join(difflib.unified_diff(Path(row['source']).read_text().splitlines(keepends=True),f.read_text().splitlines(keepends=True),fromfile=row['source'],tofile=str(f)))
  (patches/(f.name+'.patch')).write_text(text)
report={'schema':'tate-theta-tooling-static-validation-v1','status':'passed','checkCount':len(checks),'checks':checks,'compilerExecuted':False,'schedulerCalled':False,'apiOrNetworkCalled':False,'gitExecuted':False,'mainWorkspaceModified':False,'pending':'Actual current parser, Expr and four small-original source acceptance; platform4.33 gates and kernel/axiom audit belong to root MCP-CI.'}
(P/'static-validation.json').write_text(json.dumps(report,ensure_ascii=False,indent=2)+'\n');print(json.dumps({'status':'passed','checkCount':len(checks)}))
