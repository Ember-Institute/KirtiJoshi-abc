#!/usr/bin/env python3
import json, hashlib, pathlib, subprocess, difflib
B=pathlib.Path('/home/admin-wsl/Coq/abc/prove2me_workspace/.local/adaptation/reference-volume-tate-carriers-20261115')
O=pathlib.Path(__file__).parent
sha=lambda p:hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()
read=lambda p:json.loads(pathlib.Path(p).read_text())
inv=read(B/'inventory.json'); small=read(B/'generated/foundation-small-source-report.json'); orig=read(B/'original-exprs.json'); dep=read(B/'dependency-closure.json')
errors=[]; checked=[]
def check(ok,msg):
 if not ok:errors.append(msg)
rows={r['name']:r for r in orig['records']}
graph={}
for line in pathlib.Path(inv['graph']).open():
 r=json.loads(line)
 if r.get('record')=='decl':graph[r['name']]=r
check(sha(inv['graph'])==inv['graphSha256'],'graph hash')
modules=[]; edge_count=0
for m,s in zip(inv['modules'],small['modules']):
 name=m['module']; check(name==s['module'],'module order '+name)
 selected=[d for d in m['declarations'] if d['selected']]
 check({d['name'] for d in selected}==set(s['selectedCompilerDeclarations']),'selected declarations '+name)
 p=m['provenance']; effective=pathlib.Path(p['frozenEffectiveSource']['path']); check(sha(effective)==p['sourceSha256'],'effective bytes '+name)
 check(sha(s['originalCoordinateSource'])==s['normalizedSha256'],'normalized source '+name)
 source=pathlib.Path(s['source']); check(sha(source)==s['sourceSha256'],'small bytes '+name)
 raw=pathlib.Path(s['originalCoordinateSource']).read_bytes(); out=source.read_bytes(); cmds=0
 for c in s['retainedCommands']:
  a,z=c['originalRange']['start']['offset'],c['originalRange']['end']['offset']; x,y=c['outputRange']['start']['offset'],c['outputRange']['end']['offset']
  check(hashlib.sha256(raw[a:z]).hexdigest()==c['sha256'],'original command hash '+name+':'+str(c['commandIndex']))
  check(raw[a:z]==out[x:y],'retained whole command equality '+name+':'+str(c['commandIndex']))
  if c['role']=='selected-declaration':cmds+=1
 gitblob=subprocess.check_output(['git','-C',p['actualGitRepository'],'show',p['originalCommit']+':'+p['originalSourcePath']])
 check(hashlib.sha256(gitblob).hexdigest()==p['upstreamSourceSha256'],'exact Git blob '+name)
 if not p['sourceOverridden']:check(gitblob==effective.read_bytes(),'unchanged upstream '+name)
 else:
  patch=p['effectiveSourceOverride']; check(name=='Iut.Cor312.LogVolume','unexpected override')
  # Keep the full effective/upstream byte identities, never identify effective bytes with the linked Git blob.
  check(not p['sourceGitBlobMatches'],'override Git equality false')
 for d in selected:
  r=rows[d['name']];check(r['selected'] and r['sourceSha256']==p['sourceSha256'],'compiler source binding '+d['name'])
  check(not d['hasSorryAx'] and set(r['axioms'])<= {'propext','Classical.choice','Quot.sound'},'original axioms '+d['name'])
  check(d['typeDeps']==graph[d['name']]['typeDeps'] and d['valueDeps']==graph[d['name']]['valueDeps'],'graph declaration '+d['name'])
  for c in d['actualConsumers']:
   edge_count+=1; check(d['name'] in graph[c['consumer']].get(c['edge'],[]),'consumer edge '+d['name']+' -> '+c['consumer'])
  path=d['consumerPathToMainTheorem'] or []
  if path:check(path[0]==d['name'] and path[-1]=='Iut.Theorem110Invariants.theorem110','path endpoints '+d['name'])
  for a,z in zip(path,path[1:]):check(a in sum([graph[z].get(e,[]) for e in ['typeDeps','valueDeps','constructors']],[]),'path edge '+a+' -> '+z)
 structures={d['name']:rows[d['name']]['structure']['fieldsInConstructorOrder'] for d in selected if rows[d['name']].get('structure')}
 modules.append({'module':name,'originalCount':len(m['declarations']),'selectedCount':len(selected),'selectedCommandCount':cmds,'withOriginalConsumers':sum(bool(d['actualConsumers']) for d in selected),'withOriginalTheorem110Path':sum(bool(d['consumerPathToMainTheorem']) for d in selected),'fullStructureFields':structures,'effectiveSha256':p['sourceSha256'],'upstreamSha256':p['upstreamSourceSha256'],'sourceGitBlobMatches':p['sourceGitBlobMatches']})
# Resolve prior identities from accepted comparison outputs, not candidate wrapper maps.
f=read(B.parent/'foundation-reference-carriers-20261115/kernel-audit/foundation-kernel-audit.json')
p=read(B.parent/'reference-packet-field-carriers-20261115/kernel-audit/next-carrier-kernel-audit.json')
c=read(B.parent/'reference-packet-field-carriers-20261115/accepted-compiler-correspondence.json')
actual={(r['original'],r['target']):r for a in [f,p] for r in a['comparisons']}
required=dep['requiredPriorActualPairs']; counts={'foundation':0,'packetField':0}
fset={(r['original'],r['target']) for r in f['comparisons']}
for r in required:
 k=(r['original'],r['target']);check(k in actual,'prior actual comparison '+r['original'])
 if k in actual:
  a=actual[k];check(a['kernelTypeEqual'] and (a['proofDeclaration'] or a['sourceRecord'].get('valueExpr') is None or a['kernelValueEqual'] or a.get('kernelPropositionalValueEquality',False)),'prior equality '+r['original'])
  counts['foundation' if k in fset else 'packetField']+=1
check(len(required)==62,'62 prior identities');check(not dep['requiredPriorProofValueResolutions'],'no proof-value substitutions required')
check(c['status']=='accepted-kernel-audit','accepted packet correspondence')
for r in c['namedPairs']:check((r['original'],r['target']) in actual,'accepted pair actual '+r['original'])
for x in ['parser','original-exprs','runtime-driver']:
 a=read(B/(x+'-acceptance.json'));check(a['status']=='accepted','acceptance '+x)
# Freeze only evidence used in this stage; later gates get a new report.
inputs=['inventory.json','dependency-closure.json','source-provenance-audit.json','source-command-selection.json','paper-context.json','NORMALIZEDORDER-IMPORTS.md','normalizedorder-import-visibility.json','precise-import-review.json','generated/foundation-small-source-report.json','original-exprs.json','parser-acceptance.json','original-exprs-acceptance.json','runtime-driver-acceptance.json']
report={'schema':'volume-tate-independent-source-review-stage1-v1','status':'source-reviewed-target-gates-pending' if not errors else 'source-review-blocked','compilerOrNetworkInvocations':0,'mainWorkspaceWrites':0,'concreteBlockers':errors,'modules':modules,'originalConsumerEdgesVerified':edge_count,'priorActualNamedIdentityCount':len(required),'priorIdentityOrigins':counts,'scope':{'rootGraphMembership':False,'canonicalC22Connected':False,'paperIdentityAndArithmeticInstantiationCompleted':False},'openMathematicalIdentity':'Paper III p94 inverse-extension-degree weight differs from intended direct normalized degree in the source header. Actual fields only supply positive weights summing to one; no arithmetic identification is proved. This does not block faithful definition preparation.','pendingAcceptance':['five small runtime InfoTree and exact auxiliary emission oracles','final wrapper platform leaves','cross-version target kernel comparison and all owned axiom closures','production checks/axioms, import audit, Act1Scene1, AxiomAudit and git diff --check','independent final readback review'],'inputFiles':[{'path':str(B/x),'sha256':sha(B/x)} for x in inputs]}
(O/'stage1-source-review.json').write_text(json.dumps(report,ensure_ascii=False,indent=2)+'\n')
print(json.dumps({k:v for k,v in report.items() if k in ['status','concreteBlockers','originalConsumerEdgesVerified','priorActualNamedIdentityCount','priorIdentityOrigins']},ensure_ascii=False))
