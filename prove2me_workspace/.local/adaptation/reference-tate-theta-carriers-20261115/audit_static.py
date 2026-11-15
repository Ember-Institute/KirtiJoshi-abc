#!/usr/bin/env python3
"""Second pass over frozen inputs; writes only an audit receipt in this directory."""
import hashlib,json
from collections import Counter
from pathlib import Path
P=Path('/tmp/p2m-tate-theta-inventory-v5-20261115')
load=lambda p:json.loads(Path(p).read_text())
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
inventory=load(P/'inventory.json');config=load(P/'parser-config.json');export=load(P/'export-config.json');closure=load(P/'dependency-closure.json')
graph={r['name']:r for r in map(json.loads,Path(inventory['graph']).read_text().splitlines()) if r.get('record')=='decl'}
issues=[];checks=[]
def ck(value,message):
    checks.append(message)
    if not value:issues.append(message)
ck(inventory['graphSha256']==sha(inventory['graph']),'accepted graph SHA256')
ck(export['inventorySha256']==sha(P/'inventory.json'),'export bound to frozen inventory')
selected={r['name'] for m in inventory['modules'] for r in m['declarations'] if r['selected']}
available=set(closure['requiredPriorConstants'])|selected
all_names=set();counts=[];proof_roots=[]
for m,c in zip(inventory['modules'],config['sources']):
    module=m['module'];raw=Path(m['source']).read_bytes();norm=raw.replace(b'\r\n',b'\n')
    ck(hashlib.sha256(raw).hexdigest()==m['sourceSha256']==c['sourceSha256'],module+' source identity')
    ck(hashlib.sha256(norm).hexdigest()==m['normalizedSha256']==c['normalizedSha256'],module+' normalized identity')
    rr=[r for r in graph.values() if r['module']==module]
    ck({r['name'] for r in rr}=={r['name'] for r in m['declarations']}=={r['name'] for r in c['compilerDeclarations']},module+' complete declaration inventory')
    for r,cr in zip(m['declarations'],c['compilerDeclarations']):
        n=r['name'];all_names.add(n)
        ck(r['selected']==r['selectedForBundle']==cr['selected'],n+' consistent selection')
        ck(r['typeDeps']==graph[n]['typeDeps'] and r['valueDeps']==graph[n]['valueDeps'] and r['constructors']==graph[n]['constructors'],n+' exact independent type/value/constructor edges')
        if r['isInstance'] and not r['isInternal']:ck(r['selected'],n+' public instance root retained')
        if not r['selected']:continue
        ck(not r['hasSorryAx'] and set(r['axioms'])<={'propext','Classical.choice','Quot.sound'},n+' accepted graph axiom closure')
        for e in ['typeDeps','valueDeps','constructors']:
            ck(set(r[e])<=available,n+' '+e+' closed under new and audited imported carriers')
        p=r['consumerPathToMainTheorem']
        if p:
            ck(p[0]==n and p[-1]==closure['root'],n+' actual path endpoints')
            ck(all(a in graph[b]['typeDeps']+graph[b]['valueDeps']+graph[b]['constructors'] for a,b in zip(p,p[1:])),n+' actual graph path edges')
        if r['kind']=='theorem' and r['sourceCommandRootCandidate']:
            ck(bool(p),n+' inline proof source root has an actual main-theorem consumer path')
            proof_roots.append(n)
    counts.append({'module':module,'all':len(rr),'selected':sum(r['selected'] for r in m['declarations']),'sourceCommandCandidates':len(m['selectedSourceCommandCandidates']),'publicInstances':sum(r['isInstance'] and not r['isInternal'] for r in rr)})
ck(all_names=={r['name'] for r in export['records']},'export exact declaration set')
ck(len(all_names)==export['expectedRecordCount'],'export configurable total count')
ck(len(selected)==export['expectedSelectedCount'],'export configurable selected count')
ck(not closure['missingPriorAvailableConstants'],'required prior constants all present in accepted kernel audit')
ck(len(closure['requiredPriorActualPairs'])==len(closure['requiredPriorConstants']),'every prior requirement has accepted actual identity')
ck(all(x['target'] for x in closure['requiredPriorActualPairs']),'no candidate-only prior identities')
ck(not closure['requiredPriorProofValueResolutions'],'no unused proof-value resolver dependencies')
ck(not closure['selectedNoOwner'],'every selected declaration has an owner candidate')
for b in closure['importedBundles']:ck(sha(b['file'])==b['sha256'],b['module']+' installed imported bundle identity')
out={'schema':'next-carrier-static-audit-v1','status':'passed' if not issues else 'failed','issues':issues,'checkCount':len(checks),'modules':counts,'inlineProofSourceRoots':proof_roots,'sourceCommandSelectionLimit':'Compiler range/prefix candidates are not accepted AST source command spans. Main MCP-CI parser then small-source oracle must establish exact command emission and auxiliary identity.','compilationPerformed':False,'mainWorkspaceModified':False,'inputHashes':{f:sha(P/f) for f in ['inventory.json','parser-config.json','export-config.json','unit-config.json','imports.json','dependency-closure.json','QueryNextCarrierParserRanges.lean']}}
(P/'static-audit.json').write_text(json.dumps(out,ensure_ascii=False,indent=2)+'\n')
print(json.dumps({'status':out['status'],'issues':issues,'checkCount':len(checks),'modules':counts},ensure_ascii=False))
assert not issues
