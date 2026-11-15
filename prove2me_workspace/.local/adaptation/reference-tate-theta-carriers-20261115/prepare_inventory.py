#!/usr/bin/env python3
"""Independent graph/source inventory. No Lean, CI, API, or Git mutation."""
import hashlib,json,subprocess
from collections import Counter,defaultdict,deque
from pathlib import Path
TASK=Path('/tmp/p2m-tate-theta-inventory-v5-20261115')
BASE=Path('/home/admin-wsl/Coq/abc'); WORK=BASE/'prove2me_workspace'
REF=WORK/'.local/adaptation/reference-extraction-20261115'
PRIOR=WORK/'.local/adaptation/foundation-reference-carriers-20261115'
PACKET=WORK/'.local/adaptation/reference-packet-field-carriers-20261115'
VOLUME=WORK/'.local/adaptation/reference-volume-tate-carriers-20261115'
B=WORK/'.local/adaptation/reference-tate-theta-carriers-20261115'
GRAPH=REF/'c22-decl-graph.jsonl'
ORDER=['TateCurvesTheta.TateCurve.JInvariant','TateCurvesTheta.TateCurve.Parametrization','Iut.Cor312.ThetaData.AdmissiblePrime','Iut.Cor312.ThetaData.TateStructure']
ROOT='Iut.Theorem110Invariants.theorem110'
OLDIUT=Path('/home/admin-wsl/Coq/abc.old/refer/iut'); TATE=OLDIUT/'.lake/packages/tate-curves-theta'
IUTCOMMIT='07cb1da58f6d428a670dbb5dd6093d428bcbcdd8'
def sha(x):return hashlib.sha256(x if isinstance(x,bytes) else Path(x).read_bytes()).hexdigest()
def load(p):return json.loads(Path(p).read_text())
def write(name,d): (TASK/name).write_text(json.dumps(d,ensure_ascii=False,indent=2)+'\n')
def git(repo,*args):return subprocess.run(['git','-C',str(repo),*args],capture_output=True,check=True).stdout
def point(p):return p['line'],p['col']
def contains(a,b):return a is not None and b is not None and point(a['start'])<=point(b['start']) and point(b['end'])<=point(a['end'])
def off(raw,p):
    lines=raw.decode().splitlines(keepends=True)
    return len((''.join(lines[:p['line']-1])+lines[p['line']-1][:p['col']]).encode())
def nameexpr(n):
    v=[]
    for s in n.split('.'):v=[v,'str',s]
    return v

def main():
    assert sha(GRAPH)=='861ad257b5657ac581fcaf138890383fd53caba157ff99fa07a903c0ab03f6ed'
    rows={r['name']:r for r in map(json.loads,GRAPH.read_text().splitlines()) if r.get('record')=='decl'}
    sources={m['module']:m for m in load(REF/'c22-participating-modules.json')}
    headers={m['module']:m for m in load(REF/'module-closure.json')['modules']}
    receipt=load(REF/'c22-graph-source-receipt.json')
    previous=load(PRIOR/'inventory.json'); packet=load(PACKET/'inventory.json'); volume=load(VOLUME/'inventory.json'); prior_modules={m['module'] for u in [previous,packet,volume] for m in u['modules']}
    prior_selected={r['name'] for u in [previous,packet,volume] for m in u['modules'] for r in m['declarations'] if r['selectedForBundle']}
    prior_map=load(PRIOR/'wrapped/typed-original-source-wrapped-map.json')
    registry=load(WORK/'.local/adaptation/platform-node-registry.json')['reference_source_preparation']['definitions']
    prior_bundles=load(PRIOR/'wrapped/foundation-wrapper-report.json')['bundles']+load(PACKET/'generated-wrapped/foundation-wrapper-report.json')['bundles']+load(VOLUME/'generated-wrapped/foundation-wrapper-report.json')['bundles']
    def deps(n):return set(rows[n]['typeDeps']+rows[n]['valueDeps']+rows[n]['constructors'])
    def closure(seed):
        seen=set(); todo=list(seed)
        while todo:
            n=todo.pop()
            if n in seen:continue
            assert n in rows,n
            seen.add(n);todo.extend(deps(n)-seen)
        return seen
    minimum=closure(rows[ROOT]['typeDeps']); structural=set(minimum); rounds=[]
    while True:
        modules={rows[n]['module'] for n in structural}
        instances={n for n,r in rows.items() if r['module'] in modules and r['isInstance'] and not r['isInternal']}
        inds=[rows[n] for n in structural if rows[n]['kind']=='inductive']
        emitted={n for n,r in rows.items() if any(a['module']==r['module'] and contains(a['range'],r['range']) for a in inds)}
        nxt=closure(structural|instances|emitted)
        rounds.append({'input':len(structural),'instances':len(instances),'structureContained':len(emitted),'output':len(nxt)})
        if nxt==structural:break
        structural=nxt
    oldplan=load('/tmp/p2m-reference-carrier-closure-next-20261115/plan.json')
    assert minimum==set(oldplan['sets']['kernelSignatureMinimum']['names'])
    assert structural==set(oldplan['sets']['fullSourceStructureContext']['names'])
    # Maximal compiler ranges are candidates, not asserted parser command spans.
    roots={}; owners={}; module_roots={}
    for module in ORDER:
        rr=[r for r in rows.values() if r['module']==module and r['range']]
        maximal=[r for r in rr if not any(contains(s['range'],r['range']) and s['range']!=r['range'] for s in rr)]
        groups=defaultdict(list)
        for r in maximal:groups[json.dumps(r['range'],sort_keys=True)].append(r)
        chosen=[]
        for group in groups.values():
            c=min(group,key=lambda r:(r['kind']!='inductive',r['isInternal'],len(r['name']),r['name']))
            roots[c['name']]=c;chosen.append(c['name'])
        module_roots[module]=sorted(chosen,key=lambda n:(point(rows[n]['range']['start']),n))
        for n,r in rows.items():
            if r['module']!=module:continue
            ranged=[k for k in chosen if contains(rows[k]['range'],r['range'])]
            if ranged:owners[n]=min(ranged,key=len)
            elif not r['range']:
                candidates=[k for k in chosen if n==k or n.startswith(k+'.')]
                if candidates:owners[n]=max(candidates,key=len)
    selected={n for n in structural if rows[n]['module'] in ORDER}; material_rounds=[]
    while True:
        selected_roots={owners[n] for n in selected if n in owners}
        generated={n for n,owner in owners.items() if owner in selected_roots}
        full=closure(selected|generated)
        outside={n for n in full if rows[n]['module'] not in ORDER and rows[n]['module'] not in prior_modules}
        assert not outside,sorted(outside)
        nxt={n for n in full if rows[n]['module'] in ORDER}
        material_rounds.append({'input':len(selected),'sourceRootCandidates':len(selected_roots),'emittedCandidates':len(generated),'output':len(nxt)})
        if nxt==selected:break
        selected=nxt
    required_prior={n for n in full if rows[n]['module'] in prior_modules}
    prior_kernel=load(PRIOR/'kernel-audit/foundation-kernel-audit.json')
    prior_available={r['original'] for r in prior_kernel['comparisons'] if r['kernelTypeEqual']}
    effective_packet=load(PACKET/'accepted-compiler-correspondence.json')
    prior_available.update(r['original'] for r in effective_packet['namedPairs'])
    prior_actual={r['original']:r['target'] for r in prior_kernel['comparisons'] if r['kernelTypeEqual']}
    prior_actual.update({r['original']:r['target'] for r in effective_packet['namedPairs']})
    effective_volume=load(VOLUME/'accepted-compiler-correspondence.json')
    prior_available.update(r['original'] for r in effective_volume['namedPairs'])
    prior_actual.update({r['original']:r['target'] for r in effective_volume['namedPairs']})
    assert len(prior_available)==len(prior_actual)==339
    missing_prior=sorted(required_prior-prior_available)
    prior_unselected_support=sorted(required_prior-prior_selected)
    reverse=defaultdict(list)
    for n,r in rows.items():
        for e in ['typeDeps','valueDeps','constructors']:
            for d in r[e]:reverse[d].append({'consumer':n,'edge':e})
    def path(n):
        q=deque([[n]]);seen={n}
        while q:
            p=q.popleft()
            if p[-1]==ROOT:return p
            for e in reverse[p[-1]]:
                if e['consumer'] not in seen:seen.add(e['consumer']);q.append(p+[e['consumer']])
        return None
    manifest=load(BASE/'refer/iut/lake-manifest.json')
    tlock=next(p for p in manifest['packages'] if p['name'].strip('«»')=='tate-curves-theta')
    tcommit=git(TATE,'rev-parse','HEAD').decode().strip();assert tcommit==tlock['rev']
    tlicense=git(TATE,'ls-tree','-r','--name-only',tcommit).decode().splitlines()
    tlicense=[x for x in tlicense if Path(x).name.lower().startswith(('license','copying','notice'))]
    imports=[]; inventory=[]; config={'schema':'reference-foundation-parser-config-v1','outputDir':str(B/'parser-output'),'acceptedGraphSha256':sha(GRAPH),'sources':[]}
    unit={'schema':'reference-carrier-unit-v1','projectPrefixes':['Iut','TateCurvesTheta'],'prefixMap':{'Iut':'AbcAdaptation.Reference.Iut','TateCurvesTheta':'AbcAdaptation.Reference.TateCurvesTheta'},'sources':[]}
    oldmath=Path('/home/admin-wsl/Coq/mathlib4');newmath=Path('/home/admin-wsl/Coq/mathlib4-0df444a')
    translations={'Mathlib.Algebra.Group.Semigroup':'Mathlib.Algebra.Group.Defs','Mathlib.Basic.SetLike.Basic':'Mathlib.Data.SetLike.Basic','Mathlib.Algebra.Group.Monoid':'Mathlib.Algebra.Group.Defs','Mathlib.Basic.Finite.Defs':'Mathlib.Data.Finite.Defs','Mathlib.Basic.Finite.Prod':'Mathlib.Data.Finite.Prod','Mathlib.Basic.Real.Basic':'Mathlib.Data.Real.Basic','Mathlib.Algebra.Group.DivInvMonoid':'Mathlib.Algebra.Group.Defs','Mathlib.Basic.FunLike.Basic':'Mathlib.Data.FunLike.Basic','Mathlib.Basic.FunLike.Equiv':'Mathlib.Data.FunLike.Equiv'}
    export_records=[]
    for module in ORDER:
        source=Path(sources[module]['source']);raw=source.read_bytes();norm=raw.replace(b'\r\n',b'\n')
        assert sha(raw)==receipt['sourceFiles'][module]['rawSha256']
        tate=module.startswith('TateCurvesTheta.');repo=TATE if tate else OLDIUT;commit=tcommit if tate else IUTCOMMIT
        rel='/'.join(module.split('.'))+'.lean'
        upstream_raw=git(repo,'show',commit+':'+rel)
        original_source=Path(sources[module].get('original_source',source))
        overridden=source!=original_source
        assert overridden or upstream_raw==raw
        assert original_source.read_bytes()==upstream_raw
        prov={'originalSourcePath':rel,'originalAuthors':'The tate-curves-theta contributors' if tate else 'The iut contributors','originalRepository':tlock['url'] if tate else 'https://github.com/lana-agents/iut','originalCommit':commit,'originalLicense':'Apache-2.0','licenseFile':None if tate else str(BASE/'refer/iut/LICENSE'),'licenseSha256':None if tate else sha(BASE/'refer/iut/LICENSE'),'sourceHeaderSha256':sha(raw[:raw.index(b'import ')]),'sourceSha256':sha(raw),'sourceGitBlobMatches':upstream_raw==raw,'sourceOverridden':overridden,'originalSource':str(original_source),'upstreamSourceSha256':sha(upstream_raw),'effectiveSourceIsAcceptedGraphInput':True,'acceptedGraphJobId':'ci-012771-ee109b3e','sourceGitObject':git(repo,'rev-parse',commit+':'+rel).decode().strip(),'actualGitRepository':str(repo),'evidence':[{'path':str(BASE/'refer/iut/lake-manifest.json'),'sha256':sha(BASE/'refer/iut/lake-manifest.json')},{'path':str(source),'sha256':sha(raw)}]}
        if tate:prov.update(licenseEvidence='Apache 2.0 declaration in exact upstream source header; no LICENSE/COPYING/NOTICE file exists in repository tree',repositoryLicenseFiles=tlicense,manifestPackage=tlock,upstreamDeclaredToolchain=(TATE/'lean-toolchain').read_text().strip(),acceptedCompilerVersion='4.35.0-rc3')
        rr=[r for r in rows.values() if r['module']==module];cfg=[];facts=[]
        sr=[n for n in module_roots[module] if n in selected_roots]
        helpers={n for n in sr if rows[n]['kind']=='theorem' and not rows[n]['isInstance']}
        for r in rr:
            n=r['name'];rng=r['range'];chosen=n in selected
            facts.append(dict(r,selectedForBundle=chosen,selected=chosen,actualConsumers=reverse[n],consumerPathToMainTheorem=path(n),sourceCommandRootCandidate=n in sr,sourceCommandOwnerCandidate=owners.get(n),sourceHelper={'policy':'retain exact original proof inside definition bundle; no separate theorem node','actualConsumers':reverse[n]} if n in helpers else None,selectionReason='signature-and-public-instance-closure' if n in structural else 'whole-source-command-emission-or-dependency' if chosen else 'excluded',inKernelSignatureMinimum=n in minimum,inFullStructureEmission=n in structural))
            cfg.append({'name':n,'kind':r['kind'],'selected':chosen,'sourceRootCandidate':n in sr,'sourceHelper':n in helpers,'hasCompilerRange':rng is not None,'expectedStartOffset':off(norm,rng['start']) if rng else None,'expectedEndOffset':off(norm,rng['end']) if rng else None})
            export_records.append({'name':n,'nameExpr':None,'nameResolutionStatus':'pending-actual-compiler-Name-resolution','module':module,'sourceSha256':sha(raw),'normalizedSha256':sha(norm),'selected':chosen})
        entry={'module':module,'source':str(source),'sourceSha256':sha(raw),'normalizedSha256':sha(norm),'compilerDeclarations':cfg,'provenance':prov}
        config['sources'].append(entry);unit['sources'].append({k:v for k,v in entry.items() if k!='compilerDeclarations'})
        inventory.append({'module':module,'source':str(source),'sourceSha256':sha(raw),'normalizedSha256':sha(norm),'provenance':prov,'parsedSourceImports':headers[module]['imports'],'selectedSourceCommandCandidates':sr,'sourceCommandSelectionStatus':'compiler-range candidates; parser AST containment and small-source oracle remain required','graphCounts':dict(Counter(r['kind'] for r in rr)),'declarations':facts})
        external={d['module'] for r in rr if r['name'] in selected for d in r['externalDependencies']}
        candidates=[]
        for m in sorted(x for x in external if x.startswith('Mathlib.')):
            mapped=translations.get(m,m)
            candidates.append({'sourceCompilerTermModule':m,'source435PathExists':oldmath.joinpath(*m.split('.')).with_suffix('.lean').is_file(),'platform433SamePathExists':newmath.joinpath(*m.split('.')).with_suffix('.lean').is_file(),'platform433Candidate':mapped,'platform433CandidatePathExists':newmath.joinpath(*mapped.split('.')).with_suffix('.lean').is_file(),'status':'source-existence candidate; compatibility/notation/tactic imports require main CI'})
        participating=sorted({rows[d]['module'] for r in rr if r['name'] in selected for d in deps(r['name']) if rows[d]['module']!=module})
        platform_defs=['Definitions.Def_AbcAdaptation_Reference_'+m.replace('.','_') for m in participating]
        imports.append({'module':module,'source435Imports':sorted(external|set(participating)),'platform433Candidates':[x['platform433Candidate'] for x in candidates]+platform_defs,'participatingDependencies':participating,'candidates':candidates,'originalParsedImports':headers[module]['imports'],'monolithicMathlibImportAllowed':False})
    write('inventory.json',{'schema':'reference-foundation-inventory-v1','graph':str(GRAPH),'graphSha256':sha(GRAPH),'acceptedGraphJob':'ci-012771-ee109b3e','modules':inventory,'projectPrefixes':unit['projectPrefixes'],'prefixMap':unit['prefixMap']})
    write('parser-config.json',config);write('unit-config.json',unit);write('imports.json',imports)
    write('export-config.json',{'schema':'foundation-original-export-config-v2','compilerVersion':'4.35.0-rc3','expectedRecordCount':len(export_records),'expectedSelectedCount':sum(x['selected'] for x in export_records),'inventorySha256':sha(TASK/'inventory.json'),'graphSha256':sha(GRAPH),'outputFile':str(B/'original-exprs.json'),'sources':unit['sources'],'records':export_records})
    imported=[]
    for b in prior_bundles:
        n=b['definitionName'];registered=next(x for x in registry if x['name']==n)
        file=WORK/'Definitions'/Path(b['path']).name
        imported.append({'module':b['module'],'wrappedModule':b['wrappedModule'],'definitionName':n,'platformId':registered['id'],'status':registered.get('status'),'file':str(file),'sha256':sha(file),'neededConstants':sorted(n for n in required_prior if rows[n]['module']==b['module'])})
    write('dependency-closure.json',{'schema':'next-carrier-dependency-closure-v1','graphSha256':sha(GRAPH),'root':ROOT,'rootSignatureSeeds':rows[ROOT]['typeDeps'],'minimumNames':sorted(minimum),'structuralNames':sorted(structural),'globalRounds':rounds,'agreesWithEarlierPointer':True,'selectedMaterialNames':sorted(selected),'materialRounds':material_rounds,'sourceCommandOwnerCandidates':{n:owners.get(n) for n in sorted(selected)},'ownershipPolicy':'ranged containment first; absent-range longest source-root prefix is a candidate only; validate exact generation with small-source oracle','selectedNoOwner':sorted(n for n in selected if n not in owners),'requiredPriorConstants':sorted(required_prior),'missingPriorSelectedConstants':sorted(required_prior-prior_selected),'missingPriorAvailableConstants':missing_prior,'priorGeneratedSupportRequired':prior_unselected_support,'priorKernelAuditPath':str(PRIOR/'kernel-audit/foundation-kernel-audit.json'),'priorKernelAuditSha256':sha(PRIOR/'kernel-audit/foundation-kernel-audit.json'),'priorInventory':str(PRIOR/'inventory.json'),'priorInventorySha256':sha(PRIOR/'inventory.json'),'priorMap':str(PACKET/'accepted-compiler-correspondence.json'),'priorMapSha256':sha(PACKET/'accepted-compiler-correspondence.json'),'priorMapPolicy':'Actual kernel-accepted named constants only; raw wrapper candidate names are provenance, never dependency identity. Proof-value resolutions have no standalone target identity.','requiredPriorActualPairs':[{'original':n,'target':prior_actual.get(n),'module':rows[n]['module'],'supplierUnit':'volume-tate' if n in {r['original'] for r in effective_volume['namedPairs']} else 'packet-field' if n in {r['original'] for r in effective_packet['namedPairs']} else 'foundation'} for n in sorted(required_prior)],'availableAcceptedNamedCount':339,'requiredPriorProofValueResolutions':[],'priorEvidence':[{'path':str(VOLUME/'accepted-compiler-correspondence.json'),'sha256':sha(VOLUME/'accepted-compiler-correspondence.json')},{'path':str(PRIOR/'kernel-audit/foundation-kernel-audit.json'),'sha256':sha(PRIOR/'kernel-audit/foundation-kernel-audit.json')},{'path':str(PACKET/'accepted-compiler-correspondence.json'),'sha256':sha(PACKET/'accepted-compiler-correspondence.json')}],'importedBundles':imported,'typeEdges':[{'consumer':n,'dependency':d} for n in sorted(selected) for d in rows[n]['typeDeps']],'valueEdges':[{'consumer':n,'dependency':d} for n in sorted(selected) for d in rows[n]['valueDeps']],'constructorEdges':[{'consumer':n,'dependency':d} for n in sorted(selected) for d in rows[n]['constructors']]})
    write('machine-plan.json',{'status':'frozen-parser-and-inventory-draft-no-CI','plannedMainDirectory':str(B),'draftDirectory':str(TASK),'moduleOrder':ORDER,'projectPrefixes':unit['projectPrefixes'],'prefixMap':unit['prefixMap'],'parser':{'query':'QueryNextCarrierParserRanges.lean','config':'parser-config.json','environmentVariable':'FOUNDATION_PARSER_CONFIG','firstLeafEstimate':{'expected_duration':'60s','expected_memory':'16GiB'},'exclusive':True},'export':{'config':'export-config.json','environmentVariable':'NEXT_CARRIER_EXPORT_CONFIG'},'sourceCommandCandidates':sum(len(m['selectedSourceCommandCandidates']) for m in inventory),'selectedDeclarationCount':len(selected),'originalDeclarationCount':len(export_records),'priorMissingConstants':missing_prior,'parserRequiredBeforeSlicing':True,'separateOrphanTheoremNodesAllowed':False,'scope':'source carrier preparation; no mathematical field constructions or parent proof completion'})
    print(json.dumps({'modules':len(ORDER),'sourceRoots':sum(len(m['selectedSourceCommandCandidates']) for m in inventory),'selected':len(selected),'allDeclarations':len(export_records),'priorRequired':len(required_prior),'priorMissing':missing_prior,'selectedNoOwner':[n for n in selected if n not in owners],'importCandidateMissing':[x for m in imports for x in m['candidates'] if not x['platform433CandidatePathExists']]},ensure_ascii=False))

if __name__=='__main__':main()
