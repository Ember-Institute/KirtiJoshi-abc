#!/usr/bin/env python3
"""Build the four-module ledger from accepted actual compiler correspondence only.

No compiler, CI, API, network, Git or production registry operations are performed.
The caller chooses a new output directory. Candidate mapping files are not inputs.
"""
import argparse
import hashlib
import json
from pathlib import Path

ALLOWED = {'propext','Classical.choice','Quot.sound'}
SCOPES = {
 'TateCurvesTheta.TateCurve.JInvariant': 'The totalized field expression tateCurve.c₄ ^ 3 / tateCurve.Δ. No nonzero-discriminant, norm, analytic j-parameter or agreement theorem is supplied by this bundle.',
 'TateCurvesTheta.TateCurve.Parametrization': 'Exact rational Xterm/Yterm and total-tsum X/Y definitions, with their selected compiler support. No convergence, periodicity, curve-membership, quotient or uniformization theorem is supplied by this bundle.',
 'Iut.Cor312.ThetaData.AdmissiblePrime': 'The complete 15-field supplied AdmissiblePrimeData interface, genuine Galois point map and exact inline torsion-preservation helper, local completion, fixed-field definition and normalized qOrder definition. Fbar has Field and Algebra assumptions only. No construction of admissible data or finite-Galois torsion extension is established.',
 'Iut.Cor312.ThetaData.TateStructure': 'The complete six-field supplied TateStructure interface retains t, C, hC, the actual quotient additive isomorphism iso and both coordinate pins. Exact coordinate maps, ofUnit and its inline group-law helpers, graphLine and IsCanonical are retained. The latter two quantify over every ℓ : ℕ. No torsion/graph-quotient theorem or ofTateParameter construction is established.'}
def load(p): return json.loads(Path(p).read_text())
def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def digest(b): return hashlib.sha256(b).hexdigest()
def require(ok,msg):
    if not ok: raise ValueError(msg)
def cut(data,r): return data[r['start']['offset']:r['end']['offset']]
def checked_file(evidence):
    require(sha(evidence['path'])==evidence['sha256'],'Evidence hash changed: '+evidence['path'])
def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--unit',required=True,type=Path)
    ap.add_argument('--wrapper-report',required=True,type=Path)
    ap.add_argument('--correspondence',required=True,type=Path)
    ap.add_argument('--out',required=True,type=Path)
    args=ap.parse_args(); unit=args.unit.resolve()
    inv=load(unit/'inventory.json'); deps=load(unit/'dependency-closure.json')
    require({m['module'] for m in inv['modules']}==set(SCOPES),'Not this exact four-module unit')
    require(sha(inv['graph'])==inv['graphSha256'],'Accepted original graph changed')
    wr=load(args.wrapper_report); wrappers={w['module']:w for w in wr['bundles']}
    require(len(wrappers)==4 and set(wrappers)==set(SCOPES),'Wrapper modules differ')
    require(wr['definitionsBundleCount']==4,'Wrapper bundle count differs')
    cor=load(args.correspondence)
    require(cor['status']=='accepted-kernel-audit','Accepted compiler correspondence is required; candidate names are refused')
    require(cor['wrapperReport']=={'path':str(args.wrapper_report.resolve()),'sha256':sha(args.wrapper_report)},'Correspondence does not bind this exact wrapper report')
    require(sha(cor['audit'])==cor['auditSha256'] and sha(cor['receipt'])==cor['receiptSha256'],'Accepted audit or receipt changed')
    audit=load(cor['audit']); receipt=load(cor['receipt'])
    require(receipt['job_id']==cor['job_id'] and receipt['status']=='succeeded' and receipt['result']['exit_code']==0,'Kernel receipt not succeeded')
    require(not audit['hasSorryAx'] and audit['allOwnedTypeValueClosuresStandardAxiomsOnly'],'Owned axiom closure did not pass')
    comparisons={(r['original'],r['target']):r for r in audit['comparisons']}
    named={}; proofs={}
    for pair in cor['namedPairs']:
        n=pair['original']; require(n not in named,'Duplicate original named comparison: '+n)
        row=comparisons.get((n,pair['target'])); require(row is not None and row['kernelTypeEqual'],'Named comparison absent or failed: '+n)
        require(pair['originalName']==row['originalName'] and pair['targetName']==row['targetName'],'Actual structural Names differ: '+n)
        require(row['binderInfoPlacementEqual'] and row['allExpressionBinderInfoEqual'] and row['completeStructureMetadataEqual'],'Binders or full structure metadata differ: '+n)
        require(row['kernelValueEqual'] or row['proofDeclaration'] or row['recursorRulesCompared'] or row['sourceRecord']['valueExpr'] is None,'Computational value not compared: '+n)
        named[n]=pair
    require(cor.get('proofValueResolutions',[])==audit.get('proofValueResolutions',[]),'Proof-value resolutions differ from actual audit')
    for row in cor.get('proofValueResolutions',[]):
        n=row['original']; require(n not in named and n not in proofs,'Proof resolution collides with named identity: '+n)
        require(row['standaloneTargetIdentity'] is None and row['resolution']=='genuine-exported-original-proof-value','Proof resolution invents standalone identity: '+n)
        require(not row['hasSorryAx'] and row['genuineOriginalValueInhabitsExactOriginalType'] and row['exactOriginalTypeKernelChecked'] and row['originalTypeBinderInfoPreserved'] and row['expandedDependenciesHaveAllowedOwners'],'Proof-value audit incomplete: '+n)
        require(set(row['expandedTypeAxioms'])<=ALLOWED and set(row['expandedValueAxioms'])<=ALLOWED,'Proof-value axioms exceed standard set: '+n)
        require(not row['parentWholeValueEqualityRequired'] or row['parentOriginal'] in named,'Proof-value parent has no accepted named comparison: '+n)
        proofs[n]=row
    selected={r['name'] for m in inv['modules'] for r in m['declarations'] if r['selected']}
    require(len(selected)==78 and selected<=set(named)|set(proofs),'78 selected source obligations not resolved')
    require(cor['sourceSelectedCount']==78 and cor['sourceObligationsResolved']==78,'Accepted selected obligation count differs')
    require(len(deps['requiredPriorActualPairs'])==42 and not deps['requiredPriorProofValueResolutions'],'Prior named supplier obligations differ')
    for pair in deps['requiredPriorActualPairs']: checked_file({'path':pair['evidencePath'],'sha256':pair['evidenceSha256']})
    entries=[]
    for module in inv['modules']:
        m=module['module']; w=wrappers[m]; p=module['provenance']
        require(not p['sourceOverridden'],'Source override is outside reviewed unit')
        source=Path(p['frozenEffectiveSource']['path']).read_bytes()
        require(digest(source)==module['sourceSha256']==p['upstreamSourceSha256'],'Frozen source changed: '+m)
        wrapper=Path(w['path']).read_bytes(); require(digest(wrapper)==w['sha256'],'Wrapper changed: '+m)
        require(w['projectOccurrenceEdits']==[],'Unexpected source occurrence edits: '+m)
        commands=[]; retained=set()
        for cm in w['commandMaps']:
            require(cut(source,cm['originalRange'])==cut(wrapper,cm['wrapperRange']),'Complete source/context command bytes differ: '+m)
            require(digest(cut(source,cm['originalRange']))==cm['sha256'],'Complete command SHA differs: '+m)
            for body in cm['bodyRanges']:
                require(cut(source,body['originalRange'])==cut(wrapper,body['wrapperRange']),'Proof/definition body differs: '+m)
                require(digest(cut(source,body['originalRange']))==body['sha256'],'Body hash differs: '+m)
            retained.update(cm['selectedCompilerDeclarations']); commands.append(cm)
        rows=[]
        for d in module['declarations']:
            if not d['selected']: continue
            n=d['name']; pair=named.get(n)
            owner=deps['sourceCommandOwnerCandidates'].get(n)
            require(n in retained or owner in retained,'Selected original has no retained complete source-command owner: '+n)
            row={'original':n,'wrapped':pair['target'] if pair else None,'actualCompilerPair':pair,'kind':d['kind'],'isInstance':d['isInstance'],
                 'sourceCommandOwner':deps['sourceCommandOwnerCandidates'].get(n),'selectionReason':d['selectionReason'],
                 'actualOriginalConsumers':d['actualConsumers'],'originalConsumerPathToMainTheorem':d['consumerPathToMainTheorem'],
                 'targetIdentityStatus':'accepted-actual-named-comparison' if pair else 'accepted-internal-proof-value-no-standalone-identity'}
            if not pair: row['internalProofValueResolution']=proofs[n]
            rows.append(row)
        entries.append({'producer':w['definitionName'],'kind':'definition-bundle','stage':'reference signature and definition-body carrier preparation',
            'originalModule':m,'sourceURL':p['originalRepository']+'/blob/'+p['originalCommit']+'/'+p['originalSourcePath'],
            'sourceProvenance':p,'wrappedSourceSha256':w['sha256'],'selectedSourceCommands':module['selectedSourceCommandCandidates'],
            'selectedDeclarations':rows,'exactRetainedSourceAndContextCommands':commands,
            'actualSourceConsumer':'Iut.Theorem110Invariants.theorem110','consumerEvidence':{'graphJobId':inv['acceptedGraphJob'],'graphSha256':inv['graphSha256'],'inventorySha256':sha(unit/'inventory.json')},
            'sourceCommandsPreserved':True,'definitionBodyProofsPreserved':True,'actualScope':SCOPES[m],
            'rootGraphMembership':False,'canonicalC22Connected':False})
    require(sum(len(e['selectedSourceCommands']) for e in entries)==20,'Not 20 complete selected source commands')
    result={'schema':'reference-tate-theta-source-ledger-v1','status':'accepted-compiler-identities','entries':entries,
        'sourceCommandCount':20,'selectedDeclarationCount':78,'selectedNamedCount':len(selected&set(named)),'selectedProofValueResolutionCount':len(selected&set(proofs)),
        'additionalAcceptedUnselectedNamedPairs':[p for n,p in named.items() if n not in selected],
        'requiredPriorConstants':deps['requiredPriorConstants'],'requiredPriorActualPairs':deps['requiredPriorActualPairs'],'priorRequiredCount':42,
        'priorIdentityPolicy':'Only actual accepted named pairs are standalone dependency identities. Genuine proof values have no standalone target identity.',
        'consumerPolicy':'Exact original graph consumers and paths are retained, including empty arrays for structure fields and compiler auxiliaries. Inclusion in a full structure does not invent a downstream use.',
        'productionUpstreamDependenciesAdded':False,'rootGraphMembership':False,'canonicalC22Connected':False,'mathematicalParentObligationCompleted':False,
        'wrapperReport':{'path':str(args.wrapper_report.resolve()),'sha256':sha(args.wrapper_report)},
        'acceptedCompilerCorrespondence':{'path':str(args.correspondence.resolve()),'sha256':sha(args.correspondence),'job_id':cor['job_id']}}
    args.out.mkdir(parents=True,exist_ok=True)
    for n in ['SOURCE_LEDGER.json','SOURCE_LEDGER.md']: require(not (args.out/n).exists(),'Refuse to overwrite '+n)
    (args.out/'SOURCE_LEDGER.json').write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n')
    (args.out/'SOURCE_LEDGER.md').write_text('# Tate and initial Θ-data carrier sources\n\nFour bundles retain 20 complete source commands and resolve 78 selected source obligations. Actual named identities and any genuine internal proof-value resolutions are listed separately, using the accepted kernel correspondence. The bundles use 42 actual named identities from prior accepted units. Original consumer edges and paths are preserved, including empty structural paths.\n\nThe selected Tate formulas are totalized field expressions and total tsums. AdmissiblePrimeData retains all 15 fields; Fbar has Field and Algebra assumptions only. TateStructure retains all six fields, including the supplied quotient isomorphism and both coordinate pins. graphLine and IsCanonical accept arbitrary natural ℓ. Existence, convergence, graph-quotient identification and the mathematical parent obligation remain open for this unit.\n\nExact source notices and Apache text are retained. The iut sources are pinned to 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8; Tate sources are pinned to ca6c2279d3cea0690cdb01328e727118d5485d68. The Tate tree has no standalone LICENSE/COPYING/NOTICE file; the distributed Apache text comes from pinned iut.\n')
    print(json.dumps({'status':result['status'],'bundles':4,'commands':20,'selectedOriginals':78,'selectedNamed':result['selectedNamedCount'],'selectedProofValues':result['selectedProofValueResolutionCount']}))
if __name__=='__main__': main()
