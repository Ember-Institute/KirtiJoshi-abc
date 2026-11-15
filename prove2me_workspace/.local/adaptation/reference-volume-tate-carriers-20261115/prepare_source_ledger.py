#!/usr/bin/env python3
"""Generate a source ledger from final wrapper reports. No CI, API, compiler, or Git calls."""
import argparse, hashlib, json
from pathlib import Path

def load(p): return json.loads(Path(p).read_text())
def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def require(ok,msg):
    if not ok: raise ValueError(msg)

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--unit',required=True,type=Path)
    ap.add_argument('--wrapper-report',required=True,type=Path)
    ap.add_argument('--correspondence',type=Path,help='Optional accepted actual compiler correspondence. Candidate maps are not accepted.')
    ap.add_argument('--out',required=True,type=Path,help='Output directory. Existing ledger files are never overwritten.')
    a=ap.parse_args(); b=a.unit.resolve()
    inv=load(b/'inventory.json'); deps=load(b/'dependency-closure.json'); paper=load(b/'paper-context.json')
    wr=load(a.wrapper_report); wrappers={r['module']:r for r in wr['bundles']}
    scopes={r['module']:r['implementation_scope_en'] for r in paper['bundles']}
    correspondence=None; actual={}; resolutions={}
    if a.correspondence:
        correspondence=load(a.correspondence)
        require(correspondence.get('status')=='accepted-kernel-audit','Use an accepted compiler correspondence, not a candidate map')
        audit_path=Path(correspondence['audit']); receipt_path=Path(correspondence['receipt'])
        require(sha(audit_path)==correspondence['auditSha256'],'Accepted audit hash changed')
        require(sha(receipt_path)==correspondence['receiptSha256'],'Accepted receipt hash changed')
        audit=load(audit_path); receipt=load(receipt_path)
        require(receipt['status']=='succeeded' and receipt['result']['exit_code']==0,'Accepted receipt did not succeed')
        require(not audit['hasSorryAx'] and audit['allOwnedTypeValueClosuresStandardAxiomsOnly'],'Owned declaration axiom audit failed')
        compared={(r['original'],r['target']) for r in audit['comparisons'] if r['kernelTypeEqual']}
        for r in correspondence['namedPairs']:
            require((r['original'],r['target']) in compared,'Named identity missing from actual audit: '+r['original'])
            actual[r['original']]=r['target']
        resolutions={r['original']:r for r in correspondence.get('proofValueResolutions',[])}
    entries=[]
    for m in inv['modules']:
        w=wrappers[m['module']]; require(sha(w['path'])==w['sha256'],'Wrapper bytes changed: '+m['module'])
        p=m['provenance']; roots=m['selectedSourceCommandCandidates']; selected=[d for d in m['declarations'] if d['selected']]
        ds={d['name']:d for d in m['declarations']}; first=min(ds[n]['startLine'] for n in roots); last=max(ds[n]['endLine'] for n in roots)
        upstream_url=p['originalRepository']+'/blob/'+p['originalCommit']+'/'+p['originalSourcePath']
        # Effective compiler line numbers do not identify the modified upstream blob.
        source_url=upstream_url if p.get('sourceOverridden') else upstream_url+'#L'+str(first)+'-L'+str(last)
        decls=[]
        for d in selected:
            if correspondence: require(d['name'] in actual or d['name'] in resolutions,'Selected source obligation unresolved: '+d['name'])
            row={'original':d['name'],'wrapped':actual.get(d['name']), 'kind':d['kind'],'isInstance':d['isInstance'],
                'sourceCommandOwner':deps['sourceCommandOwnerCandidates'].get(d['name']),
                'actualOriginalConsumers':d['actualConsumers'],'originalConsumerPathToMainTheorem':d['consumerPathToMainTheorem']}
            # Generated compiler declarations need not have a consumer or theorem path.
            # Preserve the actual empty arrays/None and give their selection reason.
            row['selectionReason']=d['selectionReason']
            row['targetIdentityStatus']='accepted-actual-named-comparison' if d['name'] in actual else ('accepted-internal-proof-value' if d['name'] in resolutions else 'pending-target-compiler-audit')
            if d['name'] in resolutions:row['internalProofValueResolution']=resolutions[d['name']]
            decls.append(row)
        row={'producer':w['definitionName'],'kind':'definition-bundle','stage':'reference signature and definition-body carrier preparation',
            'owner':'reference adaptation; actual producer existence obligations keep their original stage','originalModule':m['module'],
            'sourceURL':source_url,'sourceProvenance':p,'wrappedSourceSha256':w['sha256'],'selectedSourceCommands':roots,'selectedDeclarations':decls,
            'actualSourceConsumer':'Iut.Theorem110Invariants.theorem110',
            'consumerEvidence':{'graphJobId':inv['acceptedGraphJob'],'graphSha256':inv['graphSha256'],'inventorySha256':sha(b/'inventory.json')},
            'sourceCommandsPreserved':True,'definitionBodyProofsPreserved':True,'rootGraphMembership':False,'canonicalC22Connected':False,'actualScope':scopes[m['module']]}
        if p.get('sourceOverridden'):
            row['sourceURLScope']='Whole upstream Git file; effective compiler line numbers are recorded separately.'
            row['effectiveSourceRanges']={'coordinate':'effective-source-lines',
                'source':p['frozenEffectiveSource']['path'],'sourceSha256':p['sourceSha256'],
                'selectedCommands':[{'sourceCommand':n,'startLine':ds[n]['startLine'],'endLine':ds[n]['endLine']} for n in roots]}
            row['effectiveGitDelta']={'effectiveSourceSha256':p['sourceSha256'],'upstreamGitBlobSha256':p['upstreamSourceSha256'],
                'effectiveSourceEqualsUpstreamGitBlob':False,'patch':p['effectiveSourceOverride'],
                'scope':'Two elaborator options and explicit use of the already supplied summand CommRing, with explicit term/cast types. No additional mathematical hypothesis.'}
        entries.append(row)
    result={'schema':'reference-volume-tate-source-ledger-v1','status':'accepted-compiler-identities' if correspondence else 'source-ledger-draft-target-identities-pending',
        'entries':entries,'sourceCommandCount':sum(len(x['selectedSourceCommands']) for x in entries),'selectedDeclarationCount':sum(len(x['selectedDeclarations']) for x in entries),
        'requiredPriorConstants':deps['requiredPriorConstants'],'requiredPriorActualPairs':deps['requiredPriorActualPairs'],
        'priorRequiredCount':len(deps['requiredPriorConstants']),'priorIdentityPolicy':'Actual named constants from both prior accepted kernel audits; no raw candidate maps or proof-value substitutions.',
        'productionUpstreamDependenciesAdded':False,'rootGraphMembership':False,'canonicalC22Connected':False,'paperIdentityAndArithmeticInstantiationCompleted':False,
        'paperWeightIdentification':'Open: III p94 inverse-extension-degree weights versus source-header intended direct normalized degrees. Positive fiber weights summing to one do not prove that identification.',
        'wrapperReport':{'path':str(a.wrapper_report.resolve()),'sha256':sha(a.wrapper_report)}}
    require(result['sourceCommandCount']==25 and result['selectedDeclarationCount']==100 and result['priorRequiredCount']==62,'Unexpected ledger counts')
    if correspondence: result['acceptedCompilerCorrespondence']={'path':str(a.correspondence.resolve()),'sha256':sha(a.correspondence),'job_id':correspondence['job_id']}
    a.out.mkdir(parents=True,exist_ok=True)
    for name in ['SOURCE_LEDGER.json','SOURCE_LEDGER.md']:require(not (a.out/name).exists(),'Refuse to overwrite '+name)
    (a.out/'SOURCE_LEDGER.json').write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n')
    (a.out/'SOURCE_LEDGER.md').write_text(
        '# Volume and Tate carrier sources\n\n'
        'The five bundles retain 25 complete source commands and 100 original compiler obligations. '
        'They use 62 actual named identities from two accepted prior units. '
        'The ledger preserves all original consumers and paths, including empty paths for structural declarations.\n\n'
        'Two modules come from iut commit `07cb1da58f6d428a670dbb5dd6093d428bcbcdd8`. '
        'Three modules come from tate-curves-theta commit `ca6c2279d3cea0690cdb01328e727118d5485d68`. '
        'The exact Tate sources declare Apache 2.0. That upstream tree has no standalone license file. '
        'The retained notices and `LICENSE.Apache-2.0` record this distinction.\n\n'
        'LogVolume uses the accepted effective source, SHA256 `002f44da071e858c1fe48f3608da4e75f1179d3cd6c3007444bc5453440b7ef0`. '
        'The linked upstream Git blob has SHA256 `79f0f12f1c82d6a0b6b83a42197527542fa946e9a5bb8dd4fd3572fd88edaf15`. '
        'The ledger includes the full source delta. It adds no mathematical hypothesis.\n\n'
        'These bundles prepare supplied interfaces and local definitions. '
        'Paper-object identity, arithmetic instantiation, weight normalization, and the Joshi bridge remain open. '
        'The abc root graph remains separate.\n\n'
        + ('Actual target identities come from the accepted compiler correspondence.\n' if correspondence else 'Target identities remain pending. This draft leaves each `wrapped` field null.\n'))
    print(json.dumps({'status':result['status'],'bundles':len(entries),'commands':25,'selectedOriginals':100,'priorActualIdentities':62}))

if __name__=='__main__':main()
