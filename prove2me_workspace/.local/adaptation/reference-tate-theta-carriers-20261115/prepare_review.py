#!/usr/bin/env python3
"""Generate candidate scope/consumer ledger and independently check actual prior suppliers."""
import hashlib,json
from collections import Counter
from pathlib import Path
P=Path('/tmp/p2m-tate-theta-inventory-v5-20261115');B=Path('/home/admin-wsl/Coq/abc/prove2me_workspace/.local/adaptation/reference-tate-theta-carriers-20261115')
def load(p):return json.loads(Path(p).read_text())
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def write(n,d):(P/n).write_text(json.dumps(d,ensure_ascii=False,indent=2)+'\n')
inv=load(P/'inventory.json');closure=load(P/'dependency-closure.json');prior=load(P/'accepted-prior-identity-map.json');ledger=[];scopes=[]
for m in inv['modules']:
 lines=Path(m['source']).read_text().splitlines();selected={r['name'] for r in m['declarations'] if r['selected']}
 # These are lexical review observations, not parser AST facts or slices.
 context=[{'line':i,'text':s} for i,s in enumerate(lines,1) if s.startswith(('namespace ','section','noncomputable section','end','variable ','universe ','open ','omit ','include '))]
 eof_anon=m['module'].startswith('TateCurvesTheta.')
 scopes.append({'module':m['module'],'sourceSha256':m['sourceSha256'],'completeFrozenSource':m['provenance']['frozenEffectiveSource'],'status':'static-source-review-pending-parser-AST','contextCommandLineCandidates':context,'eofImplicitAnonymousNoncomputableSection':eof_anon,'policy':'Preserve all context commands and scopes from actual parser AST. Balance EOF-implicit anonymous sections before concatenation; do not strip source text or infer signatures.'})
 for n in m['selectedSourceCommandCandidates']:
  r=next(r for r in m['declarations'] if r['name']==n);owned=[x for x in m['declarations'] if x['sourceCommandOwnerCandidate']==n];assert all(x['selected'] for x in owned)
  record={'original':n,'module':m['module'],'status':'source-command-candidate-not-current-compiler-accepted','source':m['source'],'sourceSha256':m['sourceSha256'],'frozenSource':m['provenance']['frozenEffectiveSource'],'sourceRootCompilerRange':r['range'],'completeParserCommandSpan':None,'spanStatus':'Pending actual source compiler parser AST. Compiler range is not a complete source-command assertion.','originalRepository':m['provenance']['originalRepository'],'originalCommit':m['provenance']['originalCommit'],'sourceGitObject':m['provenance']['sourceGitObject'],'originalSourcePath':m['provenance']['originalSourcePath'],'originalLicense':'Apache-2.0','fidelity':'Exact full source command, docs, context and all structure fields must be preserved; inline helper proof bodies remain inside the carrier. No target type weakening or extra assumptions.','ownedOriginalCandidates':[x['name'] for x in owned],'actualConsumers':r['actualConsumers'],'consumerPathToMainTheorem':r['consumerPathToMainTheorem'],'typeDeps':r['typeDeps'],'valueDeps':r['valueDeps'],'constructors':r['constructors'],'sourceHelper':r['sourceHelper'],'mathematicalScope': 'Complete original structure with every public field and all generated declarations' if r['kind']=='inductive' else 'Exact original inline helper proof and all its consumers' if r['sourceHelper'] else 'Exact original definition body, including all dependent binders and computational data'}
  ledger.append(record)
write('SOURCE_LEDGER.json',{'schema':'tate-theta-source-command-candidate-ledger-v1','status':'uncompiled-candidate','graph':inv['graph'],'graphSha256':inv['graphSha256'],'records':ledger,'producerCount':len(ledger),'consumerEdgePolicy':'actualConsumers and consumerPathToMainTheorem copied from exact accepted graph, preserving edge kinds; generated names belong to their whole original source command','acceptancePolicy':'No new carrier, source slice, parser span, compiler Name or target identity is accepted by this ledger.'})
write('source-context-review.json',{'schema':'tate-theta-static-source-context-review-v1','modules':scopes,'parsePerformed':False,'scopeWarning':'Lexical command candidates guide review only. Exact parser AST remains authoritative.'})
lookup={r['original']:r for r in prior['namedPairs']};checks=[]
def ck(x,label):assert x,label;checks.append(label)
ck(len(lookup)==339,'339 distinct accepted named originals')
ck(len(closure['requiredPriorActualPairs'])==42,'42 exact required actual named pairs')
for r in closure['requiredPriorActualPairs']:
 ck(r==lookup[r['original']],r['original']+' complete pair copied from prior accepted identity map')
 ck(sha(r['evidencePath'])==r['evidenceSha256'],r['original']+' supplier evidence hash')
for r in prior['proofValueResolutions']:
 ck(r['standaloneTargetIdentity'] is None,r['original']+' no standalone target identity')
 ck(r['original'] not in lookup and r['original'] not in closure['requiredPriorConstants'],r['original']+' separate from actual named dependency requirements')
for e in prior['evidence']:
 ck(sha(e['path'])==e['sha256'],e['path']+' accepted evidence unchanged')
ck(sum(len(x['neededConstants']) for x in closure['importedBundles'])==42,'all42 required named supplied by installed bundle inputs')
for m in inv['modules']:
 ck(not m['provenance']['sourceOverridden'],m['module']+' no source override')
 ck(Path(m['source']).read_bytes()==(P/Path(m['provenance']['frozenEffectiveSource']['path']).relative_to(B)).read_bytes(),m['module']+' complete exact source retained')
for n in ['Iut.AdmissiblePrimeData','Iut.TateStructure']:
 r=next(r for r in ledger if r['original']==n);ck(bool(r['constructors']),n+' constructors retained');ck(bool(r['consumerPathToMainTheorem']),n+' actual consumer path retained')
export=load(P/'export-config.json');ck(all(r['nameExpr'] is None and r['nameResolutionStatus']=='pending-actual-compiler-Name-resolution' for r in export['records']),'all117 source candidate Names await actual compiler resolution')
private=[r for m in inv['modules'] for r in m['declarations'] if r['isPrivate']];ck(len(private)==6 and all(not r['selected'] for r in private),'six numeric-private Parametrization originals kept in all-original scope only')
query=(P/'QueryNextCarrierParserRanges.lean').read_text();ck('.num p n' in query and 'encodeActualName actualName' in query and 'findDeclarationRanges? name.toName' not in query,'parser serializes actual numeric Names without display-name reconstruction')
write('supplier-and-scope-static-audit.json',{'schema':'tate-theta-supplier-scope-static-audit-v1','status':'passed','checkCount':len(checks),'checks':checks,'compilationPerformed':False,'currentAcceptanceAsserted':False})
(P/'SOURCE_LEDGER.md').write_text('''# Four-module source carrier candidate ledger

The source inventory contains 117 original declarations, with 78 selected declarations emitted by 20 complete source-command candidates. `SOURCE_LEDGER.json` records exact source/Git hashes, all producer-to-consumer edges, paths to the actual Theorem110 consumer, and unchanged source proof dependencies. Parser command spans and current target identities are pending compilation.

The complete `AdmissiblePrimeData` command retains all 15 fields, including the genuine Galois-action pin `rep_spec`, image/open-kernel data, and every bad-place Tate/uniformizer/coprimality field. The complete `TateStructure` command retains all six fields `t`, `C`, `hC`, `iso`, `iso_x`, and `iso_y`; it does not construct the explicit uniformization. The exact inline source proofs `galPointMap_torsionBy` and `TateStructure.ofUnit_mul/ofUnit_one/ofUnit_inv` remain inside their carriers. No independent theorem nodes are proposed for them.

The selected coordinate definitions fix the original `tateJ`, `Xterm`, `Yterm`, `X`, and `Y` formulas. Convergence, discriminant/norm estimates, periodicity, and the optional `ofTateParameter` constructor are outside this selected dependency closure. This unit does not discharge those statements or the mathematical parent obligation.

Each frozen source preserves its exact Apache 2.0 header. Tate has no standalone upstream LICENSE/COPYING/NOTICE file; the distributed Apache license text comes from pinned iut. No current parser, source-slice, kernel or Prove2Me acceptance is asserted.
''')
print(json.dumps({'status':'passed','supplierScopeChecks':len(checks),'ledgerProducerCandidates':len(ledger),'scopeModules':len(scopes)}))
