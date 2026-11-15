#!/usr/bin/env python3
"""Bind three accepted prior units to the new inventory. Offline only."""
import argparse, copy, json
from pathlib import Path
from carrier_contract import load, sha, require, unit_config, dependency_evidence
TASK=Path(__file__).resolve().parent

def main():
 p=argparse.ArgumentParser(description=__doc__)
 for x in ['inventory-unit','dependency-closure','volume-bound-unit','volume-correspondence','volume-ci-result','provenance-audit','out']:p.add_argument('--'+x,required=True)
 p.add_argument('--volume-typed-map')
 a=p.parse_args();out=Path(a.out).resolve();require(TASK in out.parents,'Output outside unit directory')
 unit=copy.deepcopy(load(a.inventory_unit));closure=load(a.dependency_closure)
 require(closure['schema']=='next-carrier-dependency-closure-v1','Unsupported closure schema')
 require(not closure['missingPriorAvailableConstants'] and not closure['requiredPriorProofValueResolutions'],'Missing named prior or unapproved proof-value scope')
 require(all(sha(e['path'])==e['sha256'] for e in closure['priorEvidence']),'Closure evidence changed')
 prior=load(a.volume_bound_unit);dependencies=copy.deepcopy(prior['dependencies'])
 require(len(dependencies)==2,'Expected foundation and packet-field dependencies')
 correspondence_path=Path(a.volume_correspondence).resolve();c=load(correspondence_path)
 typed_path=Path(a.volume_typed_map).resolve() if a.volume_typed_map else correspondence_path.parent/'generated-wrapped/typed-original-source-wrapped-map.json'
 typed=load(typed_path);receipt=Path(a.volume_ci_result).resolve()
 require(sha(receipt)==c['receiptSha256'] and load(receipt)['job_id']==c['job_id']=='ci-013964-cce30c9e','Volume final-v5 receipt differs')
 # Every module path is the actual installed Definitions artifact, not a temporary candidate.
 workspace=Path(load(receipt)['request']['workspace']).resolve()
 volume={'status':'accepted-kernel-audit','typedMap':str(typed_path),'typedMapSha256':sha(typed_path),
  'acceptedConstantNames':sorted(r['original'] for r in c['namedPairs']),
  'acceptedCorrespondence':{'unitKind':'volume-tate','path':str(correspondence_path),'sha256':sha(correspondence_path)},
  'auditEvidence':[{'kind':'kernel-audit','path':c['audit'],'sha256':c['auditSha256']},
                   {'kind':'ci-result','path':str(receipt),'sha256':sha(receipt)}],
  'modules':[{'originalModule':m['originalModule'],'wrappedModule':m['wrappedModule'],
              'path':str(workspace/'Definitions'/(m['wrappedModule'].split('.')[-1]+'.lean')),
              'sha256':sha(workspace/'Definitions'/(m['wrappedModule'].split('.')[-1]+'.lean'))}for m in typed['modules']]}
 unit.update(dependencies=dependencies+[volume],sourceProvenanceAudit={'path':str(Path(a.provenance_audit).resolve()),'sha256':sha(a.provenance_audit)},
  inventoryEvidence=[{'path':str(Path(x).resolve()),'sha256':sha(x)}for x in [a.inventory_unit,a.dependency_closure]])
 constants,modules,_=dependency_evidence(unit)
 require(len(constants)==339 and len(modules)==15,'Expected339 actual named identities and15 prior modules')
 require(closure['availableAcceptedNamedCount']==339 and len(closure['requiredPriorActualPairs'])==42,'Closure dimensions differ')
 for bundle in closure['importedBundles']:
  actual=modules[bundle['module']]
  require(actual['sha256']==bundle['sha256'] and Path(actual['path']).resolve()==Path(bundle['file']).resolve(),'Installed dependency differs')
 for pair in closure['requiredPriorActualPairs']:
  actual=constants[pair['original']]
  require(actual['wrappedName']==pair['target'] and actual['originalModule']==pair['sourceOwner'],'Required actual pair differs')
 unit['requiredPriorActualNames']=sorted(r['original']for r in closure['requiredPriorActualPairs'])
 unit['proofValueResolverPolicy']='not-needed-by-this-unit; prior elisions are evidence only with no named identity'
 out.parent.mkdir(parents=True,exist_ok=True);out.write_text(json.dumps(unit,ensure_ascii=False,indent=2)+'\n');unit_config(out)
 print(json.dumps({'status':'offline-evidence-bound','path':str(out),'sha256':sha(out),'priorActualNamedConstants':339,'requiredPriorActualConstants':42,'proofValueResolverLoaded':False}))
if __name__=='__main__':main()
