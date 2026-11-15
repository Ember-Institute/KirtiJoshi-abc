#!/usr/bin/env python3
"""Bind two actually passed <=16GiB source DAG leaves to the unchanged project audit.
Writes only beside this script. No compiler, CI, network, API, or Git calls.
"""
import argparse,hashlib,json,mmap
from pathlib import Path
HERE=Path(__file__).resolve().parent
W=Path('/home/admin-wsl/Coq/abc/prove2me_workspace')
RING='NumberField.RingOfIntegers.instHasFiniteQuotients'
def load(p):return json.loads(Path(p).read_text())
def sha(p):
 h=hashlib.sha256()
 with Path(p).open('rb') as f:
  for b in iter(lambda:f.read(1024*1024),b''):h.update(b)
 return h.hexdigest()
def dump(p,v):Path(p).write_text(json.dumps(v,ensure_ascii=False,separators=(',',':'))+'\n')
def display(n):return '' if not n else (display(n[0])+'.' if n[0] else '')+str(n[2])
def verify_leaf(view_path,job,stage,count,historical_config):
 view=load(view_path);assert view['schema']=='tate-theta-adic-receipt-bound-dag-view-v1'
 artifact=Path(view['originalArtifact']['path']);receipt_path=Path(view['receipt']['path'])
 assert sha(artifact)==view['originalArtifact']['sha256'] and sha(receipt_path)==view['receipt']['sha256']
 receipt=load(receipt_path);assert receipt['job_id']==view['receipt']['job_id']==job
 assert receipt['status']=='succeeded' and receipt['result']['exit_code']==0
 assert receipt['request']['exclusive'] is True
 snapshot=receipt['result']['snapshot'];assert snapshot['workspace_mode']=='exclusive_worktree' and snapshot['snapshot_id'] is None
 assert receipt['resources']['peak_rss_bytes'] is not None and receipt['resources']['peak_rss_bytes']<=17179869184
 with artifact.open('rb') as f,mmap.mmap(f.fileno(),0,access=mmap.ACCESS_READ) as data:
  for key,span in view['exactFieldByteSpans'].items():
   raw=data[span['start']:span['end']]
   assert hashlib.sha256(raw).hexdigest()==span['sha256']
   assert json.loads(raw)==view['sourceFields'][key]
 fields=view['sourceFields'];assert fields['stage']==stage and fields['stageOriginalRecordCount']==count
 assert fields['allActiveOriginalRecordCount']==35 and fields['candidateOriginalRecordCount']==50
 assert fields['allCompleteTypeValueKernelChecksPassed'] and fields['allExprDagRootsStrictExprEqualRoundTrip']
 assert fields['roundTripIncludesBinderNamesBinderInfoAndNumericNames']
 names=[display(r['nameExpr']) for r in fields['entries']]
 assert len(names)==count+1 and len(set(names))==count+1 and RING in names
 expected={display(n) for n in fields['stageOriginalRecordNames']};assert set(names)-{RING}==expected
 req=receipt['request'];old_config=req['environment']['NEXT_CARRIER_AUDIT_CONFIG'];paths=[view_path,artifact,receipt_path,historical_config]
 assert req['worktree_manifest']['input_hashes'][old_config]==sha(historical_config)
 for path,expected_sha in req['worktree_manifest']['input_hashes'].items():
  actual_path=historical_config if path==old_config else Path(path)
  assert sha(actual_path)==expected_sha,('Changed accepted leaf input',actual_path)
  paths.append(actual_path)
 return view,receipt,fields,paths

def main():
 p=argparse.ArgumentParser(description=__doc__)
 p.add_argument('--base-config',required=True,type=Path);p.add_argument('--view-a',required=True,type=Path);p.add_argument('--view-b',required=True,type=Path)
 p.add_argument('--historical-config',required=True,type=Path);p.add_argument('--output',type=Path,default=HERE/'audit-config.json');p.add_argument('--audit-output',required=True,type=Path)
 a=p.parse_args();assert a.output.resolve().parent==HERE
 base=load(a.base_config);assert base['expectedRecordCount']==117 and base['expectedSelectedCount']==78 and base['expectedNamedSelectedCount']==77 and base['expectedProofValueResolutionCount']==1
 all_paths=[a.base_config];leaves=[];names=[];data=proof=card=0
 for view_path,job,stage,count in [(a.view_a,'ci-014497-4264b653','absnorm-support',19),(a.view_b,'ci-014507-f12c827f','finite-place',16)]:
  view,receipt,fields,paths=verify_leaf(view_path,job,stage,count,a.historical_config);all_paths+=paths
  for key in ['inventorySha256','graphSha256']:assert fields[key]==base[key]
  for row in fields['entries']:
   n=display(row['nameExpr']);assert n==row['name']
   if n==RING:continue
   assert n not in names;names.append(n)
   method=row['resolution']
   if n=='cardQuot_pow_of_prime':assert row['isProposition'] and method=='exact-original-type-native-theorem-proof';card+=1
   else:
    assert method=='genuine-original-complete-body'
    if row['isProposition']:proof+=1
    else:data+=1
  leaves.append({'viewPath':str(view_path.resolve()),'viewSha256':sha(view_path),'viewContents':view,
                 'receiptPath':view['receipt']['path'],'receiptSha256':view['receipt']['sha256'],'receiptContents':receipt})
 assert len(names)==35 and data==8 and proof==26 and card==1
 original_names=[r['nameExpr'] for leaf in leaves for r in leaf['viewContents']['sourceFields']['entries'] if r['name']!=RING]
 base['adicSourceCompatibility']={'schema':'tate-theta-adic-two-leaf-compatibility-v1','requiredOriginalNames':original_names,'leaves':leaves,
  'sourceDataCount':8,'genuineOriginalProofBodyCount':26,'nativeCardPowProofCount':1,'standardNativeProofCountIncludingRing':2,
  'unusedOriginalProofArchiveCount':15,'bindingPolicy':'Only complete, actually passed A19/B16 DAGs; full original artifacts including all diagnostic metadata remain hash-bound. No Expr metadata or data value changes.'}
 base['outputDir']=str(a.audit_output.resolve())
 all_paths=list(dict.fromkeys(Path(p).resolve() for p in all_paths))
 old={r['path']:r for r in base['inputEvidence']}
 for path in all_paths:old[str(path)]={'path':str(path),'sha256':sha(path)}
 base['inputEvidence']=list(old.values());base['auditJsonSerialization']='compact'
 dump(a.output,base)
 template=(HERE/'AuditNextCarriers.template.lean').read_text();header='import Lean\n'
 header+=''.join('import '+m+'\n' for m in base['auditorStandardImports'])
 header+=''.join('import '+display(m)+'\n' for m in base['allowedDependencyModules'])
 header+=''.join('import '+row['target']+'\n' for row in base['modules'])
 final=' ]).pretty ++ "\\n")'
 # Match the one final output serializer; ppExpr display formatting is unchanged.
 marker=']).pretty ++ "\\n")';assert template.count(marker)==1
 template=template.replace(marker,']).compress ++ "\\n")')
 (HERE/'AuditNextCarriers.lean').write_text(header+'\n'+template[template.index('/-! Stable JSON'):])
 print(json.dumps({'config':str(a.output),'bytes':a.output.stat().st_size,'sourceCompatibility':35,'genuineData':8,'genuineProofBodies':26,'nativeStandardProofs':2,'publicNamed':77,'genuineProjectProofValues':1,'compiled':False}))
if __name__=='__main__':main()
