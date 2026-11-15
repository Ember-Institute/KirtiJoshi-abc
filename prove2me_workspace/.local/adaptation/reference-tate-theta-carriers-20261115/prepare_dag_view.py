#!/usr/bin/env python3
"""Extract the exact DAG/entry fields from a passed split artifact in bounded space.
The full original artifact remains the receipt/hash-bound archive. No Expr node changes.
"""
import argparse,hashlib,json,mmap,re
from pathlib import Path

def sha(path):
 h=hashlib.sha256()
 with Path(path).open('rb') as f:
  for b in iter(lambda:f.read(1024*1024),b''):h.update(b)
 return h.hexdigest()

def top_fields(data):
 token=re.compile(rb'"(?:[^"\\]|\\.)*"|[{}\[\]]')
 depth=0;current=None;starts={};ends={}
 for match in token.finditer(data):
  c=data[match.start()]
  if c==34:
   if depth==1 and data[match.end():match.end()+1]==b':':
    if current is not None:
     end=match.start()
     while end and data[end-1] in b' \r\n\t':end-=1
     if data[end-1]==44:end-=1
     ends[current]=end
    current=json.loads(match[0]);starts[current]=match.end()+1
   continue
  if c in (123,91):depth+=1
  else:
   depth-=1
   if depth==0:
    if current is not None:ends[current]=match.start()
    break
 return {key:(starts[key],ends[key]) for key in starts}

def extract(data,key,locations):
 pos,end=locations[key]
 raw=data[pos:end]
 return json.loads(raw), {'start':pos,'end':end,'sha256':hashlib.sha256(raw).hexdigest()}

p=argparse.ArgumentParser();p.add_argument('--artifact',type=Path,required=True);p.add_argument('--receipt',type=Path,required=True);p.add_argument('--out',type=Path,required=True);a=p.parse_args()
r=json.loads(a.receipt.read_text());assert r['status']=='succeeded' and r['result']['exit_code']==0
assert r['resources']['peak_rss_bytes'] is not None and r['resources']['peak_rss_bytes']<=16*1024**3
assert r['request']['exclusive'] is True and r['result']['snapshot']['workspace_mode']=='exclusive_worktree' and r['result']['snapshot']['snapshot_id'] is None
fields=['schema','stage','inventorySha256','graphSha256','candidateOriginalRecordCount','allActiveOriginalRecordCount','stageOriginalRecordCount','stageOriginalRecordNames','unusedArchivedCandidateNames','standardProofOverrideCount','entries','exprDag','allCompleteTypeValueKernelChecksPassed','allExprDagRootsStrictExprEqualRoundTrip','roundTripIncludesBinderNamesBinderInfoAndNumericNames']
values={};spans={}
with a.artifact.open('rb') as f,mmap.mmap(f.fileno(),0,access=mmap.ACCESS_READ) as data:
 locations=top_fields(data)
 for key in fields:values[key],spans[key]=extract(data,key,locations)
assert values['schema']=='tate-theta-adic-split-expr-dag-v1'
assert values['allCompleteTypeValueKernelChecksPassed'] and values['allExprDagRootsStrictExprEqualRoundTrip']
assert values['allActiveOriginalRecordCount']==35 and values['candidateOriginalRecordCount']==50
view={'schema':'tate-theta-adic-receipt-bound-dag-view-v1','originalArtifact':{'path':str(a.artifact.resolve()),'sha256':sha(a.artifact)},'receipt':{'path':str(a.receipt.resolve()),'sha256':sha(a.receipt),'job_id':r['job_id']},'sourceFields':values,'exactFieldByteSpans':spans,'preservation':'Complete entries and expression DAG parsed from exact original field bytes. Full original artifact including all Binder diagnostics retained and hash-bound; no Expr/name/binder/value change.'}
a.out.write_text(json.dumps(view,ensure_ascii=False,separators=(',',':'))+'\n');print(json.dumps({'out':str(a.out),'bytes':a.out.stat().st_size,'stage':values['stage'],'entries':len(values['entries']),'nodes':len(values['exprDag']['nodes']),'sha256':sha(a.out)}))
