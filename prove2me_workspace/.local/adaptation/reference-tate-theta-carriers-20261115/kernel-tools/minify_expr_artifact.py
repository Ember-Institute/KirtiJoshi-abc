#!/usr/bin/env python3
"""Create and verify a lossless JSON whitespace view without loading JSON trees."""
import argparse,hashlib,json,mmap,re,time
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('source',type=Path);p.add_argument('--out',type=Path,required=True);p.add_argument('--acceptance',type=Path,required=True);p.add_argument('--report',type=Path,required=True);p.add_argument('--verify-existing',action='store_true');a=p.parse_args()
assert a.source.resolve()!=a.out.resolve()
assert a.verify_existing == a.out.exists()
started=time.monotonic();token=re.compile(rb'"(?:[^"\\]|\\.)*"|[^\s"]+')
if not a.verify_existing:
    with a.source.open('rb') as f,mmap.mmap(f.fileno(),0,access=mmap.ACCESS_READ) as data,a.out.open('wb') as output:
        for m in token.finditer(data):
            output.write(m[0])
# Compare actual JSON tokens, each punctuation mark separately. Whitespace may
# separate punctuation in the source without changing the token boundaries.
token=re.compile(rb'"(?:[^"\\]|\\.)*"|[{}\[\]:,]|-?(?:0|[1-9][0-9]*)(?:\.[0-9]+)?(?:[eE][+-]?[0-9]+)?|true|false|null')
# Verify every complete token rather than relying on a hash alone. This keeps all
# string escape spelling, numbers, object/array order, and punctuation unchanged.
with a.source.open('rb') as f,a.out.open('rb') as g,mmap.mmap(f.fileno(),0,access=mmap.ACCESS_READ) as raw,mmap.mmap(g.fileno(),0,access=mmap.ACCESS_READ) as compact:
    rawsha=hashlib.sha256(raw).hexdigest()
    left=token.finditer(raw);right=token.finditer(compact);checked=0
    while True:
        l=next(left,None);r=next(right,None)
        if l is None or r is None:
            assert l is None and r is None;break
        assert l[0]==r[0],('JSON token mismatch',checked)
        checked+=1
    compactsha=hashlib.sha256(compact).hexdigest()
    compact_bytes=len(compact)
    del l,r,left,right
acceptance=json.loads(a.acceptance.read_text());assert acceptance['status']=='accepted' and acceptance['originalExprsSha256']==rawsha
profile_path=Path(__file__).resolve().parent/'original-exprs-size-profile.json'
profile=json.loads(profile_path.read_text());assert profile['sourceSha256']==rawsha and profile['recordCount']==117 and profile['selectedCount']==78
report={'schema':'tate-theta-lossless-original-exprs-compact-view-v1','status':'lossless-serialization-view-not-new-compiler-evidence','raw':{'path':str(a.source.resolve()),'bytes':a.source.stat().st_size,'sha256':rawsha},'compact':{'path':str(a.out.resolve()),'bytes':compact_bytes,'sha256':compactsha},'sourceAcceptance':{'path':str(a.acceptance.resolve()),'sha256':hashlib.sha256(a.acceptance.read_bytes()).hexdigest()},'recordCount':117,'selectedCount':78,'preservation':{'completeLexicalTokenStreamsCompared':True,'identicalTokenCount':checked,'onlyWhitespaceOutsideJsonStringsRemoved':True,'allExprNameBinderMetadataAndRecordValuesUnchanged':True,'parsedJsonEquality':True,'parsedJsonEqualityMethod':'Identical complete JSON lexical token streams preserve the parse of the source JSON already validated by its accepted original-export artifact receipt. String literals, escape spelling, numbers, punctuation, record order and every field are byte-identical tokens.','fullJsonLoadsEqualityPerformed':False},'wallSeconds':time.monotonic()-started}
a.report.write_text(json.dumps(report,ensure_ascii=False,indent=2)+'\n');print(json.dumps(report,ensure_ascii=False))
