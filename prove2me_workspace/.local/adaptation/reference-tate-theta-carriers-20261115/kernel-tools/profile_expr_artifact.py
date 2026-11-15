#!/usr/bin/env python3
"""Profile original-export JSON without materializing its Expr trees."""
import argparse, hashlib, json, mmap, re, time
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('source',type=Path);p.add_argument('--out',type=Path,required=True);a=p.parse_args()
started=time.monotonic()
token=re.compile(rb'"(?:[^"\\]|\\.)*"|[{}\[\]]')
rows=[]
with a.source.open('rb') as f, mmap.mmap(f.fileno(),0,access=mmap.ACCESS_READ) as data:
    start=re.search(rb'"records"\s*:\s*\[',data)
    if start is None:raise ValueError('Missing records array')
    depth=1;row=None;last_field=None;key_pattern=re.compile(rb'\s*:')
    for m in token.finditer(data,start.end()):
        kind=data[m.start()]
        if kind==34:
            if depth==2 and key_pattern.match(data,m.end()):
                field=json.loads(m[0])
                if last_field is not None:row['fieldBytes'][last_field]=m.start()-row['fieldOffsets'][last_field]
                row['fieldOffsets'][field]=m.start();last_field=field
                if field in {'name','module','selected','constantKind','isProposition'}:
                    value_pos=key_pattern.match(data,m.end()).end()
                    chunk=data[value_pos:value_pos+2048].lstrip()
                    row[field]=json.JSONDecoder().raw_decode(chunk.decode('utf-8'))[0]
            continue
        if kind in (123,91):
            if depth==1:
                if kind!=123:raise ValueError('Expected record object')
                row={'offset':m.start(),'fieldOffsets':{},'fieldBytes':{}};last_field=None
            depth+=1
        else:
            depth-=1
            if depth==1:
                row['endOffset']=m.end();row['bytes']=m.end()-row['offset']
                if last_field is not None:row['fieldBytes'][last_field]=m.start()-row['fieldOffsets'][last_field]
                del row['fieldOffsets'];rows.append(row);row=None
            elif depth==0:break
    assert len(rows)==117
    file_sha=hashlib.sha256(data).hexdigest()
by_module={}
for r in rows:
    x=by_module.setdefault(r['module'],{'allRecords':0,'selectedRecords':0,'bytes':0,'selectedBytes':0,'largestRecords':[]})
    x['allRecords']+=1;x['selectedRecords']+=int(r['selected']);x['bytes']+=r['bytes'];x['selectedBytes']+=r['bytes'] if r['selected'] else 0;x['largestRecords'].append({'name':r['name'],'selected':r['selected'],'bytes':r['bytes']})
for x in by_module.values():x['largestRecords']=sorted(x['largestRecords'],key=lambda r:r['bytes'],reverse=True)[:8]
report={'schema':'tate-theta-original-expr-artifact-size-profile-v1','method':'mmap lexical structural scan; no full json.loads and no Lean compilation','source':str(a.source.resolve()),'sourceBytes':a.source.stat().st_size,'sourceSha256':file_sha,'recordCount':len(rows),'selectedCount':sum(r['selected'] for r in rows),'scanWallSeconds':time.monotonic()-started,'modules':by_module,'records':rows}
a.out.write_text(json.dumps(report,ensure_ascii=False,indent=2)+'\n')
print(json.dumps({k:report[k] for k in ['sourceBytes','recordCount','selectedCount','scanWallSeconds','modules']},ensure_ascii=False))
