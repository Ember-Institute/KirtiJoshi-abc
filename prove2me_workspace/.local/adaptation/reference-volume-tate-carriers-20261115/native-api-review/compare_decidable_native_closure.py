#!/usr/bin/env python3
"""Compare actual exported APIs as syntax, with a precise expansion boundary.

This script does not claim kernel equality and never invokes a compiler.
"""
import argparse
import hashlib
import json
from pathlib import Path

HERE=Path(__file__).resolve().parent
B=Path('/home/admin-wsl/Coq/abc/prove2me_workspace/.local/adaptation/reference-volume-tate-carriers-20261115')
FORCED_SOURCE_BODIES={'Bool.Reflects','Bool.Reflects.match_1','Nat.instDecidableCoprime._proof_1','Nat.decEq._proof_1','Nat.decEq.match_1'}
EXTRA_NATIVE_APIS=['Decidable','Decidable.decide','Bool.rec','Decidable.isFalse','Decidable.isTrue']

def load(p):return json.loads(Path(p).read_text())
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def name(n):return ((name(n[0])+'.') if n and n[0] else '')+str(n[2]) if n else ''
def normalized(j,params):
    if isinstance(j,dict):
        result={}
        for key,value in j.items():
            if key=='name' and j.get('kind') in {'forall','lam','let'}:continue
            if key=='name' and j.get('kind')=='param':result[key]=params.get(name(value),name(value))
            else:result[key]=normalized(value,params)
        return result
    if isinstance(j,list):return [normalized(value,params) for value in j]
    return j

def normalized_type(record):return normalized(record['typeExpr'],{name(p):i for i,p in enumerate(record['levelParams'])})
def constants(j):
    if isinstance(j,dict):
        if j.get('kind') in {'const','proj'}:yield name(j['name'])
        for value in j.values():yield from constants(value)
    elif isinstance(j,list):
        for value in j:yield from constants(value)

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--unit-dir',type=Path,default=B)
    parser.add_argument('--output',type=Path,default=HERE/'decidable250-native-api-comparison.json')
    args=parser.parse_args()
    assert args.output.resolve().parent==HERE
    source_path=args.unit_dir/'decidable-standard-source-closure.json'
    native_path=args.unit_dir/'decidable-native-closure-api-facts.json'
    receipt_path=args.unit_dir/'decidable-native-closure-api-result.json'
    source_doc=load(source_path);native_doc=load(native_path);receipt=load(receipt_path)
    assert source_doc['compiler']=='4.35.0-rc3' and native_doc['compiler']=='4.33.1'
    assert receipt['job_id']=='ci-013962-60467000' and receipt['status']=='succeeded' and receipt['result']['exit_code']==0
    source={row['name']:row for row in source_doc['records']};native={row['name']:row for row in native_doc['records']}
    assert set(source)==set(native) and len(source)==source_doc['recordCount']==native_doc['sourceRecordCount']
    rows=[]
    for n,s in source.items():
        t=native[n]
        row={'name':n,'nativePresent':t['present'],'sourceKind':s['kind'],'sourceUniverseCount':len(s['levelParams'])}
        if t['present']:
            row.update(nativeKind=t['kind'],nativeUniverseCount=len(t['levelParams']),
                       kindSame=s['kind']==t['kind'],universeAritySame=len(s['levelParams'])==len(t['levelParams']),
                       alphaTypeSyntaxEqual=normalized_type(s)==normalized_type(t),
                       rawBinderInventorySame=s['binderInventory']==t['binderInventory'],
                       computationShapeSyntaxEqual=s['shape']==t['shape'])
        rows.append(row)
    by_name={row['name']:row for row in rows}
    seen=set();expanded={};leaves=set()
    def visit(n):
        if n in seen:return
        seen.add(n)
        if n not in source:
            leaves.add(n);return
        if native[n]['present'] and n not in FORCED_SOURCE_BODIES:
            leaves.add(n);return
        dependencies=sorted(set(constants(source[n]['typeExpr']))|set(constants(source[n]['valueExpr'])))
        expanded[n]=dependencies
        for dependency in dependencies:visit(dependency)
    for root in ['Bool.Reflects','Nat.instDecidableCoprime._proof_1']:visit(root)
    assert set(expanded)==FORCED_SOURCE_BODIES
    leaf_reports=[by_name[n] for n in sorted(leaves)]
    risks=[r for r in leaf_reports if not r['nativePresent'] or not all(r.get(k,False) for k in ['kindSame','universeAritySame','alphaTypeSyntaxEqual','rawBinderInventorySame','computationShapeSyntaxEqual'])]
    extra_reports=[by_name[n] for n in EXTRA_NATIVE_APIS]
    assert all(r['nativePresent'] and r['alphaTypeSyntaxEqual'] and r['universeAritySame'] for r in extra_reports)
    result={'schema':'decidable250-actual-native-api-static-comparison-v1',
            'status':'all-effective-native-leaf-api-types-alpha-syntactically-identical',
            'comparisonIsKernelEqualityProof':False,
            'scope':'Only the effective source proof/matcher expansions under the exact v6 Nat.decEq.match_1 exception. Existing native declaration bodies are not recursively expanded.',
            'sourceCount':len(source),'nativePresentCount':sum(r['nativePresent'] for r in rows),
            'missingNames':[r['name'] for r in rows if not r['nativePresent']],
            'universeArityDifferences':[r for r in rows if r['nativePresent'] and not r['universeAritySame']],
            'kindDifferences':[r for r in rows if r['nativePresent'] and not r['kindSame']],
            'alphaTypeSyntaxDifferences':[r['name'] for r in rows if r['nativePresent'] and not r['alphaTypeSyntaxEqual']],
            'computationShapeSyntaxDifferences':[r['name'] for r in rows if r['nativePresent'] and not r['computationShapeSyntaxEqual']],
            'effectiveSourceExpansions':expanded,'nativeBoundary':leaf_reports,'nativeBoundaryRisks':risks,
            'constructorTransportNativeAPIs':extra_reports,
            'recommendation':'Run the exact v6 kernel audit; do not expand unrelated standard differences or add further exceptions based on this static report.',
            'rows':rows,
            'evidence':[{'path':str(p.resolve()),'sha256':sha(p)} for p in [source_path,native_path,receipt_path]],
            'nativeQueryResources':receipt['resources'],
            'subagentCompiledOrCalledCI':False}
    assert not risks
    args.output.write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n')
    print(json.dumps({k:result[k] for k in ['status','sourceCount','nativePresentCount','missingNames','alphaTypeSyntaxDifferences','computationShapeSyntaxDifferences','nativeBoundaryRisks']},indent=2))

if __name__=='__main__':main()
