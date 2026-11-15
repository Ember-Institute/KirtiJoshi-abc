#!/usr/bin/env python3
"""Bind exact term-owner candidates plus the retained original context owners."""
import argparse,copy,json
from pathlib import Path
from carrier_contract import MODULES,load,sha,require,dependency_evidence,unit_config,validate_import_graph
TASK=Path(__file__).resolve().parent
CONTEXT={'TateCurvesTheta.TateCurve.JInvariant':['Mathlib.Topology.MetricSpace.Ultra.Basic'],
         'TateCurvesTheta.TateCurve.Parametrization':['Mathlib.Topology.MetricSpace.Ultra.Basic']}
def main():
 p=argparse.ArgumentParser(description=__doc__)
 for n in ['imports','unit-config','out']:p.add_argument('--'+n,required=True)
 a=p.parse_args();out=Path(a.out).resolve();require(out==TASK or TASK in out.parents,'Output outside unit')
 rows=copy.deepcopy(load(a.imports));require({r['module']for r in rows}==set(MODULES),'Import module set differs')
 _,prior,_=dependency_evidence(unit_config(a.unit_config));plans=[]
 for r in rows:
  for name in CONTEXT.get(r['module'],[]):
   for key in ['source435Imports','platform433Candidates']:
    if name not in r[key]:r[key].append(name)
  plans.append({k:r[k]for k in ['module','source435Imports','platform433Candidates']})
 validate_import_graph({r['module']:r for r in plans},prior)
 out.mkdir(parents=True,exist_ok=True);candidate=out/'imports.json';candidate.write_text(json.dumps(rows,ensure_ascii=False,indent=2)+'\n')
 review={'schema':'foundation-precise-import-review-v1','status':'reviewed','importsCandidateSha256':sha(candidate),'modules':plans,
 'reviewNote':'Exact term-owner candidates plus Ultra.Basic for the retained IsUltrametricDist variables in JInvariant and Parametrization. All original contexts survive; no source aggregate or monolithic Mathlib import. Compilation gates remain pending.',
 'contextOwners':CONTEXT}
 (out/'precise-import-review.json').write_text(json.dumps(review,ensure_ascii=False,indent=2)+'\n')
 print(json.dumps({'status':'precise-import-plan-prepared-needs-compiler-gates','modules':len(plans),'candidateSha256':sha(candidate)}))
if __name__=='__main__':main()
