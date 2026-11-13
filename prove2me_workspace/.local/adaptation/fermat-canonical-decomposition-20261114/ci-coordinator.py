from pathlib import Path
import json,importlib.util
s=importlib.util.spec_from_file_location('ci','/tmp/p2m-riemann-sourceproof-ci-20261114.py');ci=importlib.util.module_from_spec(s);s.loader.exec_module(ci)
ci.b=ci.w/'.local/adaptation/fermat-canonical-decomposition-20261114';ci.base['session_id']='p2m-fermat-canonical-decomposition-20261114'
# The reused submit helper binds the complete source hash in a fresh evidence directory.
run=ci.run
if __name__=='__main__':
 for n in ['FermatInfinityDivisorFiniteSupport','FermatCanonicalCoordinatePoleComposition']:
  f='Definitions/Def_'+n+'.lean';run(n+'-leaf',f);run(n+'-artifact',f,artifact=True)
 for n in ['coordinatePoleMultiplicity_eq','infinityDivisorExists','canonicalDivisorDegree']:
  f='Theorems/Thm_AbcAdaptation_Tripod_Fermat_Proper_'+n+'.lean';run(n+'-leaf',f,memory='6GiB' if n in ['infinityDivisorExists','canonicalDivisorDegree'] else '16GiB');run(n+'-artifact',f,artifact=True)
 run('closed-axioms-review','Solutions/Checks_FermatCanonicalCoordinateClosed.lean','review',memory='8GiB')
 run('reduction-axioms-leaf','Solutions/Checks_FermatCanonicalCoordinateReduction.lean',memory='16GiB')
 x=json.loads((ci.b/'reduction-axioms-leaf-result.json').read_text());assert 'sorryAx' in x['result']['stdout']
 print('Canonical-coordinate leaves, closed Infinity proof, and explicit Open-child reduction checks passed.',flush=True)
