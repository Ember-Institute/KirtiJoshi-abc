from pathlib import Path
import importlib.util
s=importlib.util.spec_from_file_location('ci','/tmp/p2m-riemann-sourceproof-ci-20261114.py');ci=importlib.util.module_from_spec(s);s.loader.exec_module(ci)
ci.b=ci.w/'.local/adaptation/derivative-finite-sourceproof-20261114';ci.base['session_id']='p2m-derivative-finite-sourceproof-20261114'
if __name__=='__main__':
 for n in ['FermatCurveDerivationAdjoin','FermatCurveDerivationLocalization']:
  f='Definitions/Def_'+n+'.lean';ci.run(n+'-leaf',f,version='derivative-proof-v1');ci.run(n+'-artifact',f,artifact=True,version='derivative-proof-v1')
 f='Theorems/Thm_AbcAdaptation_Tripod_Fermat_Proper_noncriticalDerivativeBadPlacesFinite.lean';ci.run('noncriticalDerivativeBadPlacesFinite-leaf',f,memory='6GiB',version='derivative-proof-v1');ci.run('noncriticalDerivativeBadPlacesFinite-artifact',f,artifact=True,version='derivative-proof-v1')
 ci.run('closed-axioms-review','Solutions/Checks_FermatDerivativeFiniteLocalization.lean','review',memory='8GiB',version='derivative-proof-v1')
