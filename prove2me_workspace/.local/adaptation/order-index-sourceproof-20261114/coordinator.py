from pathlib import Path
import importlib.util,json,sys
s=importlib.util.spec_from_file_location('ci','/tmp/p2m-riemann-sourceproof-ci-20261114.py');ci=importlib.util.module_from_spec(s);s.loader.exec_module(ci)
ci.b=ci.w/'.local/adaptation/order-index-sourceproof-20261114';ci.base['session_id']='p2m-order-index-sourceproof-20261114'
ci.base['worktree_manifest']['input_version']='order-index-sourceproof-20261114'
names=['noncriticalPolynomialOrderAtRegularPoint','noncriticalPolynomialOrderAtPole','noncriticalInverseRamification']
def run(*a,**kw):
 kw.setdefault('version','order-proof-v1');return ci.run(*a,**kw)
if __name__=='__main__':
 phase=sys.argv[1] if len(sys.argv)>1 else 'proof'
 if phase=='proof':
  f='Definitions/Def_FermatNoncriticalOrderSource.lean';run('FermatNoncriticalOrderSource-leaf',f);run('FermatNoncriticalOrderSource-artifact',f,artifact=True)
  for n in names:
   f='Theorems/Thm_AbcAdaptation_Tripod_Fermat_Proper_'+n+'.lean';run(n+'-leaf',f,memory='6GiB');run(n+'-artifact',f,artifact=True)
  run('closed-axioms-review','Solutions/Checks_FermatOrderIndexSourceProofs.lean','review')
  run('source-graph-leaf','.local/adaptation/order-index-sourceproof-20261114/ExtractOrderIndexProofGraph.lean')
