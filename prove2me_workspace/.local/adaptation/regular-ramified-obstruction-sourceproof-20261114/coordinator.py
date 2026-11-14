from pathlib import Path
import importlib.util,json,sys
sp=importlib.util.spec_from_file_location('ci','/tmp/p2m-riemann-sourceproof-ci-20261114.py');ci=importlib.util.module_from_spec(sp);sp.loader.exec_module(ci)
_original_rpc=ci.rpc
def resilient_rpc(name,args):
 for attempt in range(3):
  try:return _original_rpc(name,args)
  except (TimeoutError,ConnectionError,OSError):
   if attempt==2:raise
   print('Transport observation failed; retrying same scheduler request without new job.',flush=True)
ci.rpc=resilient_rpc
ci.b=ci.w/'.local/adaptation/regular-ramified-obstruction-sourceproof-20261114';ci.base['session_id']='p2m-regular-ramified-obstruction-sourceproof-20261114';dag=json.loads((ci.b/'canonical-import-dag.json').read_text());names=dag['topological_order'];target='AbcAdaptation.Tripod.Fermat.Proper.noncriticalRegularRamifiedDerivNotMem'
def run(*args,**kw):
 kw.setdefault('version','obstruction-v6');return ci.run(*args,**kw)
if __name__=='__main__':
 f='Definitions/Def_FermatCurveFieldUniformizer.lean';run('FermatCurveFieldUniformizer-leaf',f);run('FermatCurveFieldUniformizer-artifact',f,artifact=True)
 for n in names:
  f='Theorems/Thm_'+n.replace('.','_')+'.lean';tag=n.removeprefix('AbcAdaptation.Tripod.Fermat.Proper.');run(tag+'-leaf',f,**({'memory':'6GiB'} if n==target else {'duration':'240s','memory':'6GiB'} if n.endswith('exists_pow_mul_derivAlong_mem_integralClosure') else {}));run(tag+'-artifact',f,artifact=True)
 run('closed-axioms-review','Solutions/Checks_FermatRegularRamifiedObstruction.lean','review')
 run('source-graph-leaf','.local/adaptation/regular-ramified-obstruction-sourceproof-20261114/ExtractObstructionProofGraph.lean')
