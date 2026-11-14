from pathlib import Path
import json,importlib.util
s=importlib.util.spec_from_file_location('ci','/tmp/p2m-riemann-sourceproof-ci-20261114.py');ci=importlib.util.module_from_spec(s);s.loader.exec_module(ci)
ci.b=ci.w/'.local/adaptation/epsilon-large-height-sourceproof-20261114';ci.base['session_id']='p2m-epsilon-large-height-sourceproof-20261114'
original_rpc=ci.rpc
def rpc(name,args):
 for attempt in range(3):
  try:return original_rpc(name,args)
  except (TimeoutError,ConnectionError,OSError):
   if attempt==2:raise
   print('Retrying observation of the same scheduler request.',flush=True)
ci.rpc=rpc
pre='AbcAdaptation.Tripod.';target=pre+'epsilonELargeHeight';source='Theorems/Thm_'+target.replace('.','_')+'.lean';u='.local/adaptation/epsilon-large-height-sourceproof-20261114/'
def run(*a,**kw):
 kw.setdefault('version','epsilon-source-v1');return ci.run(*a,**kw)
if __name__=='__main__':
 run('epsilonELargeHeight-leaf',source,memory='6GiB');run('epsilonELargeHeight-artifact',source,artifact=True)
 run('closed-axioms-review','Solutions/Checks_TripodEpsilonLargeHeight.lean','review')
 run('source-graph-leaf',u+'ExtractEpsilonProofGraph.lean')
