from pathlib import Path
import importlib.util,sys
s=importlib.util.spec_from_file_location('ci','/tmp/p2m-riemann-sourceproof-ci-20261114.py');ci=importlib.util.module_from_spec(s);s.loader.exec_module(ci)
ci.b=ci.w/'.local/adaptation/northcott-sourceproof-20261114';ci.base['session_id']='p2m-northcott-sourceproof-20261114'
pre='AbcAdaptation.Tripod.'
new_names=['Northcott.norm_embedding_le_mulHeight_one','Northcott.mulHeight_one_gen_le','Northcott.coeff_minpoly_int_mem_Icc','northcottFiniteRoots','northcottPolynomialWitness']
def run(*args,**kw):
 kw.setdefault('version','northcott-v1');return ci.run(*args,**kw)
if __name__=='__main__':
 for mod in ['TripodNorthcottInputs','TripodNorthcottComposition']:
  f='Definitions/Def_'+mod+'.lean';run(mod+'-leaf',f);run(mod+'-artifact',f,artifact=True)
 for i,name in enumerate(new_names+['boundedDegreeFiniteness']):
  f='Theorems/Thm_'+(pre+name).replace('.','_')+'.lean';run(name+'-leaf',f,**({'memory':'6GiB'} if i==5 else {}));run(name+'-artifact',f,artifact=True)
 run('closed-axioms-review','Solutions/Checks_TripodNorthcottSourceProofs.lean','review')
 run('source-graph-leaf','.local/adaptation/northcott-sourceproof-20261114/ExtractNorthcottProofGraph.lean')
