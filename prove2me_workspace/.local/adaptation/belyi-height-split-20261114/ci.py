from pathlib import Path
import importlib.util
b=Path('/home/admin-wsl/Coq/abc/prove2me_workspace/.local/adaptation/belyi-height-split-20261114')
spec=importlib.util.spec_from_file_location('scheduler',b/'scheduler_common.py');ci=importlib.util.module_from_spec(spec);spec.loader.exec_module(ci)
run=ci.run
if __name__=='__main__':
    f='Solutions/Source_FermatBelyiHeightComparison.lean';run('composer-source-leaf',f);run('composer-source-artifact',f,artifact=True)
    for n in ['canonicalCuspPolarLinearEquivalence','polarPresentationHeightSum_of_principalRelation']:
        f='Theorems/Thm_AbcAdaptation_Tripod_Fermat_Proper_'+n+'.lean';run(n+'-leaf',f);run(n+'-artifact',f,artifact=True)
    f='Theorems/Thm_AbcAdaptation_Tripod_Fermat_Proper_belyiHeightRelation.lean';run('belyiHeightRelation-leaf',f);run('belyiHeightRelation-artifact',f,artifact=True)
    run('closed-axioms-review','Solutions/Checks_FermatBelyiHeightClosed.lean','review')
    run('reduction-axioms-leaf','Solutions/Checks_FermatBelyiHeightReduction.lean')
