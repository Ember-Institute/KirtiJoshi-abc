from pathlib import Path
import importlib.util
b=Path('/home/admin-wsl/Coq/abc/prove2me_workspace/.local/adaptation/canonical-cusp-split-20261114')
spec=importlib.util.spec_from_file_location('scheduler',b/'scheduler_common.py');ci=importlib.util.module_from_spec(spec);spec.loader.exec_module(ci)
run=ci.run
if __name__=='__main__':
    f='Solutions/Source_FermatCanonicalCuspComposition.lean';run('composer-source-leaf',f);run('composer-source-artifact',f,artifact=True)
    for n in ['canonicalDifferentialChange', 'belyiCanonicalCuspCoefficientIdentity']:
        f='Theorems/Thm_AbcAdaptation_Tripod_Fermat_Proper_'+n+'.lean';run(n+'-leaf',f);run(n+'-artifact',f,artifact=True)
    f='Theorems/Thm_AbcAdaptation_Tripod_Fermat_Proper_canonicalCuspPolarLinearEquivalence.lean';run('canonicalCuspPolarLinearEquivalence-leaf',f);run('canonicalCuspPolarLinearEquivalence-artifact',f,artifact=True)
    run('closed-axioms-review','Solutions/Checks_FermatCanonicalCuspClosed.lean','review')
    run('reduction-axioms-leaf','Solutions/Checks_FermatCanonicalCuspReduction.lean')
