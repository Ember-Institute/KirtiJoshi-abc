from pathlib import Path
import importlib.util
b=Path('/home/admin-wsl/Coq/abc/prove2me_workspace/.local/adaptation/local-compactness-sourceproof-20261114')
spec=importlib.util.spec_from_file_location('scheduler',b/'scheduler_common.py');ci=importlib.util.module_from_spec(spec);spec.loader.exec_module(ci)
run=ci.run
if __name__=='__main__':
    names=['FermatLocalSequence', 'FermatLocalProjectiveConvergence', 'FermatLocalValuedPlace', 'FermatLocalLimitValuation', 'FermatLocalCompactnessBridge', 'FermatLocalCompactness']
    for n in names:
        f='Solutions/Source_'+n+'.lean'
        if n=='FermatLocalCompactnessBridge':run(n+'-leaf',f,memory='6GiB')
        else:run(n+'-leaf',f)
        run(n+'-artifact',f,artifact=True)
    f='Theorems/Thm_AbcAdaptation_Tripod_Fermat_Proper_localCompactness.lean'
    run('localCompactness-leaf',f);run('localCompactness-artifact',f,artifact=True)
    run('closed-axioms-review','Solutions/Checks_FermatLocalCompactness.lean','review')
