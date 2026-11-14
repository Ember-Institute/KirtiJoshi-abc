from pathlib import Path
import importlib.util, sys
b=Path('/home/admin-wsl/Coq/abc/prove2me_workspace/.local/adaptation/embedding-bounds-sourceproof-20261114')
spec=importlib.util.spec_from_file_location('scheduler',b/'scheduler_common.py');ci=importlib.util.module_from_spec(spec);spec.loader.exec_module(ci)
run=ci.run
if __name__=='__main__':
    names=['TripodLocalPlaceEmbeddingBasic','TripodLocalPlaceEmbeddingDegree','TripodLocalPlaceEmbedding','TripodLocalEmbeddingBounds','FermatEmbeddingBoundsSource']
    for n in names:
        f='Solutions/Source_'+n+'.lean';run(n+'-leaf',f);run(n+'-artifact',f,artifact=True)
    f='Theorems/Thm_AbcAdaptation_Tripod_Fermat_Proper_embeddingBoundsToSet.lean'
    run('embeddingBoundsToSet-leaf',f);run('embeddingBoundsToSet-artifact',f,artifact=True)
    run('closed-axioms-review','Solutions/Checks_FermatEmbeddingBounds.lean','review')
