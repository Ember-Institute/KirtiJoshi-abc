from scheduler_common import run
if __name__ == "__main__":
    f='Definitions/Def_FermatBelyiDifferentConductorChildren.lean'
    run('FermatBelyiDifferentConductorChildren'+"-leaf",f)
    run('FermatBelyiDifferentConductorChildren'+"-artifact",f,artifact=True)
    f='Solutions/Source_FermatBelyiDifferentConductorAdapters.lean'
    run('FermatBelyiDifferentConductorAdapters'+"-leaf",f,version='discriminant-transport-v2',duration='51s',memory='6GiB')
    run('FermatBelyiDifferentConductorAdapters'+"-artifact",f,artifact=True)
    f='Theorems/Thm_AbcAdaptation_Tripod_Fermat_Proper_belyiActualFieldConductorExtension.lean'
    run('Thm_AbcAdaptation_Tripod_Fermat_Proper_belyiActualFieldConductorExtension'+"-leaf",f)
    run('Thm_AbcAdaptation_Tripod_Fermat_Proper_belyiActualFieldConductorExtension'+"-artifact",f,artifact=True)
    f='Theorems/Thm_AbcAdaptation_Tripod_Fermat_Proper_belyiActualFieldDifferentTower.lean'
    run('Thm_AbcAdaptation_Tripod_Fermat_Proper_belyiActualFieldDifferentTower'+"-leaf",f)
    run('Thm_AbcAdaptation_Tripod_Fermat_Proper_belyiActualFieldDifferentTower'+"-artifact",f,artifact=True)
    f='Theorems/Thm_AbcAdaptation_Tripod_Fermat_Proper_tripodGeneratorConductorIdentity.lean'
    run('Thm_AbcAdaptation_Tripod_Fermat_Proper_tripodGeneratorConductorIdentity'+"-leaf",f,version='bad-place-membership-v2',duration='64s',memory='6GiB')
    run('Thm_AbcAdaptation_Tripod_Fermat_Proper_tripodGeneratorConductorIdentity'+"-artifact",f,artifact=True)
    f='Theorems/Thm_AbcAdaptation_Tripod_Fermat_Proper_belyiDifferentConductorComparison.lean'
    run('Thm_AbcAdaptation_Tripod_Fermat_Proper_belyiDifferentConductorComparison'+"-leaf",f)
    run('Thm_AbcAdaptation_Tripod_Fermat_Proper_belyiDifferentConductorComparison'+"-artifact",f,artifact=True)
    run("closed-axioms-review",'Solutions/Checks_FermatBelyiDifferentConductorClosed.lean',"review")
    run("reduction-axioms-leaf",'Solutions/Checks_FermatBelyiDifferentConductorReduction.lean')
