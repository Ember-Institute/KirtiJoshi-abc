from scheduler_common import run
if __name__ == "__main__":
    f='Solutions/Source_FermatDifferentialChain.lean'
    run('FermatDifferentialChain'+"-leaf",f)
    run('FermatDifferentialChain'+"-artifact",f,artifact=True)
    f='Solutions/Source_FermatDifferentialOrder.lean'
    run('FermatDifferentialOrder'+"-leaf",f)
    run('FermatDifferentialOrder'+"-artifact",f,artifact=True)
    f='Solutions/Source_FermatCanonicalDifferentialChange.lean'
    run('FermatCanonicalDifferentialChange'+"-leaf",f)
    run('FermatCanonicalDifferentialChange'+"-artifact",f,artifact=True)
    f='Theorems/Thm_AbcAdaptation_Tripod_Fermat_Proper_canonicalDifferentialChange.lean'
    run('Thm_AbcAdaptation_Tripod_Fermat_Proper_canonicalDifferentialChange'+"-leaf",f)
    run('Thm_AbcAdaptation_Tripod_Fermat_Proper_canonicalDifferentialChange'+"-artifact",f,artifact=True)
    run("closed-axioms-review","Solutions/Checks_FermatCanonicalDifferentialChange.lean","review")
