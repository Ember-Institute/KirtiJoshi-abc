from scheduler_common import run
if __name__ == "__main__":
    f='Solutions/Source_FermatDivisorTupleEquivalence.lean'
    run('FermatDivisorTupleEquivalence'+"-leaf",f)
    run('FermatDivisorTupleEquivalence'+"-artifact",f,artifact=True)
    f='Solutions/Source_FermatPositiveDegreePolar.lean'
    run('FermatPositiveDegreePolar'+"-leaf",f,version='zsmul-v3',duration='53s',memory='6GiB')
    run('FermatPositiveDegreePolar'+"-artifact",f,artifact=True)
    f='Solutions/Source_FermatDivisorHeightMachine.lean'
    run('FermatDivisorHeightMachine'+"-leaf",f,version='unfold-v2',duration='63s',memory='6GiB')
    run('FermatDivisorHeightMachine'+"-artifact",f,artifact=True)
    f='Solutions/Source_FermatDivisorDegreeHeightComparison.lean'
    run('FermatDivisorDegreeHeightComparison'+"-leaf",f,version='instance-v2',duration='53s',memory='6GiB')
    run('FermatDivisorDegreeHeightComparison'+"-artifact",f,artifact=True)
    f='Theorems/Thm_AbcAdaptation_Tripod_Fermat_Proper_divisorDegreeHeightComparison.lean'
    run('Thm_AbcAdaptation_Tripod_Fermat_Proper_divisorDegreeHeightComparison'+"-leaf",f)
    run('Thm_AbcAdaptation_Tripod_Fermat_Proper_divisorDegreeHeightComparison'+"-artifact",f,artifact=True)
    run("closed-axioms-review",'Solutions/Checks_FermatDivisorDegreeHeightComparison.lean',"review")
