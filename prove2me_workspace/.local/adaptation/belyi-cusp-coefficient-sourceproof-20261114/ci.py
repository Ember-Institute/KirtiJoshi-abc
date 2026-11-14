from scheduler_common import run
if __name__ == "__main__":
    f="Solutions/Source_FermatBelyiCuspCoefficient.lean"
    run("coefficient-source-leaf",f,version="final",duration="60s",memory="6GiB")
    run("coefficient-source-artifact",f,artifact=True,version="final")
    f="Theorems/Thm_AbcAdaptation_Tripod_Fermat_Proper_belyiCanonicalCuspCoefficientIdentity.lean"
    run("coefficient-target-leaf",f,version="final",duration="60s",memory="6GiB")
    run("coefficient-target-artifact",f,artifact=True,version="final")
    run("closed-axioms-review","Solutions/Checks_FermatBelyiCuspCoefficient.lean","review",version="final",duration="60s",memory="6GiB")
