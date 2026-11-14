from scheduler_common import run
f='Theorems/Thm_AbcAdaptation_Tripod_Fermat_Proper_canonicalCuspPolarLinearEquivalence.lean'
run('consumer-parent-leaf',f,duration='60s',memory='6GiB')
run('consumer-parent-artifact',f,artifact=True)
run('consumer-closed-review','.local/adaptation/canonical-differential-sourceproof-20261114/ChecksCanonicalCuspClosed.lean','review')
