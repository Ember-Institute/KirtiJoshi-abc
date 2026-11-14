from scheduler_common import run
helpers=['Solutions/Source_FermatConductorLowerMultiplicity.lean', 'Solutions/Source_FermatConductorLowerContribution.lean', 'Solutions/Source_FermatConductorPlaceDegree.lean', 'Solutions/Source_FermatConductorLocalComparison.lean']
for source in helpers+['Theorems/Thm_AbcAdaptation_Tripod_Fermat_Proper_belyiActualFieldLocalConductorComparison.lean']:
 tag=source.rsplit('/',1)[1][:-5].removeprefix('Source_')
 is_wrapper=source.startswith('Theorems/')
 run(tag+'-leaf',source,duration='60s',memory='6GiB' if is_wrapper else '16GiB')
 run(tag+'-artifact',source,artifact=True)
run('closed-axioms-review','Solutions/Checks_FermatLocalConductorSourceProof.lean',kind='review')
