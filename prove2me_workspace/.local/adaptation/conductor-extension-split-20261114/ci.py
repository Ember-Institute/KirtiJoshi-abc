from scheduler_common import run
paths=['Definitions/Def_FermatBelyiConductorExtensionFinitePlaces.lean', 'Definitions/Def_FermatBelyiConductorExtensionChildren.lean', 'Solutions/Source_FermatBelyiConductorExtensionAdapters.lean', 'Theorems/Thm_AbcAdaptation_Tripod_Fermat_Proper_belyiActualFieldLocalConductorComparison.lean', 'Theorems/Thm_AbcAdaptation_Tripod_Fermat_Proper_belyiActualFieldDifferentAccounting.lean', 'Theorems/Thm_AbcAdaptation_Tripod_Fermat_Proper_belyiActualFieldConductorExtension.lean']
for source in paths:
 tag=source.rsplit('/',1)[1][:-5].removeprefix('Def_').removeprefix('Source_')
 run(tag+'-leaf',source,version='v5' if 'Adapters' in tag else 'v1',duration='66s' if 'Adapters' in tag else '60s',memory='6GiB' if 'Adapters' in tag else '16GiB')
 run(tag+'-artifact',source,artifact=True)
run('closed-axioms-review','Solutions/Checks_FermatBelyiConductorExtensionClosed.lean',kind='review')
run('reduction-axioms-leaf','Solutions/Checks_FermatBelyiConductorExtensionReduction.lean')
