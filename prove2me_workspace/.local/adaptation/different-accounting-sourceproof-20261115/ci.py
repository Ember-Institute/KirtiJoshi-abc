from scheduler_common import run
paths=['Solutions/Source_FermatBelyiDifferentAccounting.lean','Theorems/Thm_AbcAdaptation_Tripod_Fermat_Proper_belyiActualFieldDifferentAccounting.lean']
for source in paths:
 tag=source.rsplit('/',1)[1][:-5].removeprefix('Source_')
 run(tag+'-leaf',source)
 run(tag+'-artifact',source,artifact=True)
run('closed-axioms-review','Solutions/Checks_FermatBelyiDifferentAccounting.lean',kind='review')
