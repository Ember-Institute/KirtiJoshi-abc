from scheduler_common import run
u='.local/adaptation/belyi-different-conductor-split-20261114/'
for tag, source, kind in [
 ('upload-definition-leaf','UploadDefinition.lean','leaf'),
 ('definition-types-leaf','AuditDefinition.lean','leaf'),
 *[('upload-type-'+str(i)+'-leaf','UploadType'+str(i)+'.lean','leaf') for i in range(3)],
 ('direct-belyiActualFieldDifferentTower-leaf','Solution_belyiActualFieldDifferentTower.lean','leaf'),
 ('direct-tripodGeneratorConductorIdentity-leaf','Solution_tripodGeneratorConductorIdentity.lean','leaf'),
 ('solution-leaf','Solution_belyiDifferentConductorComparison.lean','leaf'),
 ('types-leaf','AuditSolution.lean','leaf'),
 ('consumer-review','ChecksConductorConsumer.lean','review'),
 ('production-gates-review','ProductionGates.lean','review')]:
 run(tag,u+source,kind=kind,version='v2' if tag == 'definition-types-leaf' else 'v1',duration='66s' if tag == 'definition-types-leaf' else '60s',memory='7GiB' if tag == 'definition-types-leaf' else '16GiB')
