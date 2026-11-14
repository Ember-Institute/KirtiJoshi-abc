from scheduler_common import run
u='.local/adaptation/conductor-extension-split-20261114/'
for tag,source,kind in [
 ('upload-definition-0-leaf','UploadDefinition0.lean','leaf'),
 ('upload-definition-1-leaf','UploadDefinition1.lean','leaf'),
 ('definition-types-leaf','AuditDefinition.lean','leaf'),
 ('upload-type-0-leaf','UploadType0.lean','leaf'),
 ('upload-type-1-leaf','UploadType1.lean','leaf'),
 ('solution-leaf','Solution_belyiActualFieldConductorExtension.lean','leaf'),
 ('types-leaf','AuditSolution.lean','leaf'),
 ('consumer-review','ChecksConductorExtensionConsumer.lean','review'),
 ('production-gates-review','ProductionGates.lean','review')]:
 run(tag,u+source,kind=kind,version='v2' if tag=='definition-types-leaf' else 'v1',duration='67s' if tag=='definition-types-leaf' else '60s',memory='7GiB' if tag=='definition-types-leaf' else '16GiB')
