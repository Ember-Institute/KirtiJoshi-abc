#!/usr/bin/env python3
"""Archive the five existing private outcomes. No CI/API/Git; deep DAG evidence stays pin-only."""
import argparse
import hashlib
import io
import json
from pathlib import Path,PurePosixPath
import tarfile

ROOT=Path('/home/admin-wsl/Coq/abc');W=ROOT/'prove2me_workspace';A=W/'.local/adaptation'
V28=A/'main5-private-publication-rebind-v28-20261116';D=A/'main5-local-dossier-v27-20261116'
TOOLS=Path('/tmp/p2m-main5-publish-finish-v33-20261116')
MODULES=['LeftHandSide','RightHandSide','Statement','Invariants','LogVolumeBound'];COUNTS=[25,26,19,71,32]
DOSSIER_SHA='8921a39bb3955c4b87ddec4fd24f15a1571b5b5632ddb5a08cdf2cff7445243d'

def digest(data):return hashlib.sha256(data).hexdigest()
def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--delivery-root',type=Path,default=A/'main5-delivery-v33');p.add_argument('--destination',type=Path,default=A/'main5-small-evidence-v34');p.add_argument('--apply',action='store_true');a=p.parse_args()
 dest=a.destination.resolve();delivery=a.delivery_root.resolve()
 if not dest.is_relative_to(A) or dest.exists():p.error('Use a new destination inside the existing adaptation directory')
 selected={};pins_only={};missing=[];invalid=[];cache={};identities={};units=[]
 def need(ok,message):
  if not ok:invalid.append(message)
  return ok
 def identity(path):
  st=path.stat();return (st.st_dev,st.st_ino,st.st_size,st.st_mtime_ns,st.st_ctime_ns)
 def add(path,expected=None):
  path=Path(path)
  if not path.is_absolute():path=W/path
  if path.is_symlink():invalid.append('Symlink evidence: '+str(path));return
  path=path.resolve();key=str(path)
  if key in selected:
   if expected:need(selected[key]['sha256']==expected,'Conflicting selected pin: '+key)
   return
  if not path.is_file():missing.append(key);return
  if path.name=='.env' or any(x in path.name.lower() for x in ['credentials','access_token','refresh_token']):invalid.append('Credential path was explicitly selected: '+key);return
  if path.is_relative_to(ROOT):member=path.relative_to(ROOT).as_posix()
  elif path.is_relative_to('/tmp'):member=(dest.relative_to(ROOT)/'external-evidence/tmp'/path.relative_to('/tmp')).as_posix()
  else:invalid.append('Selected path outside repo/task tmp: '+key);return
  need(not PurePosixPath(member).is_absolute() and '..' not in PurePosixPath(member).parts,'Unsafe archive member')
  if path not in cache:cache[path]=path.read_bytes();identities[path]=identity(path)
  h=digest(cache[path])
  if expected and not need(h==expected,'Selected saved pin changed: '+key):return
  selected[key]={'source':key,'archive_path':member,'bytes':len(cache[path]),'sha256':h};pins_only.pop(key,None)
 def read(path,expected=None):
  add(path,expected);path=Path(path).resolve()
  if str(path) not in selected:return None
  return json.loads(cache[path])
 def pin_reference(path,h,reason='Deep DAG/export/report retained by its existing accepted pin; no stat/read/copy/rehash'):
  # Do not touch the referenced path. Pin collection does not inspect deep files.
  path=Path(path)
  if not path.is_absolute():path=W/path
  key=str(path)
  if key in selected:
   need(selected[key]['sha256']==h,'Selected file differs from original accepted pin: '+key)
  else:
   old=pins_only.get(key,{}).get('existingPins',[]);pins_only[key]={'existingPins':sorted(set(old+[h])),'reason':reason}
 def nested_pins(value):
  if isinstance(value,dict):
   if isinstance(value.get('path'),str) and isinstance(value.get('sha256'),str):pin_reference(value['path'],value['sha256'])
   for child in value.values():nested_pins(child)
  elif isinstance(value,list):
   for child in value:nested_pins(child)
 def receipt(path,expected=None):
  r=read(path,expected)
  if r is None:return
  need(r.get('status')=='succeeded' and r.get('result',{}).get('exit_code')==0,'Actual CI receipt is not succeeded: '+str(path))
  # The full request/manifest in the original receipt retains all resource and deep input bindings.
  for key,h in r.get('request',{}).get('worktree_manifest',{}).get('input_hashes',{}).items():pin_reference(key,h)
  for ending in ['-request.json','-submit.json']:
   candidate=Path(str(path).removesuffix('-result.json')+ending)
   if str(path).endswith('-result.json') and candidate.is_file():add(candidate)
 dossier=read(D/'main5-local-source-relative-dossier.json',DOSSIER_SHA)
 if dossier is not None:
  need(dossier.get('selectedNamedCount')==173 and dossier.get('selectedPlusPrivateCount')==176 and dossier.get('currentSelected173LocalSourceEvidenceComplete') is True,'Accepted actual main5 dossier scope differs')
  need(dossier.get('sourceSelectedProofValueResolutions')==0 and dossier['ownedInventory']['freshCurrentInventoryConfirmed'] is True,'Accepted extra proof-only/current owned scope differs')
  nested_pins(dossier)
  for row in dossier['moduleReceipts']+[dossier['private3Evidence']]:
   receipt(row['receipt']['path'],row['receipt']['sha256']);add(row['query']['path'],row['query']['sha256'])
   # Configs, source DAGs and full expanded reports remain pin-only, regardless of their byte size.
   for key in ['configuration','innerReport']:pin_reference(row[key]['path'],row[key]['sha256'])
  receipt(dossier['ownedInventory']['actualReceipt']['path'],dossier['ownedInventory']['actualReceipt']['sha256'])
  add(dossier['ownedInventory']['actualFacts']['path'],dossier['ownedInventory']['actualFacts']['sha256'])
  for row in dossier['currentFiveNativeInputs']:
   add(row['source']['path'],row['source']['sha256']);pin_reference(row['currentArtifact']['path'],row['currentArtifact']['sha256'],'Prebuilt native artifact retained by existing pin; not read/copied/rehash')
 for short,count in zip(MODULES,COUNTS):
  unit=delivery/short;packet=read(unit/'packet.json');ready=read(unit/'ready.final.json')
  if packet is None or ready is None:continue
  need(packet.get('publicationReady') is True and ready.get('passed') is True,'Unready saved packet: '+short)
  need(ready.get('packet_sha256')==digest(cache[(unit/'packet.json').resolve()]),'Packet/ready SHA differs: '+short)
  need(packet.get('actual_kernel_evidence')=={'path':str(D/'main5-local-source-relative-dossier.json'),'sha256':DOSSIER_SHA},'Different actual dossier bound: '+short)
  need(packet.get('kernel_coverage',{}).get('named')==count and packet['kernel_coverage'].get('proof')==0,'Selected named/extra proof scope differs: '+short)
  need(packet.get('required_owned_count')==count+(3 if short=='LogVolumeBound' else 0),'Owned scope differs: '+short)
  need(len(packet.get('sourceMappedPrivateProofs',[]))==(3 if short=='LogVolumeBound' else 0),'Private3 mapping differs: '+short)
  rows=packet.get('publications',[])
  if not need(len(rows)==1,'Expected one existing Definition: '+short):continue
  row=rows[0];tag=row['tag'];platform=unit/'platform'
  required=['packet-binding.json','published-ids.json','root-graph-before.json','root-graph-after.json',tag+'-intent.json',tag+'-submit.json',tag+'-result.json',tag+'-published-item.json']
  journal={name:read(platform/name) for name in required}
  if any(v is None for v in journal.values()):continue
  job=journal[tag+'-result.json'];published=journal[tag+'-published-item.json'];submit=journal[tag+'-submit.json']
  need(job.get('status')=='PUBLISHED' and job.get('id')==submit.get('job_id'),'Original job is not PUBLISHED: '+short)
  need(journal[tag+'-intent.json']==row,'Original POST intent differs: '+short)
  need(journal['packet-binding.json']=={'packet_sha256':ready['packet_sha256'],'names':[tag]},'Original journal binding differs: '+short)
  need(journal['published-ids.json'].get(tag)==published.get('definition_id')==job.get('theorem_id'),'Actual Definition identity differs: '+short)
  need(published.get('visibility')=='private' and published.get('mathlib_rev')==packet['environment'],'Private environment differs: '+short)
  for key in ['definition_name','definition_title','definition','natural_language_statement','source']:need(published.get(key)==row['payload'].get(key),'Exact readback differs: '+short+'/'+key)
  need(journal['root-graph-before.json']==journal['root-graph-after.json'],'Root graph changed: '+short)
  # This directory contains only the explicit small publication packet and journal; never the source DAG exports.
  for path in unit.rglob('*'):
   if path.is_file() and '__pycache__' not in path.parts:add(path)
  for path in (delivery/(short+'-scope')).glob('*.json'):add(path)
  for group in ready['ci_receipts'].values():
   for path in group:receipt(path,ready['evidence_sha256'][path])
  for paths in ready['gate_evidence'].values():
   for path in paths:add(path,ready['evidence_sha256'][path])
  for binding in [packet['metadata_sha256'],ready['evidence_sha256']]:
   for path,h in binding.items():pin_reference(path,h)
  for relative,h in packet['source_sha256'].items():add(W/relative,h)
  for path in unit.rglob('*'):
   if path.is_file() and '__pycache__' not in path.parts:add(path)
  scope=delivery/(short+'-scope')
  if scope.is_dir():
   for path in scope.glob('*'):
    if path.is_file():add(path)
  units.append({'module':short,'definitionName':tag,'publishedDefinition':published['definition_id'],'publishJob':job['id'],'named':count,'extraOwnProofOnlyRoots':0,'sourceMappedPrivate':3 if short=='LogVolumeBound' else 0,'owned':count+(3 if short=='LogVolumeBound' else 0),'sourceSha256':packet['source_sha256'],'kernelDossier':packet['actual_kernel_evidence']})
 # Original full code, 27 frozen readbacks, compiler-type confirmation, 18 literal paper quotations and exact source deltas.
 for path in V28.rglob('*'):
  if path.is_file() and '__pycache__' not in path.parts:add(path)
 # Explicit small integration scripts/plans; expanded comparison reports remain pin-only above.
 for name in ['README.md','merge_local_source_dossier.py','prepare_next_log32.py','prepare_reuse_and_owned_refresh.py','reuse-three-modules-and-private-plan.json','next-log32-review-plan.json','root-integration.json','delivery-manifest.json','QueryCurrentSelected173AndOwned176.lean']:
  path=D/name
  if path.is_file():add(path)
 # v28 contains only explicit full source/payload/readback/paper/delta metadata, not deep expression exports.
 for path in V28.rglob('*'):
  if path.is_file() and '__pycache__' not in path.parts:add(path)
 reuse_path=Path('/tmp/p2m-local-basic-ready-bind-v31-20261116/Basic-production-gate-reuse.json');reuse=read(reuse_path)
 if reuse:
  for item in reuse['productionPinnedInputs']:add(item['path'],item['sha256'])
 add(A/'reference-volume-tate-carriers-20261115/delivery.py')
 for path in TOOLS.glob('*'):
  if path.is_file() and path.suffix in ['.py','.json','.md']:add(path)
 for path in Path(__file__).parent.glob('*'):
  if path.is_file() and path.suffix in ['.py','.json','.md']:add(path)
 add(A/'platform-node-registry.json')
 duplicate_path=Path(__file__).parent/'exact-duplicate-candidates.json';duplicates=read(duplicate_path)
 if duplicates:
  for item in duplicates['eligibleExactDuplicateFiles']+duplicates['differentHistoricalCandidatesRetain']:add(item['path'],item['candidateSha256'])
 add(ROOT/'refer/iut/LICENSE')
 for module in ['Iut/Cor312/LeftHandSide','Iut/Cor312/RightHandSide','Iut/Cor312/Statement','Iut/Implication/Invariants','Iut/Implication/LogVolumeBound']:add(ROOT/'refer/iut'/(module+'.lean'))
 for row in units:
  for relative,h in row['sourceSha256'].items():need(digest(cache[(W/relative).resolve()])==h,'Current complete source differs')
 entries=sorted(selected.values(),key=lambda x:x['archive_path']);need(len(units)==5,'All five real PUBLISHED outcomes are required before archive write');need(len({r['archive_path'] for r in entries})==len(entries),'Duplicate member names')
 size=sum(r['bytes'] for r in entries);report={'ready':not missing and not invalid,'apply':a.apply,'destination':str(dest),'modules':units,'files':len(entries),'input_bytes':size,'input_mib':size/1024**2,'missingRequiredFiles':sorted(set(missing)),'invalidBindings':invalid,'pinOnlyReferenceCount':len(pins_only),'archiveWritten':False,'deletions':[]}
 if missing or invalid:print(json.dumps(report,ensure_ascii=False,indent=2));return 2
 if not a.apply:print(json.dumps(report,ensure_ascii=False,indent=2));return 0
 for r in entries:
  path=Path(r['source'])
  if not need(path.is_file() and not path.is_symlink() and identity(path)==identities[path],'Selected input changed before archive write: '+str(path)):print(json.dumps(report,ensure_ascii=False,indent=2));return 2
 dest.mkdir(parents=True);archive_path=dest/'main5-small-evidence.tar.gz'
 with tarfile.open(archive_path,'w:gz') as archive:
  for r in entries:
   info=tarfile.TarInfo(r['archive_path']);info.size=r['bytes'];info.mode=0o644;archive.addfile(info,io.BytesIO(cache[Path(r['source'])]))
 with tarfile.open(archive_path,'r:gz') as archive:
  if {m.name for m in archive.getmembers()}!={r['archive_path'] for r in entries}:raise ValueError('Archive member set differs')
  for r in entries:
   stream=archive.extractfile(r['archive_path'])
   if stream is None or digest(stream.read())!=r['sha256']:raise ValueError('Archive member SHA differs: '+r['archive_path'])
 manifest={'schema':'main5-existing-five-private-definitions-small-evidence-archive/v34','source':str(delivery),'publishedDefinitions':units,'files':entries,'input_bytes':size,'input_mib':size/1024**2,'pinOnlyReferences':pins_only,'pinOnlyPolicy':'Deep source DAGs/configs/expanded reports/native binaries retain original accepted pins without stat/read/copy/rehash. Explicit publication and compact factual records only are frozen. No size threshold constitutes a new acceptance gate.','sourceSelectedNamed':173,'sourceMappedPrivate':3,'owned':176,'extraOwnProofOnlyResolutionRoots':0,'canonicalC22Connected':False,'root_graph_membership':False,'archive_sha256':digest(archive_path.read_bytes()),'archive_bytes':archive_path.stat().st_size,'deletions':[]}
 (dest/'archive-manifest.json').write_text(json.dumps(manifest,ensure_ascii=False,indent=2)+'\n');report.update(archiveWritten=True,archiveSha256=manifest['archive_sha256'],archiveBytes=manifest['archive_bytes']);print(json.dumps(report,ensure_ascii=False,indent=2));return 0

if __name__=='__main__':raise SystemExit(main())
