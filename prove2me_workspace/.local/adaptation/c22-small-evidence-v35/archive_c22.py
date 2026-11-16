#!/usr/bin/env python3
"""Freeze the existing C22 private Definition result. No CI, API, Git, or deep DAG reads."""
from pathlib import Path,PurePosixPath
import argparse,hashlib,io,json,tarfile
ROOT=Path('/home/admin-wsl/Coq/abc');W=ROOT/'prove2me_workspace';A=W/'.local/adaptation';C=A/'c2-complete-inputs-20261116'
TAG='AbcAdaptation_Reference_Iut_Implication_Corollary22'
def digest(b):return hashlib.sha256(b).hexdigest()
def main():
 p=argparse.ArgumentParser(description=__doc__)
 p.add_argument('--delivery',type=Path,default=A/'c22-input44-delivery-v35');p.add_argument('--scope',type=Path,default=A/'c22-input44-ready-v34/scope')
 p.add_argument('--destination',type=Path,default=A/'c22-small-evidence-v35');p.add_argument('--apply',action='store_true');a=p.parse_args()
 dest=a.destination.resolve();delivery=a.delivery.resolve();scope=a.scope.resolve()
 if dest.exists() or not (dest.is_relative_to(A) or dest.is_relative_to('/tmp')):p.error('Use a new destination inside adaptation or /tmp')
 selected={};cache={};identities={};pins={};missing=[];invalid=[]
 def need(v,m):
  if not v:invalid.append(m)
  return bool(v)
 def identity(p):
  s=p.stat();return (s.st_dev,s.st_ino,s.st_size,s.st_mtime_ns,s.st_ctime_ns)
 def add(path,expected=None):
  path=Path(path)
  if not path.is_absolute():path=W/path
  if path.is_symlink():invalid.append('Explicit selected evidence is a symlink: '+str(path));return
  path=path.resolve();key=str(path)
  if key in selected:
   if expected:need(selected[key]['sha256']==expected,'Conflicting selected SHA: '+key)
   return
  if not path.is_file():missing.append(key);return
  if path.name=='.env' or any(s in path.name.lower() for s in ['credentials','access_token','refresh_token']):invalid.append('Credential selected: '+key);return
  if path.is_relative_to(ROOT):member=path.relative_to(ROOT).as_posix()
  elif path.is_relative_to('/tmp'):member='external-evidence/tmp/'+path.relative_to('/tmp').as_posix()
  else:invalid.append('Explicit evidence outside project and /tmp: '+key);return
  need(not PurePosixPath(member).is_absolute() and '..' not in PurePosixPath(member).parts,'Unsafe archive member')
  data=path.read_bytes();h=digest(data)
  if expected and not need(h==expected,'Selected saved pin changed: '+key):return
  cache[path]=data;identities[path]=identity(path)
  selected[key]={'source':key,'archive_path':member,'bytes':len(data),'sha256':h};pins.pop(key,None)
 def read(path,expected=None):
  add(path,expected);path=Path(path).resolve()
  if str(path) not in selected:return None
  return json.loads(cache[path])
 def pin_only(path,h,reason='Original accepted historical/deep input pin; no stat/read/copy/rehash'):
  path=Path(path)
  if not path.is_absolute():path=W/path
  key=str(path)
  if key in selected:need(selected[key]['sha256']==h,'Selected evidence differs from accepted pin: '+key)
  else:
   previous=pins.get(key,{}).get('existingPins',[]);pins[key]={'existingPins':sorted(set(previous+[h])),'reason':reason}
 def receipt(path,expected=None):
  r=read(path,expected)
  if r is None:return None
  need(r.get('status')=='succeeded' and r.get('result',{}).get('exit_code')==0,'Actual compilation receipt not succeeded: '+str(path))
  for k,h in r.get('request',{}).get('worktree_manifest',{}).get('input_hashes',{}).items():pin_only(k,h)
  if str(path).endswith('-result.json'):
   for ending in ['-request.json','-submit.json']:
    side=Path(str(path).removesuffix('-result.json')+ending)
    if side.is_file():add(side)
  return r
 def bound(v):
  if isinstance(v,dict) and isinstance(v.get('path'),str) and isinstance(v.get('sha256'),str):add(v['path'],v['sha256'])
 def collect_pins(x):
  # Only inspect already selected configuration/receipt JSON; never open referenced deep files.
  if isinstance(x,dict):
   if isinstance(x.get('path'),str) and isinstance(x.get('sha256'),str) and Path(x['path']).is_absolute():pin_only(x['path'],x['sha256'])
   for v in x.values():collect_pins(v)
  elif isinstance(x,list):
   for v in x:collect_pins(v)
 packet=read(delivery/'packet.json');ready=read(delivery/'ready.final.json')
 if packet is None or ready is None:
  print(json.dumps({'ready':False,'missingRequiredFiles':missing,'invalidBindings':invalid,'archiveWritten':False},indent=2));return 2
 need(packet.get('publicationReady') is True and ready.get('passed') is True,'Actual packet/ready not accepted')
 need(ready.get('packet_sha256')==digest(cache[(delivery/'packet.json').resolve()]),'Packet/ready binding differs')
 need(len(ready.get('gates',{}))==12 and all(v is True for v in ready['gates'].values()) and ready.get('pending')==[],'Existing twelve gates pending')
 need(packet.get('kernel_coverage',{}).get('source')==44 and packet['kernel_coverage'].get('named')==44 and packet.get('required_owned_count')==46,'C22 actual44/46 scope differs')
 need(len(packet.get('sourceBackedTargetOnlyGeneratedProofs',[]))==2 and len(packet.get('upstreamFourSourceProofRoots',[]))==4,'Original source-backed proof scope differs')
 need(packet.get('root_graph_membership') is False and packet.get('act2ConstructionClosed') is False,'Publication scope differs')
 row,=packet['publications'];need(row['tag']==TAG and row['endpoint']=='/submit-definition','One existing C22 Definition required')
 platform=delivery/'platform';required=['packet-binding.json','published-ids.json','root-graph-before.json','root-graph-after.json',TAG+'-intent.json',TAG+'-submit.json',TAG+'-result.json',TAG+'-published-item.json']
 journal={n:read(platform/n) for n in required}
 if all(v is not None for v in journal.values()):
  job=journal[TAG+'-result.json'];published=journal[TAG+'-published-item.json'];submitted=journal[TAG+'-submit.json']
  need(job.get('status')=='PUBLISHED' and job.get('id')==submitted.get('job_id'),'Actual original publication is not PUBLISHED')
  need(journal[TAG+'-intent.json']==row,'Original POST intent differs')
  need(journal['packet-binding.json']=={'packet_sha256':ready['packet_sha256'],'names':[TAG]},'Original journal packet binding differs')
  need(journal['published-ids.json'].get(TAG)==published.get('definition_id')==job.get('theorem_id'),'Actual private Definition ID differs')
  need(published.get('visibility')=='private' and published.get('mathlib_rev')==packet['environment'] and published.get('deprecated_at') is None,'Published private scope differs')
  for k in ['definition_name','definition_title','definition','natural_language_statement','source']:need(published.get(k)==row['payload'].get(k),'Exact published readback differs: '+k)
  need(journal['root-graph-before.json']==journal['root-graph-after.json'],'Existing root graph changed')
 # Complete current mathematical result is 12,585,247 bytes, not a deep global DAG.
 # Include its bytes, current request/config, and actual leaf/artifact/review receipts.
 mathreceipt=receipt(packet['actualCurrent44Receipt']['path'],packet['actualCurrent44Receipt']['sha256'])
 report=read(packet['actualCurrent44Report']['path'],packet['actualCurrent44Report']['sha256'])
 if mathreceipt and report:
  need(report.get('comparedRecordCount')==report.get('sourceGeneratedClosureCount')==44 and report.get('targetGeneratedClosureCount')==46 and not report.get('hasSorryAx'),'Current mathematical report scope differs')
  need(report.get('sourceBackedWholeValueEqualityCertificateCount')==2 and report.get('rawAllComputationalValueBinderInfoEqual') is False,'Retain exactly two checked whole-function equalities and raw differences')
  cfgpath=mathreceipt['request']['environment']['PACKAGE_IDENTITY_AUDIT_CONFIG'];cfg=read(cfgpath)
  if cfg:
   need(report['configuration']==cfg,'Actual current report/configuration differs');need(Path(cfg['outputFile']).resolve()==Path(packet['actualCurrent44Report']['path']).resolve(),'Current output binding differs')
   collect_pins(cfg)
   # Source44 export is an explicit 18 MB unit export, not the huge source dependency DAG.
   add(cfg['sourceExprFile']);add(C/'source-export-config.json');add(C/'QueryOriginalExprs.lean')
   receipt(cfg['sourceReceiptBinding']['receiptPath'])
   for key in ['casesOnWholeValueCertificate','recOnWholeValueCertificate']:
    cert=cfg[key]
    for field in ['passedProbeOutput','passedProbeQuery','passedProbeConfig','actualProbeSourceRecord','actualTargetFact','sameJobActualTargetFact','actualSource44File']:
     if field in cert:bound(cert[field])
    for field in ['passedProbeReceipt','actualSource44Receipt','actualTargetFactReceipt']:
     if field in cert:receipt(cert[field]['path'],cert[field]['sha256'])
   comp=cfg['generatedProofCompatibility']
   literal=comp['literalSourceBinding'];receipt(literal['receiptPath']);add(literal['sourceExprFile'],literal.get('sourceExprSha256'))
   native=comp['nativeProofQueryBinding'];receipt(native['receiptPath']);bound(native['query'])
   for field in ['sourceExportConfig']:
    if field in cfg:bound(cfg[field])
  add(C/'AuditC2Final44WithExactlyTwoValueCertificates.lean')
 # Select this small delivery and the actual publication/scope journal, no traversal of project trees.
 for path in delivery.rglob('*'):
  if path.is_file() and '__pycache__' not in path.parts:add(path)
 for path in scope.glob('*.json'):add(path)
 for group in ready['ci_receipts'].values():
  for path in group:receipt(path,ready['evidence_sha256'][path])
 for group in ready['gate_evidence'].values():
  for path in group:add(path,ready['evidence_sha256'][path])
 for parent in packet['parent_foundation_definitions']:bound(parent['currentDefinition']);bound(parent['savedPublicationEvidence']['publishedReadback'])
 for path,h in packet['source_sha256'].items():add(W/path,h)
 for group in [packet['metadata_sha256'],ready['evidence_sha256']]:
  for path,h in group.items():pin_only(path,h)
  # Select only the recorded binder/protocol and explicit frozen materials; deep dossiers stay pin-only.
  for path,h in group.items():
   f=Path(path)
   if f.suffix=='.py' or f.name in ['metadata-rebind-plan.json','trilingual.json','readback.json','compiled-types-supplement-v1.json','source-descriptions.en.json','SOURCE-NOTES.en.md','Basic-production-gate-reuse.json']:
    add(f,h)
 add(A/'reference-volume-tate-carriers-20261115/delivery.py')
 add(A/'platform-node-registry.json');add(ROOT/'refer/iut/Iut/Implication/Corollary22.lean');add(ROOT/'refer/iut/LICENSE');add(Path(__file__))
 # Necessary old pins remain recorded, with no old-report/huge-DAG replay or rehash.
 for proof in packet['upstreamFourSourceProofRoots']:
  v=proof['acceptedUpstreamDossier'];pin_only(v['path'],v['sha256'],'Accepted upstream source proof dossier retained by existing pin; no deep replay')
 entries=sorted(selected.values(),key=lambda x:x['archive_path']);need(len({x['archive_path'] for x in entries})==len(entries),'Duplicate archive member')
 reportout={'ready':not missing and not invalid,'apply':a.apply,'destination':str(dest),'files':len(entries),'input_bytes':sum(x['bytes'] for x in entries),'pinOnlyReferenceCount':len(pins),'missingRequiredFiles':sorted(set(missing)),'invalidBindings':invalid,'archiveWritten':False,'deletions':[]}
 if missing or invalid:print(json.dumps(reportout,ensure_ascii=False,indent=2));return 2
 if not a.apply:print(json.dumps(reportout,ensure_ascii=False,indent=2));return 0
 for x in entries:
  f=Path(x['source'])
  if not need(f.is_file() and not f.is_symlink() and identity(f)==identities[f],'Input changed before archive write: '+str(f)):print(json.dumps(reportout,ensure_ascii=False,indent=2));return 2
 dest.mkdir(parents=True);archivepath=dest/'c22-input44-small-evidence.tar.gz'
 with tarfile.open(archivepath,'w:gz') as tar:
  for x in entries:
   item=tarfile.TarInfo(x['archive_path']);item.size=x['bytes'];item.mode=0o644;tar.addfile(item,io.BytesIO(cache[Path(x['source'])]))
 with tarfile.open(archivepath,'r:gz') as tar:
  if {x.name for x in tar.getmembers()}!={x['archive_path'] for x in entries}:raise ValueError('Archive member set differs')
  for x in entries:
   stream=tar.extractfile(x['archive_path'])
   if stream is None or digest(stream.read())!=x['sha256']:raise ValueError('Archived member SHA differs: '+x['archive_path'])
 published=journal[TAG+'-published-item.json'];manifest={'schema':'c22-input44-existing-private-definition-small-evidence-archive/v35','source':str(delivery),'publishedDefinition':{'name':TAG,'id':published['definition_id'],'publishJob':journal[TAG+'-result.json']['id']},'current44Receipt':packet['actualCurrent44Receipt'],'current44Report':packet['actualCurrent44Report'],'source44':44,'target46':46,'sourceBackedTargetOnlyGeneratedProofs':packet['sourceBackedTargetOnlyGeneratedProofs'],'upstreamFourSourceProofRoots':packet['upstreamFourSourceProofRoots'],'wholeFunctionEqualityCertificates':2,'rawComputationalBinderDifferencesRetained':True,'frozenReadbacksAndPaperStringsUnchanged':True,'files':entries,'input_bytes':reportout['input_bytes'],'pinOnlyReferences':pins,'pinOnlyPolicy':'Only explicit unit44 exports, current actual reports, two whole-function proofs, literal proof support and small publication evidence are read/copied. Huge dependency DAGs and upstream expanded dossiers retain accepted historical pins without stat/read/copy/rehash. No file-size limit is an acceptance gate.','archive_sha256':digest(archivepath.read_bytes()),'archive_bytes':archivepath.stat().st_size,'root_graph_membership':False,'act2ConstructionClosed':False,'deletions':[]}
 (dest/'archive-manifest.json').write_text(json.dumps(manifest,ensure_ascii=False,indent=2)+'\n');reportout.update(archiveWritten=True,archiveSha256=manifest['archive_sha256'],archiveBytes=manifest['archive_bytes']);print(json.dumps(reportout,ensure_ascii=False,indent=2));return 0
if __name__=='__main__':raise SystemExit(main())
