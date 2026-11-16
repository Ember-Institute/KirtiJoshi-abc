#!/usr/bin/env python3
"""Root-run lmod small-evidence archive and exact integrated-draft cleanup.
Default is a read-only preview. Three real final receipts and platform ACCEPTED
are required. --apply writes a verified archive; --cleanup then removes only the
pinned role drafts. No compiler, MCP-CI, API, or Git calls.
"""
from pathlib import Path,PurePosixPath
import sys
sys.dont_write_bytecode=True
import argparse,hashlib,io,json,tarfile
TASK=Path(__file__).resolve().parent
ROOT=Path('/home/admin-wsl/Coq/abc');W=ROOT/'prove2me_workspace';A=W/'.local/adaptation';F=A/'lmod-prime-counting-v35-20261116';R=F/'roles-v36';P=F/'publication-v37';C=A/'main-chain-open-20261116'
NAME='AbcAdaptation.Reference.Iut.Theorem110Invariants.lmod_mul_logSle_le';TAG=NAME.replace('.','_');CANONICAL=W/'Theorems'/f'Thm_{TAG}.lean';PROOF_SHA='499d0410c10e8c12f53355dc06192f7af8433f6d55937bbec1c4c62795389be8'
read=lambda p:json.loads(Path(p).read_text());digest=lambda b:hashlib.sha256(b).hexdigest()
def checked(p):
 p=Path(p).absolute();assert p.is_file()and not p.is_symlink(),str(p);assert p.is_relative_to(ROOT)or p.is_relative_to('/tmp'),str(p);return p
def sha(p):return digest(checked(p).read_bytes())
def save(p,j):Path(p).write_text(json.dumps(j,ensure_ascii=False,indent=2)+'\n')
def member(p):
 p=Path(p);key=p.relative_to(ROOT).as_posix()if p.is_relative_to(ROOT)else'external-evidence/tmp/'+p.relative_to('/tmp').as_posix();assert not PurePosixPath(key).is_absolute()and'..'not in PurePosixPath(key).parts;return key
def success(path):
 r=read(checked(path));assert r['status']=='succeeded'and r['result']['exit_code']==0
 assert r['request']['workspace']==str(W)and r['request']['exclusive']is True
 s=r['result']['snapshot'];assert s['workspace_mode']=='exclusive_worktree'and s['snapshot_id']is None
 req=r['request'];params=req['parameters'];args=[params['source']]if'source'in params else params['args'];assert r['result']['actual_arguments']==['lean',*args]
 for d in r['result'].get('diagnostics')or[]:
  if isinstance(d,dict):assert d.get('severity')not in ['error','fatal']
 return r

def final_acceptance(leaf_path,artifact_path,axiom_path):
 plat=P/'platform';summary=read(plat/'delivery-summary.json');assert summary['direct_proof']=='ACCEPTED'and summary['published_theorem_count']==1 and summary['root_graph_unchanged']is True
 assert summary['root_graph_membership']is False and summary['canonicalC22Connected']is False
 assert read(plat/'root-graph-before.json')==read(plat/'root-graph-after.json')
 verify=read(plat/f'verify-{TAG}-result.json');assert verify['status']=='ACCEPTED';assert summary['published_ids'][NAME]==verify['theorem_id'];assert verify['id']==read(plat/f'verify-{TAG}-submit.json')['submission_id']
 published=read(plat/f'{TAG}-published-item.json');packet=read(P/'packet.ready.json');payload=packet['publications'][0]['payload'];assert published['theorem_id']==verify['theorem_id']and published['visibility']=='private'
 for key in ['theorem_name','theorem_title','preamble','formal_statement','natural_language_statement','source']:assert published[key]==payload[key],key
 assert read(P/'ready.final.json')['passed']is True
 # Capture actual canonical bytes. Its provenance header may differ from the submitted global solution.
 canonical=checked(CANONICAL);raw=canonical.read_bytes();assert ('theorem '+NAME).encode()in raw and b'theorem solution'not in raw
 cfg=read(R/'actual/four-role-audit.json')['configuration'];proof=cfg['sourceBinding']['sourceProofText'].encode();signature=cfg['sourceBinding']['sourceSignatureText'].encode();assert digest(proof)==PROOF_SHA and raw.count(proof)==1 and raw.count(signature)==1
 hs=digest(raw);final=[]
 for role,path in [('leaf',leaf_path),('artifact',artifact_path),('axiom',axiom_path)]:
  r=success(path);assert r['request']['worktree_manifest']['input_hashes'].get(str(canonical))==hs,'Final receipt does not bind actual canonical source'
  if role!='axiom':
   ps=r['request']['parameters'];src=ps.get('source')or ps['args'][0];assert (W/src).resolve()==canonical.resolve();assert r['request']['worktree_manifest']['source_sha256']==hs
   if role=='artifact':assert '-o'in ps['args']and Path(ps['args'][ps['args'].index('-o')+1]).suffix=='.olean'
  else:
   assert r['request']['task_type']=='review';report=r['result']['review'];assert report['passed']is True and report['checks']['no_sorryAx']is True and report['violations']==[]
  final.append({'role':role,'job_id':r['job_id'],'receipt':str(Path(path).resolve()),'resources':r.get('resources'),'exit_code':r['result']['exit_code']})
 audit=read(R/'actual/four-role-audit.json');assert audit['sourceOracleJob']=='ci-017433-8866e8c9'and audit['sourceProofSha256']==PROOF_SHA
 assert audit['sourceProofCommandIdentityVerified']is True and not audit['nativeHasTransitiveSorryAx']and not audit['solutionHasTransitiveSorryAx']
 return {'targetName':NAME,'theorem_id':verify['theorem_id'],'submission_id':verify['id'],'canonicalSource':str(canonical),'canonicalSha256':hs,'canonicalProofSha256':PROOF_SHA,'canonicalProofByteRange':[raw.index(proof),raw.index(proof)+len(proof)],'headerPolicy':'Actual root-integrated provenance header is retained; proof body matches complete original byte slice.','finalReceipts':final}

def main():
 ap=argparse.ArgumentParser(description=__doc__)
 for key in ['leaf','artifact','axiom']:ap.add_argument('--'+key+'-receipt',type=Path,required=True)
 ap.add_argument('--destination',type=Path,default=F/'archive-final-v38');ap.add_argument('--apply',action='store_true');ap.add_argument('--cleanup',action='store_true');args=ap.parse_args();assert not args.cleanup or args.apply,'Cleanup requires the archive-write phase'
 dest=args.destination.resolve();assert dest.is_relative_to(A)or dest.is_relative_to('/tmp');assert not dest.exists(),'Do not overwrite an existing archive or a partial run'
 final=final_acceptance(args.leaf_receipt,args.artifact_receipt,args.axiom_receipt)
 selected={};cache={};historical_pins={};source_ids={}
 def pin_only(p,h,reason='Existing accepted historical input pin; no expanded dependency-DAG replay'):
  p=Path(p);p=p if p.is_absolute()else W/p;historical_pins.setdefault(str(p),{'sha256Pins':[],'reason':reason});pins=historical_pins[str(p)]['sha256Pins'];
  if h not in pins:pins.append(h)
 def add(p,expected=None):
  p=checked(p);key=str(p)
  if key in selected:
   if expected:assert selected[key]['sha256']==expected
   return
  assert p.name!='.env'and not any(t in p.name.lower()for t in ['credentials','access_token','refresh_token'])
  b=p.read_bytes();h=digest(b)
  if expected:assert h==expected,'Recorded evidence pin changed: '+key
  st=p.stat();source_ids[p]=(st.st_dev,st.st_ino,st.st_size,st.st_mtime_ns,st.st_ctime_ns);cache[p]=b;selected[key]={'source':key,'archive_path':member(p),'bytes':len(b),'sha256':h}
 def include_pins(j):
  if isinstance(j,dict):
   if isinstance(j.get('path'),str)and isinstance(j.get('sha256'),str):pin_only(j['path'],j['sha256'])
   for v in j.values():include_pins(v)
  elif isinstance(j,list):
   for v in j:include_pins(v)
 # Own complete unit is small and contains source/type/InfoTree, successful/failing query versions,
 # all config, B trilingual snapshots, quotations and the entire private platform mutation journal.
 for base in [F,TASK]:
  for p in base.rglob('*'):
   if p.is_file()and'__pycache__'not in p.parts and'.lake'not in p.parts and not p.is_relative_to(dest):add(p)
 for p in C.glob('lmod-*.json'):add(p)
 # Explicit original source parser evidence and source oracle runtime, not huge transitive exports.
 source_meta=read(F/'source-difference-metadata.json')['sourceMetadataRetained']
 for key in ['parserEvidence','oracleRuntimeDriver','oracleRuntimeDriverAcceptance']:
  v=source_meta[key];add(v['path'],v['sha256'])
 add(source_meta['originalCoordinateSource'],source_meta['originalCoordinateSha256'])
 add(ROOT/'refer/iut/Iut/Implication/Theorem110.lean');add(ROOT/'refer/iut/LICENSE');add(CANONICAL)
 # Archive all 34 actually registered current Definition interface source files and the exact ten TYPE map.
 regpath=A/'platform-node-registry.json';reg=read(regpath);add(regpath);definitions=reg['reference_source_preparation']['definitions'];assert len(definitions)==34,'Definition inventory changed; review the intended archive scope'
 dep_sources=[]
 for row in definitions:
  p=W/'Definitions'/('Def_'+row['name']+'.lean');add(p);dep_sources.append({'name':row['name'],'definition_id':row['id'],'source':str(p),'sha256':sha(p)})
 datamap=read(R/'typedata-map-evidence.json');assert len(datamap['dataMappings'])==10
 for row in datamap['dataMappings']:
  add(row['existingMap']['path'],row['existingMap']['sha256']);v=row['currentInstalledSource'];add(v['path'],v['sha256'])
 # Preserve explicitly bound small shared evidence. Expanded upstream dossiers remain pin-only.
 packet=read(P/'packet.ready.json');ready=read(P/'ready.final.json')
 for group in [packet['metadata_sha256'],ready['evidence_sha256']]:
  for p,h in group.items():
   if Path(p).suffix in ['.py','.md','.lean','.txt','.json','.jsonl','.png']and not any(t in str(p)for t in ['c22-decl-graph.jsonl','source-all-records','source-expansion','source-project/.lake']):add(p,h)
   else:pin_only(p,h)
 paper=read(P/'paper-materials/paper-context.json')
 for v in paper['evidencePins']:add(v['path'],v['sha256'])
 receipt_paths=[args.leaf_receipt,args.artifact_receipt,args.axiom_receipt]
 for p in receipt_paths:
  p=Path(p).resolve();add(p);r=read(p)
  for src,h in r['request']['worktree_manifest']['input_hashes'].items():pin_only(src,h)
  stem=p.name.removesuffix('-result.json')
  for suffix in ['-request.json','-submit.json']:
   q=p.parent/(stem+suffix)
   if q.is_file():add(q)
  ps=r['request']['parameters'];src=ps.get('source')or ps['args'][0]
  if src!='--run'and(W/src).is_file():add(W/src)
 # Exact frozen duplicate whitelist only. The canonical theorem, source oracles and journal are protected.
 deletion=read(TASK/'delete-whitelist.json');protected=[F/'OriginalCommands',F/'SourceProbes',F/'actual',R/'queries',P/'platform']
 for row in deletion:
  p=checked(row['path']);assert p!=CANONICAL and not any(p.is_relative_to(q)for q in protected)
  assert sha(p)==row['sha256']and p.stat().st_size==row['bytes'],'Role draft changed; review exact cleanup list'
  if p.is_relative_to(W/'Theorems'):assert p.name.endswith('_NativeAuditProof.lean')
  if p.is_relative_to(W/'Solutions'):assert p.name==f'Sol_{TAG}.lean'
  add(p,row['sha256'])
 attempts=[]
 for p in sorted(C.glob('lmod-*-result.json')):
  r=read(p);status=r['status'];classification='actual-successful-attempt'if status=='succeeded'else'actual-'+status+'-not-passed'
  if r['job_id'].startswith('ci-017434-'):classification='cancelled-wrong-TYPE-environment-key; not a mathematical failure'
  if r['job_id'].startswith('ci-017451-'):classification='failed-historical-discard-syntax-query; mathematical comparison not reached'
  attempts.append({'source':str(p),'job_id':r['job_id'],'status':status,'classification':classification,'exit_code':r.get('result',{}).get('exit_code'),'resources':r.get('resources'),'diagnostics':r.get('result',{}).get('diagnostics'),'stderr':r.get('result',{}).get('stderr')})
 for p,b in cache.items():
  if p.suffix=='.json':
   try:j=json.loads(b)
   except (ValueError,UnicodeDecodeError):continue
   include_pins(j)
   if isinstance(j,dict):
    for path,h in j.get('request',{}).get('worktree_manifest',{}).get('input_hashes',{}).items():pin_only(path,h)
 entries=sorted(selected.values(),key=lambda r:r['archive_path']);assert len({r['archive_path']for r in entries})==len(entries)
 summary={'ready':True,'apply':args.apply,'cleanupRequested':args.cleanup,'destination':str(dest),'evidenceFiles':len(entries),'inputBytes':sum(r['bytes']for r in entries),'deleteFiles':len(deletion),'deleteBytes':sum(r['bytes']for r in deletion),'attemptResults':len(attempts),'registeredDefinitionSources':len(dep_sources),'actualSourceTypeDataMap':len(datamap['dataMappings']),'pinOnlyReferenceCount':len(historical_pins),'archiveCreated':False,'filesDeleted':0}
 print(json.dumps(summary,ensure_ascii=False,indent=2))
 if not args.apply:return 0
 dest.mkdir(parents=True);tarpath=dest/'small-evidence.tar.gz';manifest={'schema':'lmod-accepted-canonical-small-evidence-archive/v38','completed':False,'finalIntegration':final,'evidence':entries,'deleteAfterArchive':deletion,'attempts':attempts,'registeredDefinitionSources':dep_sources,'actualSourceTypeDataMap':datamap,'historicalPins':historical_pins,'historicalPinPolicy':'Physical mathlib/source cache artifacts and expanded accepted upstream dossiers are retained by original pins; they are not copied or rebuilt. All current lmod source/type/proof/config/journal evidence and current34 Definition source interfaces are included.','rawUpstreamProofByteIdentity':True,'effectiveSourceProofSha256':PROOF_SHA,'sourceOracleJob':'ci-017433-8866e8c9','fourRoleAuditJob':'ci-017463-3cafdf8c','paperContext':'IUT IV Proposition1.6 uses printed4/3; source helper uses3/2. Theorem1.10 excerpts are parent context, not an independent GenericLemma.','canonicalC22Connected':False,'S2-04Completed':False,'cleanupCompleted':False,'cleanupJournal':[]}
 save(dest/'archive-manifest.json',manifest)
 # Tar from the already hashed bytes. Read each archived member back and compare its SHA before any unlink.
 with tarfile.open(tarpath,'w:gz')as tar:
  for row in entries:
   info=tarfile.TarInfo(row['archive_path']);info.size=row['bytes'];info.mode=0o644;tar.addfile(info,io.BytesIO(cache[Path(row['source'])]))
 with tarfile.open(tarpath,'r:gz')as tar:
  assert {i.name for i in tar.getmembers()}=={r['archive_path']for r in entries}
  for row in entries:
   f=tar.extractfile(row['archive_path']);assert f is not None and digest(f.read())==row['sha256']
 archive_sha=sha(tarpath);manifest['archiveBytes']=tarpath.stat().st_size;manifest['archiveSha256']=archive_sha;manifest['allTarMemberSha256Verified']=True;save(dest/'archive-manifest.json',manifest)
 for row in entries:assert sha(row['source'])==row['sha256'],'Evidence changed during archive write'
 if args.cleanup:
  assert sha(tarpath)==archive_sha
  for row in deletion:
   p=checked(row['path']);assert sha(p)==row['sha256'];p.unlink();manifest['cleanupJournal'].append({'path':str(p),'archivedSha256':row['sha256'],'deleted':True});save(dest/'archive-manifest.json',manifest)
  manifest['cleanupCompleted']=True
 assert sha(CANONICAL)==final['canonicalSha256'];manifest['completed']=True;save(dest/'archive-manifest.json',manifest)
 summary.update(archiveCreated=True,archiveSha256=archive_sha,archiveBytes=tarpath.stat().st_size,filesDeleted=len(manifest['cleanupJournal']));print(json.dumps(summary,ensure_ascii=False,indent=2));return 0
if __name__=='__main__':raise SystemExit(main())
