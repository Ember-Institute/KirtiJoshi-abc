import pathlib,json,hashlib
p=pathlib.Path('/home/admin-wsl/Coq/abc/prove2me_workspace/.local/adaptation/foundation-reference-carriers-20261115'); repo=pathlib.Path('/home/admin-wsl/Coq/abc');sha=lambda b:hashlib.sha256(b).hexdigest();cut=lambda b,r:b[r['start']['offset']:r['end']['offset']]
small=json.loads((p/'foundation-small-source-report.json').read_text());wrapped=json.loads((p/'wrapped/foundation-wrapper-report.json').read_text());ledger=json.loads((p/'SOURCE_LEDGER.json').read_text()); original=json.loads((p/'original-exprs.json').read_text());mapping=json.loads((p/'wrapped/typed-original-source-wrapped-map.json').read_text()); issues=[];counts={'retained':0,'selected_commands':0,'source_provenance':0,'wrapper_segments':0,'wrapper_commands':0,'blind_removals':0,'consumer_edges':0,'paths':0}; summaries=[]
def ck(v,s):
 if not v:issues.append(s)
for sm,b,e in zip(small['modules'],wrapped['bundles'],ledger['entries']):
 name=sm['module'];src=pathlib.Path(sm['originalSource']).read_bytes();norm=pathlib.Path(sm['originalCoordinateSource']).read_bytes();ss=pathlib.Path(sm['source']).read_bytes();wp=p/'wrapped/Definitions'/pathlib.Path(b['path']).name;w=wp.read_bytes();prod=repo/'prove2me_workspace/Definitions'/wp.name
 import subprocess
 blob=subprocess.run(['git','-C','/home/admin-wsl/Coq/abc.old/refer/iut','show','07cb1da58f6d428a670dbb5dd6093d428bcbcdd8:'+str(pathlib.Path(sm['originalSource']).relative_to(repo/'refer/iut'))],capture_output=True,check=True).stdout
 ck(blob==src,name+' exact upstream commit blob')
 ck(sha(src)==sm['rawSha256']==e['originalSourceSha256'],name+' source hash');ck(src==norm,name+' normalized byte identity');ck(sha(ss)==sm['sourceSha256'],name+' small hash');ck(w==prod.read_bytes() and sha(w)==b['sha256']==e['wrappedSourceSha256'],name+' installed hash')
 for c in sm['retainedCommands']:
  counts['retained']+=1;counts['selected_commands']+=bool(c['selectedCompilerDeclarations']);raw=cut(norm,c['originalRange']);ck(raw==cut(ss,c['outputRange']) and sha(raw)==c['sha256'],name+' retained '+str(c['commandIndex']))
 end=0
 for seg in sm['provenance']:
  counts['source_provenance']+=1;r=seg['outputRange'];ck(r['start']['offset']==end,name+' provenance coverage');end=r['end']['offset'];out=cut(ss,r);ck(sha(out)==seg['sha256'],name+' provenance sha')
  if seg['kind']=='copied':ck(out==cut(norm,seg['originalRange']),name+' copied identity')
 ck(end==len(ss),name+' provenance complete')
 end=0
 for seg in b['provenance']:
  counts['wrapper_segments']+=1;r=seg['outputRange'];ck(r['start']['offset']==end,name+' wrapper coverage');end=r['end']['offset'];out=cut(w,r);ck(sha(out)==seg['sha256'],name+' wrapper seg sha')
  if 'smallSourceRange' in seg:ck(out==cut(ss,seg['smallSourceRange']),name+' wrapper copied identity')
 ck(end==len(w),name+' wrapper full coverage');ck(b['projectOccurrenceEdits']==[],name+' no occurrence edits')
 for c in b['commandMaps']:
  counts['wrapper_commands']+=1;ck(cut(w,c['wrapperRange'])==cut(norm,c['originalRange']),name+' wrapper command byte identity')
 blind=b['blindReadback'];rem=blind['removedNarrative'];end=0;parts=[]
 for seg in sorted(rem,key=lambda x:x['productionRange']['start']['offset']):
  counts['blind_removals']+=1;r=seg['productionRange'];ck(sha(cut(w,r))==seg['removedSha256'],name+' blind removal hash');parts.append(w[end:r['start']['offset']]);end=r['end']['offset']
 parts.append(w[end:]);bb=(p/'wrapped/blind'/wp.name).read_bytes();ck(sha(bb)==blind['sha256'],name+' blind hash');recon=b''.join(parts);ck(recon==bb,name+' blind exact narrative subtraction');print(name,'blind recon same?',recon==bb,'selected',len(sm['selectedCompilerDeclarations']))
 summaries.append({'module':name,'selected_count':len(sm['selectedCompilerDeclarations']),'source_sha256':sha(src),'installed_sha256':sha(w),'blind_sha256':sha(bb)})
gp=repo/'prove2me_workspace/.local/adaptation/reference-extraction-20261115/c22-decl-graph.jsonl';rows=[json.loads(s) for s in gp.read_text().splitlines()];print('graph row2 keys',list(rows[1]));graph={r['name']:r for r in rows if 'name' in r}
for e in ledger['entries']:
 for d in e['selectedDeclarations']:
  for edge in d['actualOriginalConsumers']:
   counts['consumer_edges']+=1;ck(d['original'] in graph[edge['consumer']][edge['edge']],d['original']+' consumer edge '+str(edge))
  path=d['originalConsumerPathToMainTheorem']
  if path is None:continue
  ck(path[0]==d['original'] and path[-1]=='Iut.Theorem110Invariants.theorem110',d['original']+' path endpoints');counts['paths']+=1
  for a,b in zip(path,path[1:]):ck(a in graph[b]['typeDeps'] or a in graph[b]['valueDeps'] or a in graph[b]['constructors'],d['original']+' path step '+a+' -> '+b)
ck(len(original['records'])==len(mapping['constants'])==151,'151 record/map counts');ck(sum(r['selected'] for r in original['records'])==83,'83 original selected');ck({r['name'] for r in original['records']}=={r['originalName'] for r in mapping['constants']},'map exact original inventory');ck(sum(len(e['selectedDeclarations']) for e in ledger['entries'])==83,'83 ledger count')
print('COUNTS',counts);print('ISSUES',issues)
out=pathlib.Path('/tmp/p2m-foundation-final-review-v2-20261115');(out/'byte-graph-review.json').write_text(json.dumps({'issues':issues,'counts':counts,'modules':summaries},ensure_ascii=False,indent=2)+'\n')
