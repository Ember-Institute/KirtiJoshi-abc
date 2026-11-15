from pathlib import Path
import importlib.util,json
W=Path('/home/admin-wsl/Coq/abc/prove2me_workspace');O=Path('/tmp/p2m-orbicurve70-single-delivery-v9-20261116')
def load(n,p):
 s=importlib.util.spec_from_file_location(n,p);m=importlib.util.module_from_spec(s);s.loader.exec_module(m);return m
pub=load('pub',W/'.local/adaptation/supplier-carriers-delivery-20261116/tools/publisher.py');api=load('api',W/'.local/abc-item/api.py');packet=pub.read(O/'packet.json');ready=pub.read(O/'ready.final.json');assert ready['passed']and all(ready['gates'].values())
assert ready['packet_sha256']==pub.sha(O/'packet.json')
for p,h in ready['evidence_sha256'].items():assert pub.sha(p)==h
for p,h in packet['source_sha256'].items():assert pub.sha(W/p)==h
P=pub._protocol();D=O/'platform';P['check_scope'](api,D);row,=packet['publications'];before=api.request('/theorems/'+pub.ROOT+'/graph');pub.save(D/'root-graph-before.json',before)
intent=D/(row['tag']+'-intent.json');posted=D/(row['tag']+'-submit.json')
if intent.exists():assert pub.read(intent)==row and posted.exists()
else:
 assert not posted.exists();pub.save(intent,row);pub.save(posted,api.request('/submit-definition',row['payload'],'POST'))
z=pub.read(posted);job=P['poll'](api,D,row,z['job_id'],900);P['check_definition'](api,D,row,job['theorem_id']);after=api.request('/theorems/'+pub.ROOT+'/graph');pub.save(D/'root-graph-after.json',after);assert before==after
pub.save(D/'published-ids.json',{row['tag']:job['theorem_id']});print(json.dumps({'published':row['tag'],'id':job['theorem_id']}),flush=True)
