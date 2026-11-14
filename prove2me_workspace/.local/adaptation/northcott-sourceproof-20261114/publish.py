from pathlib import Path
import json,sys,uuid,urllib.request,urllib.error,importlib.util,shutil
w=Path('/home/admin-wsl/Coq/abc/prove2me_workspace');b=w/'.local/adaptation/northcott-sourceproof-20261114';sys.path.insert(0,str(b))
s=importlib.util.spec_from_file_location('p2m_api',w/'.local/abc-item/api.py');api=importlib.util.module_from_spec(s);s.loader.exec_module(api)
assert api.base=='https://prove2.me/api/v1'
import delivery_draft
import delivery_common as strong
delivery_draft.Delivery.preflight=strong.preflight
class Adapter:
 def request(self,endpoint,payload=None,method='GET'):
  return api.request(endpoint,payload,method)
 def verify_file(self,theorem_id,proof_type,absolute_path,explanation):
  boundary='p2m-'+uuid.uuid4().hex;parts=[]
  for k,v in [('theorem_id',theorem_id),('proof_type',proof_type),('explanation',explanation)]:
   parts.append(('--'+boundary+'\r\nContent-Disposition: form-data; name="'+k+'"\r\n\r\n'+v+'\r\n').encode())
  code=Path(absolute_path).read_bytes();assert b'sorry' not in code
  parts.extend([('--'+boundary+'\r\nContent-Disposition: form-data; name="file"; filename="solution.lean"\r\nContent-Type: text/plain; charset=utf-8\r\n\r\n').encode()+code+b'\r\n',('--'+boundary+'--\r\n').encode()])
  credentials=json.loads((w/'credentials.json').read_text());req=urllib.request.Request(api.base+'/verify',data=b''.join(parts),headers={'Authorization':'Bearer '+credentials['access_token'],'Accept':'application/json','Content-Type':'multipart/form-data; boundary='+boundary},method='POST')
  try:
   with api.opener.open(req,timeout=45) as response:return json.load(response)
  except urllib.error.HTTPError as e:raise RuntimeError('Verification HTTP '+str(e.code)) from None
if __name__=='__main__':
 shutil.copy2(__file__,b/'publish.py')
 delivery=delivery_draft.Delivery(Adapter(),b,w);delivery.run();print('Northcott private Definition/node publication, six proof submissions, and platform graph readback completed.',flush=True)
