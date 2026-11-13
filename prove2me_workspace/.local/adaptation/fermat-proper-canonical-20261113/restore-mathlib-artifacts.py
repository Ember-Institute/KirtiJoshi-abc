from pathlib import Path
import json,subprocess,hashlib,concurrent.futures
p=Path('/home/admin-wsl/Coq/mathlib4-0df444a');b=Path('/home/admin-wsl/Coq/abc/prove2me_workspace/.local/adaptation/fermat-proper-canonical-20261113');rows=json.loads(Path('/tmp/p2m-mathlib-cache-restore-plan-20261113.json').read_text());leantar='/root/.elan/toolchains/leanprover--lean4---v4.33.1/bin/leantar'
def restore(row):
 f=Path(row['archive']);url='https://lakecache.blob.core.windows.net/mathlib4-master/f/'+f.name
 if not f.exists():
  x=subprocess.run(['curl','--fail','--silent','--show-error','--location','--proxy','http://127.0.0.1:10808','--max-time','45',url,'-o',str(f)+'.restore-part'],capture_output=True,text=True)
  assert x.returncode==0,(row['module'],x.stderr)
  Path(str(f)+'.restore-part').rename(f)
 comment=subprocess.check_output([leantar,'-k',str(f)],text=True).strip()
 x=subprocess.run([leantar,'-x','-f',str(f)],cwd=p,capture_output=True,text=True);assert x.returncode==0,(row['module'],x.stderr)
 o=p/'.lake/build/lib/lean'/(row['module'].replace('.','/')+'.olean');assert o.exists();header=o.read_bytes()[:64];assert b'4.33.1' in header,(row['module'],header)
 return dict(row,url=url,archive_sha256=hashlib.sha256(f.read_bytes()).hexdigest(),comment=comment,olean=str(o),olean_sha256=hashlib.sha256(o.read_bytes()).hexdigest(),method='Exact Mathlib cache hash; unpacked prebuilt artifacts with leantar; no compilation')
with concurrent.futures.ThreadPoolExecutor(max_workers=4) as pool:results=list(pool.map(restore,rows))
(b/'mathlib-artifact-restoration.json').write_text(json.dumps({'locked_revision':'0df444a360eaa60ab8c11dca51a86af692955474','count':len(results),'records':results},indent=2)+'\n')
print('Restored',len(results),'exact Mathlib Lean 4.33.1 prebuilt module archives.',flush=True)
