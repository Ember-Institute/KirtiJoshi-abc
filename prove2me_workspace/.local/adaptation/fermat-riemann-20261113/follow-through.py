from pathlib import Path
import time,json,runpy
b=Path('/home/admin-wsl/Coq/abc/prove2me_workspace/.local/adaptation/fermat-riemann-20261113')
while True:
 p=b/'sketch-axioms-leaf-result.json'
 if p.exists():
  x=json.loads(p.read_text());assert x['status']=='succeeded';break
 time.sleep(15)
runpy.run_path('/tmp/p2m-riemann-upload-types-20261113.py',run_name='__main__')
runpy.run_path('/tmp/p2m-platform-riemann-20261113.py',run_name='__main__')
