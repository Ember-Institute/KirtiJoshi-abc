from pathlib import Path
import json,time,runpy
b=Path('/home/admin-wsl/Coq/abc/prove2me_workspace/.local/adaptation/fermat-noncritical-composition-20261114')
while True:
 p=b/'reduction-axioms-leaf-result.json'
 if p.exists():
  assert json.loads(p.read_text())['status']=='succeeded';break
 time.sleep(15)
runpy.run_path('/tmp/p2m-composition-upload-types-20261114.py',run_name='__main__')
