from pathlib import Path
import subprocess,json,time,os
coordinator='/tmp/p2m-proper-canonical-ci-main-20261113.py';w=Path('/home/admin-wsl/Coq/abc/prove2me_workspace');b=w/'.local/adaptation/fermat-proper-canonical-20261113'
def alive():
 for p in Path('/proc').iterdir():
  if not p.name.isdigit():continue
  try:args=p.joinpath('cmdline').read_bytes().split(b'\0')
  except OSError:continue
  if len(args)>1 and args[0].rsplit(b'/',1)[-1] in [b'python3',b'python'] and args[1].decode(errors='ignore')==coordinator:return int(p.name)
 return None
pid=alive();print('Following the live main-only CI coordinator PID',pid,flush=True)
while alive() is not None:time.sleep(15)
p=b/'canonical-reduction-axioms-result.json';assert p.exists() and json.loads(p.read_text())['status']=='succeeded','CI coordinator ended before the final successful reduction receipt; inspect the same jobs before retrying.'
for script in ['/tmp/p2m-audit-proper-ci-20261113.py','/tmp/p2m-proper-upload-types-20261113.py','/tmp/p2m-audit-proper-ci-20261113.py','/tmp/p2m-platform-proper-canonical-20261113.py']:
 subprocess.run(['python3',script],check=True)
print('Proper canonical unit ready for main-agent final database update and delivery.',flush=True)
