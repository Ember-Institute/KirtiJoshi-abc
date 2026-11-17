#!/usr/bin/env python3
"""Verify the one-file cleanup plan; --apply is for the accepting main agent only."""
from pathlib import Path
import argparse,hashlib,json,tarfile
O=Path(__file__).resolve().parent
W=Path('/home/admin-wsl/Coq/abc/prove2me_workspace')
SOL=W/'Solutions/Sol_AbcAdaptation_Tripod_mem_fieldOfExtended_self.lean'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def main():
 p=argparse.ArgumentParser();p.add_argument('--apply',action='store_true');args=p.parse_args()
 j=json.loads((O/'cleanup-whitelist.json').read_text());g=json.loads((O/'gates.json').read_text())
 assert g['complete'] and g['archiveReopenedSHA256Verified']
 assert len(j['entries'])==1 and j['entries'][0]['path']==str(SOL)
 assert not j['recursiveDeletionAllowed'] and not j['otherSolutionDeletionAllowed'] and not j['cacheDeletionAllowed']
 e=j['entries'][0];assert sha(SOL)==e['sha256']
 a=O/Path(e['archiveSource']['archive']).name;assert sha(a)==e['archiveSource']['archiveSHA256']
 with tarfile.open(a,'r:gz') as t:
  b=t.extractfile(e['archiveSource']['member']).read();assert hashlib.sha256(b).hexdigest()==e['sha256']==e['archiveSource']['memberSHA256']
 for kept in j['mustKeep']:assert sha(kept['path'])==kept['sha256']
 if args.apply:SOL.unlink()
 print(json.dumps({'verified':True,'cleanupPerformed':args.apply,'onlyPath':str(SOL)},indent=2))
if __name__=='__main__':main()
