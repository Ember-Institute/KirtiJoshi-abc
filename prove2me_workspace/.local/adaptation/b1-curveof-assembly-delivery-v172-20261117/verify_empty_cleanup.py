#!/usr/bin/env python3
"""Verify the unit has no permitted cleanup entries; never deletes any file."""
from pathlib import Path
import hashlib,json
O=Path(__file__).resolve().parent
j=json.loads((O/'cleanup-whitelist.json').read_text())
assert j['entries']==[] and j['unitHasNoSolFiles'] and not j['cleanupPerformed']
assert not j['cacheDeletionAllowed'] and not j['otherSolutionDeletionAllowed'] and not j['recursiveDeletionAllowed']
for p in j['mustKeep']:assert hashlib.sha256(Path(p['path']).read_bytes()).hexdigest()==p['sha256']
print(json.dumps({'verified':True,'permittedDeletionCount':0,'cleanupPerformed':False}))
