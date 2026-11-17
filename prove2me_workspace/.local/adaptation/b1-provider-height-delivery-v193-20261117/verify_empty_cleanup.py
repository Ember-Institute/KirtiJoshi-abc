#!/usr/bin/env python3
from pathlib import Path
import json
p=Path(__file__).with_name('cleanup-whitelist.json')
j=json.loads(p.read_text())
assert j['entries']==[] and j['cleanupPerformed'] is False
assert j['cacheDeletionAllowed'] is False and j['recursiveDeletionAllowed'] is False
print('Empty cleanup whitelist verified; no deletion performed')
