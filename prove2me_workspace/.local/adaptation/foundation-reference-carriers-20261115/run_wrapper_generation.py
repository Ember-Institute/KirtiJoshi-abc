#!/usr/bin/env python3
"""Convenience invocation; this only launches the local Python generator."""
import argparse
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--unit', type=Path, default=Path('/home/admin-wsl/Coq/abc/prove2me_workspace/.local/adaptation/foundation-reference-carriers-20261115'))
parser.add_argument('--out', type=Path, default=HERE / 'wrapped')
args = parser.parse_args()
unit = args.unit.resolve()
command = [sys.executable, str(HERE / 'wrap_foundation.py')]
for key, filename in [
    ('small-source-report', 'foundation-small-source-report.json'),
    ('parser-acceptance', 'parser-acceptance.json'),
    ('original-exprs', 'original-exprs.json'),
    ('original-exprs-acceptance', 'original-exprs-acceptance.json'),
    ('original-exprs-ci-result', 'original-exprs-v2-result.json'),
    ('imports', 'imports.json'),
    ('reviewed-imports', 'precise-import-review.json'),
]:
    command.extend(['--' + key, str(unit / filename)])
for slug in ['Places', 'PointMap', 'RationalPlace', 'Procession', 'PacketPresentation']:
    command.extend(['--oracle-receipt', str(unit / ('small-oracle-' + slug) / 'index.json'),
                    '--oracle-ci-result', str(unit / ('small-oracle-' + slug + '-result.json'))])
command.extend(['--out', str(args.out.resolve())])
raise SystemExit(subprocess.run(command, check=False).returncode)
