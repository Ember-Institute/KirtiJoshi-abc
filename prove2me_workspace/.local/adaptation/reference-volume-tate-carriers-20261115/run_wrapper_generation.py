"""Generate five exact namespace wrappers from accepted compiler artifacts."""
from pathlib import Path
import subprocess, sys

B = Path(__file__).resolve().parent
args = [sys.executable, str(B / 'wrap_carriers.py')]
for key, name in [
    ('small-source-report', 'generated/foundation-small-source-report.json'),
    ('parser-acceptance', 'parser-acceptance.json'),
    ('original-exprs', 'original-exprs.json'),
    ('original-exprs-acceptance', 'original-exprs-acceptance.json'),
    ('original-exprs-ci-result', 'original-exprs-result.json'),
    ('imports', 'imports.json'), ('reviewed-imports', 'precise-import-review.json'),
    ('unit-config', 'bound-unit-config.json'),
    ('oracle-driver-acceptance', 'runtime-driver-acceptance.json'),
    ('oracle-driver-ci-result', 'runtime-oracle-driver-leaf-result.json'),
]:
    args += ['--' + key, str(B / name)]
for slug in ['ContainerHull', 'LogVolume', 'PrimeToOrder', 'Weierstrass-v2', 'NormalizedOrder']:
    args += ['--oracle-receipt', str(B / ('small-oracle-' + slug) / 'index.json'),
        '--oracle-ci-result', str(B / ('small-oracle-' + slug + '-result.json'))]
args += ['--out', str(B / 'generated-wrapped')]
raise SystemExit(subprocess.run(args, check=False).returncode)
