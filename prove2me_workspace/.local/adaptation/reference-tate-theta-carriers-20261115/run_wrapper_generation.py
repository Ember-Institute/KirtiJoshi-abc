"""Generate four exact namespace wrappers from accepted compiler artifacts."""
from pathlib import Path
import argparse, json, subprocess, sys

B = Path(__file__).resolve().parent
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--original-receipt', type=Path)
options = parser.parse_args()
acceptance = json.loads((B / 'original-exprs-acceptance.json').read_text())
original_receipt = options.original_receipt or Path(acceptance.get('compilerReceiptPath', str(B / 'original-exprs-result.json')))
args = [sys.executable, str(B / 'wrap_carriers.py')]
for key, name in [
    ('small-source-report', 'generated/foundation-small-source-report.json'),
    ('parser-acceptance', 'parser-acceptance.json'),
    ('original-exprs', 'original-exprs.json'),
    ('original-exprs-acceptance', 'original-exprs-acceptance.json'),
    ('imports', 'imports.json'), ('reviewed-imports', 'precise-import-review.json'),
    ('unit-config', 'bound-unit-config.json'),
]:
    args += ['--' + key, str(B / name)]
args += ['--original-exprs-ci-result', str(original_receipt.resolve())]
previous = B.parent / 'reference-volume-tate-carriers-20261115'
args += ['--oracle-driver-acceptance', str(previous / 'runtime-driver-acceptance.json'),
         '--oracle-driver-ci-result', str(previous / 'runtime-oracle-driver-leaf-result.json')]
for slug in ['JInvariant', 'Parametrization', 'AdmissiblePrime', 'TateStructure']:
    args += ['--oracle-receipt', str(B / ('small-oracle-' + slug) / 'index.json'),
        '--oracle-ci-result', str(B / ('small-oracle-' + slug + '-result.json'))]
args += ['--out', str(B / 'generated-wrapped')]
raise SystemExit(subprocess.run(args, check=False).returncode)
