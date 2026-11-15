"""Root-only sequential exclusive platform checks; no compiler subprocesses."""
from pathlib import Path
import json
from run_queries import run
B = Path(__file__).resolve().parent
if __name__ == '__main__':
    report = json.loads((B / 'generated-wrapped/foundation-wrapper-report.json').read_text())
    assert report['definitionsBundleCount'] == 4 and report['selectedConstantCount'] == 78
    for bundle in report['bundles']:
        slug = bundle['module'].split('.')[-1]
        source = 'Definitions/' + Path(bundle['path']).name
        run('platform-' + slug + '-leaf', source)
        run('platform-' + slug + '-artifact', source, '--artifact')
    run('production-gates', '.local/adaptation/reference-tate-theta-carriers-20261115/ProductionGates.lean', '--review')
