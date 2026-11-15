"""One source frontend per scheduler-managed runtime process."""
from pathlib import Path
import json, sys
from run_queries import run, finish

B = Path(__file__).resolve().parent

if __name__ == '__main__':
    report = json.loads((B / 'generated/foundation-small-source-report.json').read_text())
    for entry in report['modules']:
        slug = Path(entry['source']).stem
        tag = 'small-oracle-' + slug + ('-v2' if slug == 'Weierstrass' else '')
        config = B / (tag + '-config.json')
        run(tag, '.local/adaptation/reference-volume-tate-carriers-20261115/ExtractSmallRuntimeOracle.lean',
            '--original', '--runtime-config', str(config), '--duration', '120s' if slug == 'Weierstrass' else '180s', '--memory', '8GiB' if slug == 'Weierstrass' else '13GiB',
            '--basis', ('Weierstrass retry after ci-013764 wall80.008s RSS5345447936 B; one required Ultra.Basic context import. ' if slug == 'Weierstrass' else '') + 'Lean-only outer frontend followed by one source frontend; current parser141.46s8.18GiB, cached Expr exporter140.49s8.59GiB, previous one-source frontend peak9.72GiB; physical peak acceptance remains16GiB',
            '--input', str(config), '--input', entry['source'], '--purpose', 'One exact selected source module and authentic InfoTree references at runtime')
        index = json.loads((B / tag / 'index.json').read_text())
        assert index['complete'] and index['requestedFiles'] == index['finishedFiles'] == 1
        result, = index['results']
        assert result['status'] == 'success'
        facts = [json.loads(line) for line in Path(result['output']).read_text().splitlines()]
        assert facts[-1]['kind'] == 'summary' and facts[-1]['status'] == 'success'
        print('ACCEPTED SOURCE ' + slug, flush=True)
