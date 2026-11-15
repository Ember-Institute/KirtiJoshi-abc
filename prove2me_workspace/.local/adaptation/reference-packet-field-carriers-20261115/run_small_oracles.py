"""One source frontend per scheduler-managed runtime process."""
from pathlib import Path
import json, sys
from run_queries import run, finish

B = Path(__file__).resolve().parent

if __name__ == '__main__':
    report = json.loads((B / 'generated/foundation-small-source-report.json').read_text())
    for entry in report['modules']:
        slug = Path(entry['source']).stem
        tag = 'small-oracle-' + slug
        config = B / (tag + '-config.json')
        run(tag, '.local/adaptation/reference-packet-field-carriers-20261115/ExtractSmallRuntimeOracle.lean',
            '--original', '--runtime-config', str(config), '--duration', '180s', '--memory', '13GiB',
            '--basis', 'Lean-only outer frontend followed by one source frontend; prior original import/parser ~151s8.18GiB and original small-source peak8.78GiB; physical peak acceptance remains16GiB',
            '--input', str(config), '--input', entry['source'], '--purpose', 'One exact selected source module and authentic InfoTree references at runtime')
        index = json.loads((B / tag / 'index.json').read_text())
        assert index['complete'] and index['requestedFiles'] == index['finishedFiles'] == 1
        result, = index['results']
        assert result['status'] == 'success'
        facts = [json.loads(line) for line in Path(result['output']).read_text().splitlines()]
        assert facts[-1]['kind'] == 'summary' and facts[-1]['status'] == 'success'
        print('ACCEPTED SOURCE ' + slug, flush=True)
