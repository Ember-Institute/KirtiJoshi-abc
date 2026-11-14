"""Main-agent sequential scheduler pipeline. All compiler work stays in MCP-CI."""
from pathlib import Path
import hashlib, json, subprocess, sys

B = Path(__file__).resolve().parent
W = B.parents[2]

def call(*args):
    subprocess.run([sys.executable, '-u', str(B / 'ci.py'), *args], check=True)

def finish(tag):
    while not (B / (tag + '-result.json')).exists():
        call('collect', tag)
    z = json.loads((B / (tag + '-result.json')).read_text())
    assert z['status'] == 'succeeded', (tag, z['status'])
    r = z['result']
    assert r['exit_code'] == 0
    assert not any(t in r.get('stdout', '') + r.get('stderr', '') for t in ['PANIC', 'error:', 'error('])
    assert z['resources']['peak_rss_bytes'] <= 16 * 1024**3

if __name__ == '__main__':
    finish('original-exprs-v2')
    for slug in ['Places', 'PointMap', 'RationalPlace', 'Procession', 'PacketPresentation']:
        tag = 'small-oracle-' + slug
        source = '.local/adaptation/foundation-reference-carriers-20261115/ExtractSmall' + slug + 'Oracle.lean'
        config = B / (tag + '-config.json')
        entry, = json.loads(config.read_text())['files']
        if not (B / (tag + '-submit.json')).exists():
            call('submit', tag, source, '--original', '--env', 'REFERENCE_STAGE2_CONFIG=' + str(config),
                '--input', str(config), '--input', entry['source'])
        finish(tag)
        index = B / tag / 'index.json'
        if not index.exists():
            candidates = list((B / tag).glob('*index*.json'))
            assert len(candidates) == 1, ('Missing oracle index', tag, candidates)
            index, = candidates
        z = json.loads(index.read_text())
        assert z['complete'] is True and z['finishedFiles'] == z['requestedFiles'] == 1
        item, = z['results']
        assert item['status'] == 'success'
        facts = [json.loads(line) for line in Path(item['output']).read_text().splitlines()]
        assert facts[-1]['kind'] == 'summary' and facts[-1]['status'] == 'success'
        print('ACCEPTED SMALL SOURCE ' + slug, flush=True)
