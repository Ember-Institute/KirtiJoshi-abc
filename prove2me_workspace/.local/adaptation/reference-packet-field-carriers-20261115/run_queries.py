"""Sequential scheduler-only parsing and exact original Expr export."""
from pathlib import Path
import hashlib, json, subprocess, sys

B = Path(__file__).resolve().parent
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()

def call(*args):
    subprocess.run([sys.executable, '-u', str(B / 'ci.py'), *args], check=True)

def finish(tag):
    while not (B / (tag + '-result.json')).exists():
        call('collect', tag)
    z = json.loads((B / (tag + '-result.json')).read_text())
    assert z['status'] == 'succeeded'
    r = z['result']
    assert r['exit_code'] == 0
    assert r['snapshot']['workspace_mode'] == 'exclusive_worktree'
    assert r['snapshot']['snapshot_id'] is None
    assert z['resources']['peak_rss_bytes'] <= 16 * 1024**3
    assert not any(s in r.get('stdout', '') + r.get('stderr', '') for s in ['PANIC', 'error:', 'error('])
    return z

def run(tag, source, *args):
    if not (B / (tag + '-submit.json')).exists():
        call('submit', tag, source, *args)
    return finish(tag)

if __name__ == '__main__':
    z = run('parser-ranges-v2', '.local/adaptation/reference-packet-field-carriers-20261115/QueryNextCarrierParserRanges.lean',
        '--original', '--duration', '210s', '--memory', '11GiB',
        '--basis', 'Same parser retry after scoped notation diagnostic; previous wall161.50s RSS8.18GiB; activate original source scopes',
        '--env', 'FOUNDATION_PARSER_CONFIG=' + str(B / 'parser-config.json'),
        '--input', str(B / 'parser-config.json'), '--input', str(B / 'inventory.json'))
    outputs = []
    for p in sorted((B / 'parser-output').glob('*.jsonl')):
        fs = [json.loads(line) for line in p.read_text().splitlines()]
        source, summary = fs[0], fs[-1]
        assert summary['kind'] == 'summary' and summary['status'] == 'success'
        normalized = Path(source['coordinateSource'])
        assert sha(normalized) == source['normalizedSha256Expected']
        assert normalized.read_bytes() == Path(source['source']).read_bytes().replace(b'\r\n', b'\n')
        outputs.append({'module': source['module'], 'path': str(p), 'sha256': sha(p),
            'normalized': str(normalized), 'normalizedSha256': sha(normalized), 'summary': summary})
    assert len(outputs) == 5
    acceptance = {'schema': 'foundation-parser-acceptance-v1', 'status': 'accepted',
        'job_id': z['job_id'], 'compilerReceiptSha256': sha(B / 'parser-ranges-v2-result.json'),
        'configSha256': sha(B / 'parser-config.json'),
        'parserQuerySha256': sha(B / 'QueryNextCarrierParserRanges.lean'),
        'graphSha256': json.loads((B / 'inventory.json').read_text())['graphSha256'],
        'noPanicOrErrorDiagnostics': True, 'outputs': outputs}
    (B / 'parser-acceptance.json').write_text(json.dumps(acceptance, ensure_ascii=False, indent=2) + '\n')
    z = run('original-exprs', '.local/adaptation/reference-packet-field-carriers-20261115/QueryNextCarrierOriginalExprs.lean',
        '--original', '--env', 'NEXT_CARRIER_EXPORT_CONFIG=' + str(B / 'export-config.json'),
        '--input', str(B / 'export-config.json'), '--input', str(B / 'inventory.json'))
    data = json.loads((B / 'original-exprs.json').read_text())
    assert len(data['records']) == 196 and data['selectedCount'] == 133
    acceptance = {'schema': 'foundation-original-exprs-acceptance-v1', 'status': 'accepted',
        'job_id': z['job_id'], 'compilerReceiptSha256': sha(B / 'original-exprs-result.json'),
        'configSha256': sha(B / 'export-config.json'), 'originalExprsSha256': sha(B / 'original-exprs.json'),
        'inventorySha256': sha(B / 'inventory.json'), 'noPanicOrErrorDiagnostics': True}
    (B / 'original-exprs-acceptance.json').write_text(json.dumps(acceptance, ensure_ascii=False, indent=2) + '\n')
