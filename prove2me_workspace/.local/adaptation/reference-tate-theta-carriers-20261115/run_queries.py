"""Sequential scheduler receipt collection and exact source-data acceptance."""
from pathlib import Path
import hashlib
import json
import subprocess
import sys

B = Path(__file__).resolve().parent


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def call(*args):
    subprocess.run([sys.executable, '-u', str(B / 'ci.py'), *args], check=True)


def finish(tag):
    path = B / (tag + '-result.json')
    while not path.exists():
        call('collect', tag)
    result = json.loads(path.read_text())
    assert result['status'] == 'succeeded'
    assert result['result']['exit_code'] == 0
    assert result['result']['snapshot']['workspace_mode'] == 'exclusive_worktree'
    assert result['result']['snapshot']['snapshot_id'] is None
    assert result['resources']['peak_rss_bytes'] <= 16 * 1024**3
    assert not any(marker in result['result'].get('stdout', '') + result['result'].get('stderr', '')
                   for marker in ['PANIC', 'error:', 'error('])
    request = result['request']
    arguments = request['parameters']
    assert result['result']['actual_arguments'] == ['lean', *([arguments['source']] if 'source' in arguments else arguments['args'])]
    cpu, user, system = [result['resources'].get(k) for k in ['cpu_time_seconds', 'cpu_user_seconds', 'cpu_system_seconds']]
    if all(v is not None for v in [cpu, user, system]):
        assert abs(cpu - user - system) < 0.1
    return result


def run(tag, source, *args):
    if not (B / (tag + '-submit.json')).exists():
        call('submit', tag, source, *args)
    return finish(tag)


def accept_parser():
    receipt = finish('parser-ranges')
    assert (Path(receipt['request']['workspace']) / receipt['request']['parameters']['source']).resolve() == B / 'QueryNextCarrierParserRanges.lean'
    assert Path(receipt['request']['environment']['FOUNDATION_PARSER_CONFIG']).resolve() == B / 'parser-config.json'
    outputs = []
    for path in sorted((B / 'parser-output').glob('*.jsonl')):
        facts = [json.loads(line) for line in path.read_text().splitlines()]
        source, summary = facts[0], facts[-1]
        assert summary['kind'] == 'summary' and summary['status'] == 'success'
        normalized = Path(source['coordinateSource'])
        assert sha(normalized) == source['normalizedSha256Expected']
        assert normalized.read_bytes() == Path(source['source']).read_bytes().replace(b'\r\n', b'\n')
        outputs.append({'module': source['module'], 'path': str(path), 'sha256': sha(path),
            'normalized': str(normalized), 'normalizedSha256': sha(normalized), 'summary': summary})
    assert len(outputs) == 4
    acceptance = {'schema': 'foundation-parser-acceptance-v1', 'status': 'accepted',
        'job_id': receipt['job_id'], 'compilerReceiptSha256': sha(B / 'parser-ranges-result.json'),
        'configSha256': sha(B / 'parser-config.json'),
        'parserQuerySha256': sha(B / 'QueryNextCarrierParserRanges.lean'),
        'querySha256': sha(B / 'QueryNextCarrierParserRanges.lean'),
        'graphSha256': json.loads((B / 'inventory.json').read_text())['graphSha256'],
        'noPanicOrErrorDiagnostics': True, 'outputs': outputs}
    (B / 'parser-acceptance.json').write_text(json.dumps(acceptance, ensure_ascii=False, indent=2) + '\n')


def accept_original(tag='original-exprs'):
    receipt = finish(tag)
    receipt_path = (B / (tag + '-result.json')).resolve()
    assert (Path(receipt['request']['workspace']) / receipt['request']['parameters']['source']).resolve() == B / 'QueryNextCarrierOriginalExprs.lean'
    assert Path(receipt['request']['environment']['NEXT_CARRIER_EXPORT_CONFIG']).resolve() == B / 'export-config.json'
    data = json.loads((B / 'original-exprs.json').read_text())
    assert len(data['records']) == data['recordCount'] == 117 and data['selectedCount'] == 78
    config = json.loads((B / 'export-config.json').read_text())
    assert data['compilerVersion'] == '4.35.0-rc3'
    assert data['inventorySha256'] == config['inventorySha256'] == sha(B / 'inventory.json')
    assert data['graphSha256'] == config['graphSha256']
    assert Path(config['outputFile']).resolve() == B / 'original-exprs.json'
    actual = {r['name']: r for r in data['records']}
    assert set(actual) == {r['name'] for r in config['records']}
    parser_names = {}
    for artifact in json.loads((B / 'parser-acceptance.json').read_text())['outputs']:
        for line in Path(artifact['path']).read_text().splitlines():
            row = json.loads(line)
            if row['kind'] == 'compilerDecl':
                parser_names[row['name']] = row['nameExpr']
    assert set(parser_names) == set(actual)
    assert all(actual[n]['nameExpr'] == parser_names[n] for n in actual)
    acceptance = {'schema': 'foundation-original-exprs-acceptance-v1', 'status': 'accepted',
        'job_id': receipt['job_id'], 'compilerReceiptPath': str(receipt_path),
        'compilerReceiptSha256': sha(receipt_path),
        'configSha256': sha(B / 'export-config.json'),
        'querySha256': sha(B / 'QueryNextCarrierOriginalExprs.lean'),
        'originalExprsSha256': sha(B / 'original-exprs.json'),
        'inventorySha256': sha(B / 'inventory.json'), 'noPanicOrErrorDiagnostics': True}
    (B / 'original-exprs-acceptance.json').write_text(json.dumps(acceptance, ensure_ascii=False, indent=2) + '\n')


if __name__ == '__main__':
    import argparse
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--original-tag', default='original-exprs')
    options = parser.parse_args()
    accept_parser()
    accept_original(options.original_tag)
