"""Sequential exclusive platform compilation after main-agent integration."""
from pathlib import Path
import json, math, subprocess, sys
from run_small_oracles import finish

B = Path(__file__).resolve().parent

def call(*args):
    subprocess.run([sys.executable, '-u', str(B / 'ci.py'), *args], check=True)

def run(tag, source, *extra):
    if not (B / (tag + '-submit.json')).exists():
        call('submit', tag, source, *extra)
    finish(tag)

if __name__ == '__main__':
    for source in json.loads((B / 'integration.json').read_text())['files']:
        slug = Path(source).stem.removeprefix('Def_AbcAdaptation_Reference_Iut_Cor312_').replace('ThetaData_', '')
        run('platform-' + slug + '-leaf', source)
        prior = json.loads((B / ('platform-' + slug + '-leaf-result.json')).read_text())['resources']
        duration = str(max(30, math.ceil(prior['wall_time_seconds'] * 1.3))) + 's'
        memory = str(min(16, max(2, math.ceil(prior['peak_rss_bytes'] / 1024**3 * 1.3)))) + 'GiB'
        run('platform-' + slug + '-artifact', source, '--artifact', '--duration', duration, '--memory', memory,
            '--basis', 'Same source artifact after accepted leaf: wall=' + str(prior['wall_time_seconds']) + ', RSS=' + str(prior['peak_rss_bytes']))
        print('ACCEPTED PLATFORM BUNDLE ' + slug, flush=True)
    run('kernel-audit', '.local/adaptation/foundation-reference-carriers-20261115/AuditFoundationCarriers.lean',
        '--review', '--env', 'FOUNDATION_AUDIT_CONFIG=' + str(B / 'audit-config.json'),
        '--input', str(B / 'audit-config.json'), '--input', str(B / 'original-exprs.json'))
    run('production-gates', '.local/adaptation/foundation-reference-carriers-20261115/ProductionGates.lean', '--review')
