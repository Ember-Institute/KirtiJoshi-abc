"""Main-agent exclusive platform leaves, artifacts and required audit gates."""
from pathlib import Path
import json, math
from run_queries import run

B = Path(__file__).resolve().parent

if __name__ == '__main__':
    files = json.loads((B / 'integration.json').read_text())['files']
    for slug, source in zip(['ContainerHull', 'LogVolume', 'PrimeToOrder', 'Weierstrass', 'NormalizedOrder'], files):
        leaf_tag = 'platform-' + slug + '-leaf' + ('-v2' if slug == 'Weierstrass' else '')
        retry_args = ['--duration', '50s', '--memory', '4GiB', '--basis', 'ci-013835 wall35.7291s RSS2652598272 B; EOF framing end only'] if slug == 'Weierstrass' else []
        run(leaf_tag, source, *retry_args,
            '--purpose', 'Exact namespace-wrapped volume/Tate carrier on platform4.33.1')
        prior = json.loads((B / (leaf_tag + '-result.json')).read_text())['resources']
        duration = str(max(30, math.ceil(prior['wall_time_seconds'] * 1.3))) + 's'
        memory = str(min(16, max(2, math.ceil(prior['peak_rss_bytes'] / 1024**3 * 1.3)))) + 'GiB'
        run('platform-' + slug + '-artifact', source, '--artifact', '--duration', duration,
            '--memory', memory, '--basis', 'Same source artifact after accepted leaf: wall=' +
            str(prior['wall_time_seconds']) + ', RSS=' + str(prior['peak_rss_bytes']))
        print('ACCEPTED PLATFORM BUNDLE ' + slug, flush=True)
    run('kernel-audit', '.local/adaptation/reference-volume-tate-carriers-20261115/AuditNextCarriers.lean',
        '--review', '--env', 'NEXT_CARRIER_AUDIT_CONFIG=' + str(B / 'audit-config.json'),
        '--input', str(B / 'audit-config.json'), '--input', str(B / 'original-exprs.json'),
        '--purpose', 'Exact current100 required types/values/instances/axioms, complete fields/parents, and62 actual prior identities')
    run('production-gates', '.local/adaptation/reference-volume-tate-carriers-20261115/ProductionGates.lean',
        '--review', '--purpose', 'Required ImportAudit, Act1Scene1 aggregate and AxiomAudit')
