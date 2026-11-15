"""Main-agent exclusive platform leaves, artifacts and required audit gates."""
from pathlib import Path
import json, math
from run_queries import run

B = Path(__file__).resolve().parent

if __name__ == '__main__':
    files = json.loads((B / 'integration.json').read_text())['files']
    for slug, source in zip(['Container', 'HolomorphicHull', 'GlobalField', 'PlacesOver', 'QParameterBasic'], files):
        run('platform-' + slug + '-leaf', source,
            '--purpose', 'Exact namespace-wrapped packet/global-field carrier on platform4.33.1')
        prior = json.loads((B / ('platform-' + slug + '-leaf-result.json')).read_text())['resources']
        duration = str(max(30, math.ceil(prior['wall_time_seconds'] * 1.3))) + 's'
        memory = str(min(16, max(2, math.ceil(prior['peak_rss_bytes'] / 1024**3 * 1.3)))) + 'GiB'
        run('platform-' + slug + '-artifact', source, '--artifact', '--duration', duration,
            '--memory', memory, '--basis', 'Same source artifact after accepted leaf: wall=' +
            str(prior['wall_time_seconds']) + ', RSS=' + str(prior['peak_rss_bytes']))
        print('ACCEPTED PLATFORM BUNDLE ' + slug, flush=True)
    run('kernel-audit', '.local/adaptation/reference-packet-field-carriers-20261115/AuditNextCarriers.lean',
        '--review', '--env', 'NEXT_CARRIER_AUDIT_CONFIG=' + str(B / 'audit-config.json'),
        '--input', str(B / 'audit-config.json'), '--input', str(B / 'original-exprs.json'),
        '--purpose', 'Exact new133 mandatory types/values/instances/axioms with actual prior110 dependencies')
    run('production-gates', '.local/adaptation/reference-packet-field-carriers-20261115/ProductionGates.lean',
        '--review', '--purpose', 'Required ImportAudit, Act1Scene1 aggregate and AxiomAudit')
