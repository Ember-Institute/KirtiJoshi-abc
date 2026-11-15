#!/usr/bin/env python3
"""Write one immutable-source oracle configuration per selected module; no jobs."""
import argparse
import json
from pathlib import Path
from carrier_contract import MODULES, load, require, sha
from wrap_carriers import SEMANTIC_OPTIONS
TASK = Path(__file__).resolve().parent


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--small-source-report', required=True)
    p.add_argument('--out', required=True)
    args = p.parse_args()
    out = Path(args.out).resolve()
    require(out == TASK or TASK in out.parents, 'Output outside task directory')
    report = load(args.small_source_report)
    require(report['status'] == 'small-source-draft-generated-needs-main-CI', 'Small sources not generated from accepted parser')
    entries = {e['module']: e for e in report['modules']}
    require(set(entries) == set(MODULES), 'Small-source module set differs')
    outputs = []
    for module, slug in MODULES.items():
        e = entries[module]
        require(sha(e['source']) == e['sourceSha256'], 'Small source changed')
        data = Path(e['source']).read_bytes()
        require(data == data.replace(b'\r\n', b'\n'), 'Expected normalized small-source bytes')
        config = {'outputDir': str(out / ('small-oracle-' + slug)), 'namePrefixes': [],
                  'options': SEMANTIC_OPTIONS, 'files': [{'module': module, 'file': module.replace('.', '/') + '.lean',
                  'source': str(Path(e['source']).resolve()), 'sourceSha256': sha(e['source']),
                  'normalizedSha256': sha(e['source'])}]}
        path = out / ('small-oracle-' + slug + '-config.json')
        outputs.append((path, config))
    out.mkdir(parents=True, exist_ok=True)
    for path, config in outputs:
        path.write_text(json.dumps(config, ensure_ascii=False, indent=2) + '\n')
    print(json.dumps({'status': 'five-single-source-configurations-only', 'configs': [str(p) for p, _ in outputs],
                      'schedulerRuntimePolicy': 'Submit one configuration per process, sequentially; never batch frontend lifetimes'}, indent=2))


if __name__ == '__main__':
    main()
