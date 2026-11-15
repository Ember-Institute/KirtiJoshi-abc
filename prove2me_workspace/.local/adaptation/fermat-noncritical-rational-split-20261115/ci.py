"""Submit or collect one exclusive scheduler job. Never invoke a compiler here."""
from pathlib import Path
import argparse, copy, hashlib, json, subprocess, sys

B = Path(__file__).resolve().parent
W = B.parents[2]
R = W.parent
sys.path.insert(0, str(B.parent / 'cusp-conductor-sourceproof-20261115'))
from scheduler_common import rpc

def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def save(name, value):
    path = B / name
    temporary = path.with_suffix(path.suffix + '.tmp')
    temporary.write_text(json.dumps(value, ensure_ascii=False, indent=2) + '\n')
    temporary.replace(path)

def submit(args):
    template = (B.parent / 'main-c22-numeric-reference-split-20261115/parser-ranges-request.json'
        if args.original else B.parent / 'reference-extraction-20261115/production-gates-request.json')
    q = copy.deepcopy(json.loads(template.read_text()))
    source = str(Path(args.source).relative_to(W)) if Path(args.source).is_absolute() else args.source
    q['environment'] = {k: v for k, v in q['environment'].items() if k in ['LEAN_PATH', 'PATH']}
    for entry in args.env:
        key, value = entry.split('=', 1)
        q['environment'][key] = value
    output = None
    if args.artifact:
        output = W / '.lake/build/lib/lean' / Path(source).with_suffix('.olean')
        output.parent.mkdir(parents=True, exist_ok=True)
    q.update(task_type='full' if output or args.runtime_config else 'review' if args.review else 'leaf',
        target='module' if output or args.runtime_config else 'file',
        parameters={'args': ['--run', source, args.runtime_config]} if args.runtime_config else
            {'args': [source, '-o', str(output.relative_to(W))]} if output else {'source': source},
        expected_duration=args.duration, expected_memory=args.memory,
        session_id='p2m-fermat-noncritical-rational-split-20261115', agent_id='/root', exclusive=True)
    q.pop('snapshot_inputs', None)
    q.pop('working_directory', None)
    m = q['worktree_manifest']
    git = lambda *xs: subprocess.check_output(['git', '-c', 'core.quotePath=false', *xs], cwd=R, text=True)
    inputs = [W / source] + [Path(p).resolve() for p in args.input]
    m.update(worktree_id=str(R), head=git('rev-parse', 'HEAD').strip(),
        modified_files=git('diff', 'HEAD', '--name-only').splitlines(),
        untracked_files=git('ls-files', '--others', '--exclude-standard').splitlines(),
        input_hashes={str(p): sha(p) for p in inputs}, source_sha256=sha(W / source),
        required_artifacts=q['environment']['LEAN_PATH'].split(':'),
        purpose=args.purpose, effective_compiler='leanprover/lean4:v4.35.0-rc3' if args.original else 'leanprover/lean4:v4.33.1',
        resource_estimate_basis=args.basis)
    m.pop('source_compiler_input_sha256', None)
    request_hash = hashlib.sha256(json.dumps(q, sort_keys=True, separators=(',', ':')).encode()).hexdigest()
    q['idempotency_key'] = 'p2m-fermat-rational-' + args.tag + '-' + request_hash[:20]
    request = B / (args.tag + '-request.json')
    submitted = B / (args.tag + '-submit.json')
    if request.exists():
        assert json.loads(request.read_text()) == q, 'Request changed; use a new attempt tag'
    else:
        save(request.name, q)
    if submitted.exists():
        z = json.loads(submitted.read_text())
    else:
        z = rpc('ci_submit', q)
        save(submitted.name, z)
    print(json.dumps(z, ensure_ascii=False))

def collect(args):
    z = json.loads((B / (args.tag + '-submit.json')).read_text())
    z = rpc('ci_wait', {'job_id': z['job_id'], 'timeout_seconds': 20})
    if z['status'] in ['queued', 'running', 'preparing_snapshot']:
        print(json.dumps({k: z.get(k) for k in ['job_id', 'status', 'compile_time_seconds']}))
        return
    z = rpc('ci_result', {'job_id': z['job_id']})
    save(args.tag + '-result.json', z)
    result = z['result']
    resources = z.get('resources', {})
    report = {k: z.get(k) for k in ['job_id', 'status']}
    report.update(resources=resources, exit_code=result.get('exit_code'),
        actual_arguments=result.get('actual_arguments'),
        workspace_mode=result.get('snapshot', {}).get('workspace_mode'),
        snapshot_id=result.get('snapshot', {}).get('snapshot_id'),
        stdout=result.get('stdout', '')[-6000:], stderr=result.get('stderr', '')[-2500:])
    print(json.dumps(report, ensure_ascii=False))
    if z['status'] != 'succeeded':
        raise SystemExit(1)
    assert result['exit_code'] == 0
    assert result['snapshot']['workspace_mode'] == 'exclusive_worktree'
    assert result['snapshot']['snapshot_id'] is None
    assert not any(s in result.get('stdout', '') + result.get('stderr', '') for s in ['PANIC', 'error:', 'error('])
    assert resources.get('peak_rss_bytes') is not None
    assert resources['peak_rss_bytes'] <= 16 * 1024**3
    cpu, user, system = [resources.get(k) for k in ['cpu_time_seconds', 'cpu_user_seconds', 'cpu_system_seconds']]
    if all(v is not None for v in [cpu, user, system]):
        assert abs(cpu - user - system) < 0.1
    q = z['request']
    p = q['parameters']
    assert result['actual_arguments'] == ['lean', *([p['source']] if 'source' in p else p['args'])]
    if q['task_type'] == 'review':
        assert result['review']['passed']

if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    sub = p.add_subparsers(dest='action', required=True)
    s = sub.add_parser('submit')
    s.add_argument('tag'); s.add_argument('source')
    s.add_argument('--original', action='store_true')
    s.add_argument('--artifact', action='store_true')
    s.add_argument('--runtime-config')
    s.add_argument('--review', action='store_true')
    s.add_argument('--env', action='append', default=[])
    s.add_argument('--input', action='append', default=[])
    s.add_argument('--duration', default='60s'); s.add_argument('--memory', default='16GiB')
    s.add_argument('--purpose', default='Fermat rational-case source decomposition')
    s.add_argument('--basis', default='New leaf first60s/16GiB')
    c = sub.add_parser('collect'); c.add_argument('tag')
    args = p.parse_args()
    (submit if args.action == 'submit' else collect)(args)
