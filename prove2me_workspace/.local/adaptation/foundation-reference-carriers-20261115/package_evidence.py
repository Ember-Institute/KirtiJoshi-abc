"""Lossless archives for large receipts and exact historical compiler inputs."""
from pathlib import Path
import gzip, hashlib, json, subprocess

B = Path(__file__).resolve().parent
R = B.parents[3]
sha = lambda data: hashlib.sha256(data).hexdigest()
archives, stage = [], []
for path in sorted(B.rglob('*')):
    if not path.is_file() or '__pycache__' in path.parts or 'archives' in path.relative_to(B).parts:
        continue
    if path.suffix in ['.lock', '.tmp', '.pyc']:
        continue
    relative = path.relative_to(B)
    if path.name in ['archive-manifest.json', 'staging-allowlist.json']:
        continue
    historical_lean = path.suffix == '.lean' and len(relative.parts) > 1
    data = path.read_bytes()
    # Preserve compiler bytes even when the original input ends in blank lines.
    whitespace_lean = path.suffix == '.lean' and (data.endswith(b'\n\n') or
        any(line.endswith((b' ', b'\t')) for line in data.splitlines()))
    if len(data) > 65536 or historical_lean or whitespace_lean:
        target = B / 'archives' / (str(relative) + '.gz')
        target.parent.mkdir(parents=True, exist_ok=True)
        with target.open('wb') as stream:
            with gzip.GzipFile(filename='', mode='wb', fileobj=stream, mtime=0) as compressed:
                compressed.write(data)
        assert gzip.decompress(target.read_bytes()) == data
        archives.append({'original': str(relative), 'archive': str(target.relative_to(B)),
            'originalBytes': len(data), 'originalSha256': sha(data),
            'archiveSha256': sha(target.read_bytes()), 'losslessVerified': True})
        stage.append(str(target.relative_to(R)))
    else:
        stage.append(str(path.relative_to(R)))
(B / 'archive-manifest.json').write_text(json.dumps({'schema': 'foundation-lossless-evidence-archives-v1',
    'entries': archives, 'note': 'Compiler inputs and outputs are preserved byte-for-byte. Expand the named archive to its original path when replaying an audit.'}, ensure_ascii=False, indent=2) + '\n')
stage += [str((B / name).relative_to(R)) for name in ['archive-manifest.json', 'staging-allowlist.json']]
integration = json.loads((B / 'integration.json').read_text())
stage += ['prove2me_workspace/' + source for source in integration['files']]
stage += ['docs/三语术语名词关键对照.md']
stage = sorted(set(stage))
(B / 'staging-allowlist.json').write_text(json.dumps(stage, ensure_ascii=False, indent=2) + '\n')
existing = subprocess.check_output(['git', '-c', 'core.quotePath=false', 'diff', '--cached', '--name-only'], cwd=R, text=True).splitlines()
unit_prefix = str(B.relative_to(R)) + '/'
obsolete = [p for p in existing if p.startswith(unit_prefix) and p not in stage]
if obsolete:
    subprocess.run(['git', 'restore', '--staged', '--', *obsolete], cwd=R, check=True)
subprocess.run(['git', 'add', '-f', '--', *stage], cwd=R, check=True)
print(json.dumps({'stagedPaths': len(stage), 'losslessArchives': len(archives)}))
