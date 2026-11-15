#!/usr/bin/env python3
"""Copy only reviewed evidence paths into an offline review tree. No Git, CI or API."""
import sys
sys.dont_write_bytecode = True
from pathlib import Path
import argparse
import gzip
import shutil
from common import ROOT, UNIT, PREFIX, DEFINITIONS, digest, exact_path, load_list, require, write_new

DRAFTS = ['common.py', 'delivery.py', 'prepare_ready.py', 'package_evidence.py',
          'finalize.py', 'delivery-README.md', 'delivery-ready.template.json',
          'delivery-blind-readbacks.template.json', 'ready-inputs.template.json']


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--input-list', type=Path, required=True)
    p.add_argument('--extra-list', type=Path, action='append', default=[])
    p.add_argument('--finalization-dir', type=Path,
                   help='Optional finalized registry candidate and finalization-summary.json directory')
    p.add_argument('--out', required=True, type=Path, help='New review directory outside the repository')
    a = p.parse_args()
    require(not a.out.resolve().is_relative_to(ROOT.resolve()), 'Review output must be outside the repository')
    require(not a.out.exists(), 'Output already exists; use a new directory')
    names = load_list(a.input_list)
    for extension in a.extra_list:
        names += load_list(extension)
    require(len(names) == len(set(names)), 'Duplicate evidence path across lists')
    selected = set(names)
    # Only enumerate names for completeness; never read unlisted inputs.
    current_receipts = {str(p.relative_to(UNIT)) for p in UNIT.rglob('*')
        if p.is_file() and '__pycache__' not in p.parts and
        (p.name.endswith(('-request.json', '-submit.json', '-result.json')) or
         ('attempts' in p.relative_to(UNIT).parts and p.suffix == '.lean'))}
    require(current_receipts <= selected, 'Review and explicitly add new attempts: ' + str(sorted(current_receipts - selected)))
    inputs = [(PREFIX + '/' + n, exact_path(UNIT, n)) for n in names]
    inputs += [(n, exact_path(ROOT, n)) for n in DEFINITIONS]
    def add_input(name, source):
        existing = [p for target, p in inputs if target == name]
        if existing:
            require(len(existing) == 1 and digest(existing[0]) == digest(source),
                    'Different evidence bytes share a final path: ' + name)
        else:
            inputs.append((name, source))
    draft_base = Path(__file__).resolve().parent
    for n in DRAFTS:
        add_input(PREFIX + '/' + n, exact_path(draft_base, n))
    for listing in a.extra_list:
        add_input(PREFIX + '/' + listing.name, listing.resolve())
    if a.finalization_dir:
        for n in ['finalization-summary.json', 'registry-update-scope.json']:
            add_input(PREFIX + '/' + n, exact_path(a.finalization_dir, n))
        candidate = exact_path(a.finalization_dir, 'platform-node-registry.candidate.json')
        require(candidate.read_bytes() == (ROOT / 'prove2me_workspace/.local/adaptation/platform-node-registry.json').read_bytes(),
                'Registry candidate has not been installed exactly; registry cannot enter allowlist')
        add_input('prove2me_workspace/.local/adaptation/platform-node-registry.json', candidate)
    require(len({n for n, _ in inputs}) == len(inputs), 'Duplicate final path')
    a.out.mkdir(parents=True)
    manifest, stage = [], []
    for name, source in sorted(inputs):
        rel = Path(name).relative_to(PREFIX) if name.startswith(PREFIX + '/') else None
        # Raw Expr, compiler/parser/runtime inputs and historical Lean always travel compressed.
        compressed = rel is not None and (source.stat().st_size > 65536 or source.suffix == '.lean' or
            source.suffix == '.diff' or rel.parts[0] == 'parser-output' or
            rel.parts[0].startswith('small-oracle-') or
            (source.stat().st_size <= 65536 and source.read_bytes().endswith(b'\n\n')))
        if compressed:
            target_name = PREFIX + '/archives/' + rel.as_posix() + '.gz'
        else:
            target_name = name
        target = a.out / target_name
        target.parent.mkdir(parents=True, exist_ok=True)
        if compressed:
            with source.open('rb') as src, target.open('xb') as dst:
                with gzip.GzipFile(filename='', mode='wb', fileobj=dst, mtime=0) as gz:
                    shutil.copyfileobj(src, gz)
            import hashlib
            h = hashlib.sha256()
            with gzip.open(target, 'rb') as expanded:
                for chunk in iter(lambda: expanded.read(1024 * 1024), b''):
                    h.update(chunk)
            require(h.hexdigest() == digest(source), 'Lossless verification failed: ' + name)
        else:
            shutil.copyfile(source, target)
            require(digest(source) == digest(target), 'Copy differs: ' + name)
        manifest.append({'original': name, 'packaged': target_name, 'original_bytes': source.stat().st_size,
                         'original_sha256': digest(source), 'packaged_sha256': digest(target),
                         'encoding': 'gzip' if compressed else 'identity', 'lossless_verified': True})
        stage.append(target_name)
    for n in ['archive-manifest.json', 'staging-allowlist.json']:
        stage.append(PREFIX + '/' + n)
    write_new(a.out / PREFIX / 'archive-manifest.json', {
        'schema': 'reference-volume-tate-lossless-evidence-v3', 'entries': manifest,
        'note': 'Original files are untouched. Expand each gzip to its original path when replaying.'})
    write_new(a.out / PREFIX / 'staging-allowlist.json', sorted(stage))
    print('Prepared exact review tree:', a.out, 'paths:', len(stage))


if __name__ == '__main__':
    main()
