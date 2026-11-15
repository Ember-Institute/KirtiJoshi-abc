#!/usr/bin/env python3
"""Root-run P5 packaging only. Default: report; --apply: package and clean whitelist.
No API, Git, compilation, MCP-CI, or large-export traversal.
"""
from pathlib import Path
import argparse
import hashlib
import json
import shutil
import tarfile

ROOT = Path('/home/admin-wsl/Coq/abc')
ADAPT = ROOT / 'prove2me_workspace/.local/adaptation'
CHAIN = ADAPT / 'main-chain-open-20261116'
DELIVERY = ADAPT / 'p5-height-reference-proof-delivery-20261116'
AUDIT = ADAPT / 'main-pure-type-identity-20261116'
PREP = Path('/tmp/p2m-main-p5-publisher-v9-20261116')
OUTPUT = DELIVERY / 'packaging-final-v11-20261116'
NAME = 'Thm_AbcAdaptation_Reference_Iut_p5_height_bound.lean'
SOL = 'Sol_AbcAdaptation_Reference_Iut_p5_height_bound.lean'
ORIGINAL_SHA = '7dcecf82656f25dea019a2d360e9170f6ae47c024a99331972641deb7e72196c'
MAX_INPUT_BYTES = 16 * 1024 * 1024

# Only these eight reviewed P5 draft files may be removed.
REMOVE = {
    CHAIN / 'pure-helper-candidates/Theorems' / NAME: '07fa23ab86541055564a7df7fa5e14cf7591232f488714bf500b6253a6c666ca',
    CHAIN / 'pure-helper-candidates/formal-only/Theorems' / NAME: '39aadd1f0097276cf3ccc14173646cd25edaddfb054a3bc7c8ea972c7bd9ca27',
    CHAIN / 'pure-helper-candidates/StatementStubs' / NAME: 'e0cdf37aaa5753c6209600bfbea7babfbca65565aac116e3d2fbb85bd387bd2e',
    CHAIN / 'p5-platform-packet/staging/Theorems' / NAME: 'ac8073653347ccac81186422d50a9d1b58876f260995a021582ccc0c1b964ff6',
    CHAIN / 'p5-platform-packet/staging/Solutions' / SOL: '6ef2a6e6ae082b0ef00bab5e5964c4d71cb950c7a270a3d2dc83e817fa3fc091',
    CHAIN / 'p5-platform-packet/actual-native-closed-proof-before-platform-stub.lean': '07fa23ab86541055564a7df7fa5e14cf7591232f488714bf500b6253a6c666ca',
    DELIVERY / 'staging/Theorems' / NAME: 'ac8073653347ccac81186422d50a9d1b58876f260995a021582ccc0c1b964ff6',
    DELIVERY / 'staging/Solutions' / SOL: '6ef2a6e6ae082b0ef00bab5e5964c4d71cb950c7a270a3d2dc83e817fa3fc091',
}


def digest(path):
    # File-size bound is checked before hashing any selected file.
    return hashlib.sha256(path.read_bytes()).hexdigest()


def label(path):
    try:
        return path.relative_to(ROOT).as_posix()
    except ValueError:
        return 'publisher-preparation/' + path.relative_to(PREP).as_posix()


def reviewed_files():
    files = set()
    # Every attempt, including failed source-type-facts v1. Future P5 retries
    # are included automatically, but unrelated helper jobs are excluded.
    for path in CHAIN.glob('*.json'):
        if 'p5' in path.name.lower() or path.name.startswith('source-pure-three-type-facts-'):
            files.add(path)
    audit_names = [
        'AuditP5GlobalSolution.lean', 'Audit_p5_height_bound.lean',
        'QueryPureArithmeticTypeFacts.lean', 'original-type-facts.json',
        'p5-global-solution-config.json', 'p5-global-solution-kernel-identity.json',
        'p5-height-native-config-bound.json', 'p5-height-type-identity.json',
        'source-config.json',
        'handoff/Audit_p5_height_bound.lean', 'handoff/p5_height_bound-config.json',
        'handoff/QueryPureArithmeticTypeFacts.lean', 'handoff/source-config.json',
        'handoff/source-body.lean.txt', 'handoff/native-body.lean.txt',
        'handoff/README.md', 'handoff/final-manifest.json', 'handoff/handoff.json',
        'handoff/separate-proof-evidence.json', 'handoff/prepare.py',
    ]
    files.update(AUDIT / name for name in audit_names)
    # Small P5 oracle outputs and source extraction inputs; never traverse
    # any complete environment/type export or other theorem output.
    oracle = CHAIN / 'tools/generated/oracle-output/Iut_p5_height_bound'
    files.update(path for path in oracle.rglob('*') if path.is_file())
    for category, filename in [
        ('metadata', 'Iut_p5_height_bound.json'),
        ('OriginalCommands', 'Iut_p5_height_bound.lean'),
        ('OracleSourceProbes', 'Iut_p5_height_bound.lean'),
        ('OracleConfigs', 'Iut_p5_height_bound.json'),
        ('OpenSourceDrafts', 'Iut_p5_height_bound.lean'),
        ('formal-only', 'Iut_p5_height_bound.lean'),
    ]:
        files.add(CHAIN / 'tools/generated' / category / filename)
    files.update(path for path in DELIVERY.glob('*') if path.is_file())
    files.update(path for path in (DELIVERY / 'platform').glob('*') if path.is_file())
    files.update(path for path in PREP.glob('*') if path.is_file())
    files.add(PREP / 'source-evidence/Original_p5_height_bound.lean')
    files.add(CHAIN / 'pure-helper-candidates/OriginalCommands/Iut_p5_height_bound.lean')
    files.add(CHAIN / 'pure-helper-candidates/source-metadata/Iut_p5_height_bound.json')
    # Original pre-publisher packet and its metadata remain in place.
    files.update(path for path in (CHAIN / 'p5-platform-packet').glob('*') if path.is_file())
    files.add(CHAIN / 'p5-platform-packet/source-evidence/Original_p5_height_bound.lean')
    files.add(ADAPT / 'platform-node-registry.json')
    files.add(ROOT / 'docs/开发计划.Prove2Me适配.md')
    files.add(ROOT / 'prove2me_workspace/Theorems' / NAME)
    return sorted(files - set(REMOVE), key=str)


def write_archive(destination, paths):
    with tarfile.open(destination, 'w:gz') as archive:
        for path in paths:
            archive.add(path, arcname=label(path), recursive=False)
    # Verify archived bytes before deleting any original draft.
    with tarfile.open(destination, 'r:gz') as archive:
        for path in paths:
            stream = archive.extractfile(label(path))
            if stream is None or hashlib.sha256(stream.read()).hexdigest() != digest(path):
                raise RuntimeError('Archive verification failed: ' + str(path))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--apply', action='store_true')
    args = parser.parse_args()
    if OUTPUT.exists():
        raise SystemExit('Output already exists; inspect the previous run: ' + str(OUTPUT))
    files = reviewed_files()
    all_files = files + list(REMOVE)
    missing = [str(path) for path in all_files if not path.is_file() or path.is_symlink()]
    if missing:
        raise SystemExit('Missing or symlink input: ' + json.dumps(missing, ensure_ascii=False))
    total = sum(path.stat().st_size for path in all_files)
    if total > MAX_INPUT_BYTES:
        raise SystemExit(f'Reviewed evidence grew beyond 16 MiB: {total} bytes')
    for path, expected in REMOVE.items():
        if digest(path) != expected:
            raise SystemExit('Reviewed draft changed; do not delete: ' + str(path))
    source = PREP / 'source-evidence/Original_p5_height_bound.lean'
    if digest(source) != ORIGINAL_SHA:
        raise SystemExit('Original source-evidence hash mismatch')
    target = DELIVERY / 'source-evidence/Original_p5_height_bound.lean'
    if target.exists() and digest(target) != ORIGINAL_SHA:
        raise SystemExit('Existing delivered original source differs')
    manifest = {
        'mode': 'apply' if args.apply else 'dry-run',
        'input_bytes': total, 'input_mib': total / 2**20,
        'compressed_archive_upper_bound_bytes': total + 1024 * len(all_files) + 1048576,
        'evidence_files': [{'source': str(path), 'archive_path': label(path),
                            'bytes': path.stat().st_size, 'sha256': digest(path)} for path in files],
        'remove_after_archive_verification': [{'source': str(path), 'archive_path': label(path),
                                             'bytes': path.stat().st_size, 'sha256': sha}
                                            for path, sha in REMOVE.items()],
        'restored_source_evidence': str(target),
        'note': 'Historical artifact-manifest/staging paths resolve inside duplicates.tar.gz; no metadata/config/audit/oracle or other-helper source is removed.',
    }
    print(json.dumps(manifest, ensure_ascii=False, indent=2))
    if not args.apply:
        return
    OUTPUT.mkdir()
    (OUTPUT / 'packaging-manifest.json').write_text(json.dumps(manifest, ensure_ascii=False, indent=2) + '\n')
    target.parent.mkdir(exist_ok=True)
    if not target.exists():
        shutil.copy2(source, target)
    write_archive(OUTPUT / 'evidence.tar.gz', files)
    write_archive(OUTPUT / 'duplicates.tar.gz', list(REMOVE))
    for path, expected in REMOVE.items():
        if digest(path) != expected:
            raise RuntimeError('Draft changed while packaging; stop before deleting: ' + str(path))
    # All input checks and both archive verifications completed.
    for path in REMOVE:
        path.unlink()
    manifest['completed'] = True
    manifest['archive_bytes'] = {name: (OUTPUT / name).stat().st_size
                                 for name in ['evidence.tar.gz', 'duplicates.tar.gz']}
    (OUTPUT / 'packaging-manifest.json').write_text(json.dumps(manifest, ensure_ascii=False, indent=2) + '\n')


if __name__ == '__main__':
    main()
