#!/usr/bin/env python3
"""Offline lossless evidence tree, adapted from the volume/tate package_evidence.py.
Only explicitly reviewed paths in input-list.json are read and copied. No CI/API/Git.
"""
import sys
sys.dont_write_bytecode = True
from pathlib import Path
import argparse
import gzip
import hashlib
import json
import shutil

ROOT=Path('/home/admin-wsl/Coq/abc')
PREFIX='prove2me_workspace/.local/adaptation/main-c22-numeric-helpers-20261115'

def digest(path):
    h=hashlib.sha256()
    with Path(path).open('rb') as source:
        for chunk in iter(lambda:source.read(1024*1024),b''):
            h.update(chunk)
    return h.hexdigest()

def write(path,value):
    path.parent.mkdir(parents=True,exist_ok=True)
    path.write_text(json.dumps(value,ensure_ascii=False,indent=2)+'\n')

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--input-list',type=Path,required=True)
    parser.add_argument('--out',type=Path,required=True)
    parser.add_argument('--installed-package-tree',type=Path,help='Prior exact review tree already copied by root; ignore only byte-identical generated outputs')
    args=parser.parse_args()
    out=args.out.resolve()
    assert not out.is_relative_to(ROOT.resolve()) and not out.exists()
    inputs=json.loads(args.input_list.read_text())
    assert inputs['schema']=='numeric-final-evidence-input-list-v1'
    rows=inputs['files']
    assert len({r['original']for r in rows})==len(rows)
    installed={}
    if args.installed_package_tree:
        for path in args.installed_package_tree.rglob('*'):
            if path.is_file():installed[str(path.relative_to(args.installed_package_tree))]=path
    # Enumerate only to catch a late receipt; never silently discard a failure.
    for selected_root in inputs['selected_roots']:
        directory=ROOT/selected_root
        current={str(p.relative_to(ROOT))for p in directory.rglob('*')if p.is_file()and not excluded(p)}
        expected={r['original']for r in rows if r['original'].startswith(selected_root+'/')}
        extras=current-expected
        for name in extras:
            assert name in installed and digest(ROOT/name)==digest(installed[name]),('Unreviewed new input',name)
        assert expected<=current,('Original reviewed input missing',selected_root,sorted(expected-current))
    out.mkdir(parents=True)
    manifest=[]
    for row in rows:
        name=row['original'];source=ROOT/name
        assert source.is_file() and not source.is_symlink() and not excluded(source)
        assert digest(source)==row['sha256'] and source.stat().st_size==row['bytes'],('Input changed',name)
        # Same deterministic gzip and byte round-trip verification as the reviewed
        # volume/tate packaging scheme; PNGs and small structured receipts stay raw.
        raw=source.read_bytes()
        try:
            raw.decode('utf-8')
            whitespace_sensitive=(any(line.endswith((b' ',b'\t',b'\r')) for line in raw.split(b'\n'))
                                  or raw.endswith(b'\n\n') or raw.endswith(b'\r\n\r\n'))
        except UnicodeDecodeError:
            whitespace_sensitive=False
        compressed=source.stat().st_size>65536 or source.suffix in ['.lean','.diff','.jsonl'] or whitespace_sensitive
        parent=next(p for p in inputs['selected_roots']if name.startswith(p+'/'))
        relative=Path(name).relative_to(parent)
        target_name=parent+'/archives/'+relative.as_posix()+'.gz' if compressed else name
        target=out/target_name;target.parent.mkdir(parents=True,exist_ok=True)
        if compressed:
            with source.open('rb')as src,target.open('xb')as dst:
                with gzip.GzipFile(filename='',mode='wb',fileobj=dst,mtime=0)as gz:
                    shutil.copyfileobj(src,gz)
            h=hashlib.sha256()
            with gzip.open(target,'rb')as expanded:
                for chunk in iter(lambda:expanded.read(1024*1024),b''):h.update(chunk)
            assert h.hexdigest()==row['sha256'],('Lossless verification failed',name)
        else:
            shutil.copyfile(source,target)
            assert digest(target)==row['sha256']
        manifest.append({'original':name,'packaged':target_name,'original_bytes':row['bytes'],
                         'original_sha256':row['sha256'],'packaged_bytes':target.stat().st_size,
                         'packaged_sha256':digest(target),'encoding':'gzip'if compressed else'identity',
                         'lossless_verified':True,'restoration_path':name})
    base=out/PREFIX
    write(base/'archive-manifest.json',{'schema':'numeric-final-lossless-evidence-v1','entries':manifest,
         'note':'Original inputs untouched. Restore each gzip to original/restoration_path and verify original_sha256 before replay.'})
    controls=['input-list.json','external-evidence-index.json','already-tracked-reuse.json',
              'paper-pdf-locators.json','final-publication-registry-review.json']
    for name in controls:
        source=args.input_list.parent/name
        if source.is_file():shutil.copyfile(source,base/name)
    shutil.copyfile(Path(__file__),base/'package_evidence.py')
    allpaths=[str(p.relative_to(out))for p in out.rglob('*')if p.is_file()]
    allpaths.append(PREFIX+'/staging-allowlist.json')
    write(base/'staging-allowlist.json',sorted(allpaths))
    print(json.dumps({'out':str(out),'input_files':len(manifest),'original_bytes':sum(r['original_bytes']for r in manifest),
                      'packaged_bytes':sum(r['packaged_bytes']for r in manifest),'gzip_files':sum(r['encoding']=='gzip'for r in manifest),
                      'lossless_verified':True,'staging_paths':len(allpaths)},ensure_ascii=False))

def excluded(path):
    return bool(set(path.parts)&{'__pycache__','.lake','.git','node_modules'}) or path.suffix in ['.pyc','.olean','.ilean','.trace'] or path.name in ['credentials.json','.env']

if __name__=='__main__':main()
