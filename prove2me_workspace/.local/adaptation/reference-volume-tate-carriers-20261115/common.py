"""Offline path and JSON helpers; importing this module has no side effects."""
from pathlib import Path
import hashlib
import json

ROOT = Path('/home/admin-wsl/Coq/abc')
WORKSPACE = ROOT / 'prove2me_workspace'
UNIT = WORKSPACE / '.local/adaptation/reference-volume-tate-carriers-20261115'
REGISTRY = WORKSPACE / '.local/adaptation/platform-node-registry.json'
PREFIX = UNIT.relative_to(ROOT).as_posix()
MODULES = ['Iut.Cor312.ContainerHull', 'Iut.Cor312.LogVolume', 'TateCurvesTheta.QParameter.PrimeToOrder', 'TateCurvesTheta.TateCurve.Weierstrass', 'TateCurvesTheta.QParameter.NormalizedOrder']
NAMES = ['AbcAdaptation_Reference_' + n.replace('.', '_') for n in MODULES]
DEFINITIONS = ['prove2me_workspace/Definitions/Def_' + n + '.lean' for n in NAMES]
TERMINAL = {'succeeded', 'failed', 'timeout', 'oom_killed', 'cancelled', 'interrupted', 'scheduler_error'}


def require(ok, message):
    if not ok:
        raise ValueError(message)


def read(path):
    return json.loads(Path(path).read_text(encoding='utf-8'))


def digest(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b''):
            h.update(chunk)
    return h.hexdigest()


def exact_path(base, name):
    p = Path(name)
    require(isinstance(name, str) and not p.is_absolute() and p.as_posix() == name
            and '\\' not in name and not {'.', '..', '__pycache__', '.git', '.lake'} & set(p.parts),
            'Invalid allowlist path: ' + str(name))
    require(p.suffix not in {'.pyc', '.lock', '.tmp'} and
            not any(token in p.name.lower() for token in ['credential', 'secret', 'token', '.env']),
            'Excluded input: ' + name)
    full = base / p
    require(all(not ancestor.is_symlink() for ancestor in [full, *full.parents] if ancestor != base.parent),
            'Symlink input: ' + name)
    require(full.resolve().is_relative_to(base.resolve()) and full.is_file(), 'Missing regular input: ' + name)
    return full


def load_list(path):
    rows = read(path)
    require(isinstance(rows, list) and rows and all(isinstance(n, str) for n in rows), 'Expected path list')
    require(len(rows) == len(set(rows)), 'Duplicate allowlist paths')
    return rows


def write_new(path, value):
    path = Path(path)
    data = (json.dumps(value, ensure_ascii=False, indent=2) + '\n').encode()
    path.parent.mkdir(parents=True, exist_ok=True)
    if path.exists():
        require(path.read_bytes() == data, 'Refusing to overwrite different output: ' + str(path))
    else:
        with path.open('xb') as f:
            f.write(data)
