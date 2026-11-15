"""Explicit provenance for the three supplier files; no compiler or source edits.
The root supplies actual final bytes and exact edits. Original metadata is immutable.
"""
from pathlib import Path
import hashlib
import json


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def _digest(data):
    return hashlib.sha256(data).hexdigest()


def build(baseline, final, original_metadata, edits, equation_source=None):
    """Return a reviewable new record; do not alter either source or old metadata.
Edits use baseline UTF-8 offsets: start/end, removed text, replacement text,
and kind (adaptation_header_cleanup or source_equation_generation).
"""
    baseline, final, original_metadata = map(Path, [baseline, final, original_metadata])
    before, after = baseline.read_bytes(), final.read_bytes()
    metadata = json.loads(original_metadata.read_text())
    expected = (metadata.get('source') or metadata.get('file'))['sha256']
    if _digest(before) != expected:
        raise ValueError('Baseline no longer matches original source-AST metadata')
    rows = sorted(edits, key=lambda e: (e['start'], e['end']))
    previous = -1
    pieces, cursor = [], 0
    checked = []
    for e in rows:
        a, b = e['start'], e['end']
        if not (0 <= a <= b <= len(before)) or a < previous:
            raise ValueError('Edit ranges overlap or are outside baseline')
        if e['kind'] not in {'adaptation_header_cleanup', 'source_equation_generation', 'adaptation_trailing_whitespace'}:
            raise ValueError('This unit admits only header cleanup and its native reserved equation generation')
        old, new = e['removed'].encode(), e['replacement'].encode()
        if before[a:b] != old:
            raise ValueError('Explicit removed bytes differ')
        if e['kind'] == 'adaptation_header_cleanup':
            if a != 0 or not old.startswith(b'/- Adaptation draft') or not old.rstrip().endswith(b'-/'):
                raise ValueError('Header cleanup must name the original adaptation-only comment')
            if b'Copyright' in old or b'Copyright' in new:
                raise ValueError('Original copyright/license notices must remain outside cleanup')
        elif e['kind'] == 'adaptation_trailing_whitespace':
            if a != len(before) or b != len(before) or old or new.strip():
                raise ValueError('Only explicit trailing whitespace is admitted')
        else:
            if a != b or old or equation_source is None:
                raise ValueError('Native reserved equation generation is an explicit insertion with original Expr evidence')
            commands = [line.strip() for line in e['replacement'].splitlines()]
            if 'attribute [local simp] epsilonE.eq_1' not in commands:
                raise ValueError('Record the actual local attribute command; no handwritten equation theorem or diagnostic #check substitute')
            if 'NumericInputs' not in final.name:
                raise ValueError('Reserved equation generation belongs only to the NumericInputs owner')
            if equation_source['originalName'] != 'Iut.epsilonE.eq_1':
                raise ValueError('Unexpected helper source Name')
            if sha(equation_source['sourceExprFile']) != equation_source['sourceExprSha256'] or sha(equation_source['sourceExportReceipt']) != equation_source['sourceExportReceiptSha256']:
                raise ValueError('Original source equation evidence changed')
            exported = json.loads(Path(equation_source['sourceExprFile']).read_text())
            records = [r for r in exported['records'] if r['name'] == 'Iut.epsilonE.eq_1']
            receipt = json.loads(Path(equation_source['sourceExportReceipt']).read_text())
            if len(records) != 1 or records[0] != equation_source['sourceRecord'] or exported['compilerVersion'] != '4.35.0-rc3' or receipt['status'] != 'succeeded' or receipt['result']['exit_code'] != 0:
                raise ValueError('Actual source equation record/export is not accepted')
        pieces.extend([before[cursor:a], new])
        cursor, previous = b, b
        checked.append(dict(e, removedSha256=_digest(old), replacementSha256=_digest(new)))
    pieces.append(before[cursor:])
    if b''.join(pieces) != after:
        raise ValueError('Explicit edits do not exactly produce final native bytes')

    def moved(pos, start):
        delta = 0
        for e in rows:
            a, b = e['start'], e['end']
            if (a < b and b <= pos) or (a == b and (a < pos or (a == pos and start))):
                delta += len(e['replacement'].encode()) - (b - a)
        return pos + delta

    commands = []
    for command in metadata['commandMaps']:
        a, b = command['outputStart'], command['outputEnd']
        for e in rows:
            x, y = e['start'], e['end']
            if (x < y and max(x, a) < min(y, b)) or (x == y and a < x < b):
                raise ValueError('Revision edits an original source AST command')
        x, y = moved(a, True), moved(b, False)
        if before[a:b] != after[x:y]:
            raise ValueError('Original source command bytes no longer agree')
        hash_field = 'originalSha256' if 'originalSha256' in command else 'sourceSha256'
        if hash_field not in command:
            raise ValueError('Original command hash field is absent from source metadata')
        commands.append({'sourceOriginalRange': command['originalRange'],
            'baselineOutputRange': [a, b], 'finalOutputRange': [x, y],
            'originalCommandSha256': command[hash_field],
            'originalMetadataHashField': hash_field,
            'preservedOutputCommandSha256': _digest(before[a:b]),
            'bytesUnchanged': True})
    notice = b'Copyright (c) 2026 '
    if before.count(notice) != after.count(notice) or b'Released under Apache 2.0 license' not in after:
        raise ValueError('Original notices changed or vanished')
    result = {'schema': 'small-supplier-explicit-revision-provenance/v1',
        'baseline': {'path': str(baseline.resolve()), 'sha256': _digest(before)},
        'final': {'path': str(final.resolve()), 'sha256': _digest(after)},
        'originalSourceAstMetadata': {'path': str(original_metadata.resolve()), 'sha256': sha(original_metadata)},
        'edits': checked, 'preservedSourceCommands': commands,
        'equationSource': equation_source, 'originalMetadataRewritten': False,
        'allOriginalCommandBytesPreserved': True,
        'rootKernelIdentityAcceptance': 'Must separately bind final native bytes and the actual 38-record source identity result.'}
    return result


def verify(record, current, metadata):
    """Replay recorded edits and compare a live source; return preserved command map."""
    if record['schema'] != 'small-supplier-explicit-revision-provenance/v1':
        raise ValueError('Wrong revision record schema')
    old = record['originalSourceAstMetadata']
    if Path(old['path']).resolve() != Path(metadata).resolve() or sha(metadata) != old['sha256']:
        raise ValueError('Original metadata was silently replaced or re-hashed')
    if sha(record['baseline']['path']) != record['baseline']['sha256']:
        raise ValueError('Baseline evidence changed')
    if sha(current) != record['final']['sha256']:
        raise ValueError('Revision does not bind current native bytes')
    rebuilt = build(record['baseline']['path'], current, metadata, record['edits'], record['equationSource'])
    if rebuilt['preservedSourceCommands'] != record['preservedSourceCommands']:
        raise ValueError('Recorded original command mapping differs')
    return rebuilt['preservedSourceCommands']
