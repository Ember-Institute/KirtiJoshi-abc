"""Apply one user-approved Chinese term; no import-time writes or API calls."""
from copy import deepcopy
import json
from pathlib import Path

MARKER = '【译名待定：DIFFERENT-IDEAL】'
TRANSLATION = '不同理想'
PREFIX = 'AbcAdaptation.Tripod.Fermat.Proper.'
EXPECTED_NAMES = {PREFIX + name for name in [
    'BelyiActualFieldDifferentAccounting', 'BelyiActualFieldLocalConductorComparison',
    'ConductorExtensionSource.diffContrib', 'ConductorExtensionSource.diffContrib_nonneg',
    'ConductorExtensionSource.finiteSetLogCond_le_of_local_and_accounting',
    'ConductorExtensionSource.sum_diffContrib_le_of_accounting',
    'belyiActualFieldConductorExtension',
    'belyiActualFieldConductorExtension_of_local_and_accounting',
    'belyiActualFieldDifferentAccounting', 'belyiActualFieldLocalConductorComparison']}


def approved_text(text):
    return text.replace(MARKER, TRANSLATION)


def approval(unit):
    evidence = json.loads((Path(unit) / 'terminology-resolution.json').read_text())
    assert evidence['term'] == 'different ideal'
    assert evidence['placeholder'] == MARKER and evidence['translation'] == TRANSLATION
    assert evidence['user_approval']['confirmed'] is True
    assert set(evidence['declarations']) == EXPECTED_NAMES
    return evidence


def resolve_rows(rows, unit):
    """Change only zh_Hans in exactly ten declaration rows; retain old prose."""
    approval(unit)
    out = deepcopy(rows)
    actual = {z['declaration'] for z in out if MARKER in z['zh_Hans'] or
              'superseded_pending_translation' in z}
    assert actual == EXPECTED_NAMES, ('Unexpected pending-term declarations', actual)
    for row in out:
        if row['declaration'] not in EXPECTED_NAMES:
            continue
        previous = row.get('superseded_pending_translation', row['zh_Hans'])
        assert MARKER in previous
        assert row['zh_Hans'] in [previous, approved_text(previous)]
        row['superseded_pending_translation'] = previous
        row['zh_Hans'] = approved_text(previous)
        row['terminology_resolution'] = 'terminology-resolution.json'
    assert all(MARKER not in z['zh_Hans'] for z in out)
    return out
