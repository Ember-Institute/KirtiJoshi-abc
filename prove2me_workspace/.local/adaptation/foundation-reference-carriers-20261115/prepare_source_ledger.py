"""Record real reference-graph consumers; no compilation or platform actions."""
from pathlib import Path
import hashlib, json

B = Path(__file__).resolve().parent
load = lambda p: json.loads(p.read_text())
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()

inventory = load(B / 'inventory.json')
wrappers = {e['module']: e for e in load(B / 'wrapped/foundation-wrapper-report.json')['bundles']}
license_audit = load(B / 'source-license-audit.json')
sources = {e['module']: e for e in license_audit['files']}
entries = []
for module in inventory['modules']:
    wrapper, source = wrappers[module['module']], sources[module['module']]
    selected = [d for d in module['declarations'] if d['selectedForBundle']]
    commands = [d for d in module['declarations'] if d['name'] in module['selectedSourceCommandCandidates']]
    for d in selected:
        assert (d['consumerPathToMainTheorem'] or d['isInstance'] or d['sourceHelper']
            or d['kind'] in ['ctor', 'rec'] or not d['sourceCommandRootCandidate']), d['name']
    first = min(d['startLine'] for d in commands)
    last = max(d['endLine'] for d in commands)
    row = {
        'producer': wrapper['definitionName'], 'kind': 'definition-bundle',
        'stage': 'Act1Scene2 reference carrier preparation',
        'owner': 'reference adaptation; no Prologue/Core boundary change',
        'originalModule': module['module'],
        'sourceURL': source['sourceURL'] + '#L' + str(first) + '-L' + str(last),
        'sourcePath': 'refer/iut/' + source['originalPath'],
        'sourceCommit': license_audit['originalCommit'],
        'author': source['author'], 'license': source['license'],
        'originalSourceSha256': source['sha256'], 'wrappedSourceSha256': wrapper['sha256'],
        'selectedSourceCommands': module['selectedSourceCommandCandidates'],
        'selectedDeclarations': [{
            'original': d['name'], 'wrapped': 'AbcAdaptation.Reference.' + d['name'],
            'kind': d['kind'], 'isInstance': d['isInstance'],
            'isSourceHelper': bool(d['sourceHelper']),
            'sourceCommandRoot': d['sourceCommandRootCandidate'],
            'actualOriginalConsumers': d['actualConsumers'],
            'originalConsumerPathToMainTheorem': d['consumerPathToMainTheorem'],
        } for d in selected],
        'actualSourceConsumer': 'Iut.Theorem110Invariants.theorem110',
        'consumerEvidence': {'graphJobId': 'ci-012771-ee109b3e',
            'graphSha256': inventory['graphSha256'], 'inventorySha256': sha(B / 'inventory.json')},
        'targetRootGraphMembership': False, 'canonicalC22Connected': False,
        'faithfulness': 'Original selected full source commands retained byte-for-byte; namespace wrapper and explicit import-path migration. Final compiler acceptance is recorded separately. Paper-object identities and arithmetic instantiation remain separate obligations.',
        'generatedDeclarationsPolicy': 'Compiler-generated companions are supplied by full original commands, not independent platform nodes. Instance roots preserve the original elaboration context even when instance terms unfold from proof dependencies.',
    }
    if module['module'].endswith('PacketPresentation'):
        row['actualCarrierScope'] = 'Arbitrary C; each Summand c has CommRing and TopologicalSpace; integral c is an arbitrary Set. The source does not require finite C, Field or TopologicalRing and does not identify integral c with an integer ring or establish tensor decomposition.'
    if module['module'].endswith('Procession'):
        row['embeddedSourceProof'] = 'Iut.procLabels_mono is retained with its exact original proof and consumed by Procession.standard.'
    if module['module'].endswith('RationalPlace'):
        row['auxiliaryReconstruction'] = {'helper': 'Iut.RationalPlace.IsFinite',
            'sharedMatcher': 'Iut.RationalPlace.IsFinite.match_1',
            'actualValueConsumer': 'Iut.RationalPlace.residueChar',
            'policy': 'Earlier IsFinite equations command retained to regenerate the matcher used by residueChar; deriving DecidableEq command retained whole.',
            'sourceOracleJobId': wrapper['sourceOracleJobId']}
    entries.append(row)
ledger = {'schema': 'foundation-source-ledger-v1', 'scope': 'detached source carrier preparation',
    'entries': entries, 'requiredDeclarationCount': sum(len(e['selectedDeclarations']) for e in entries),
    'sourceCommandCount': sum(len(e['selectedSourceCommands']) for e in entries),
    'productionUpstreamDependencyAdded': False,
    'paperSourcePolicy': 'Mochizuki original source context is separate from formal-code readback; no Joshi bridge identity is asserted.'}
assert ledger['requiredDeclarationCount'] == 83 and ledger['sourceCommandCount'] == 26
(B / 'SOURCE_LEDGER.json').write_text(json.dumps(ledger, ensure_ascii=False, indent=2) + '\n')
(B / 'SOURCE_LEDGER.md').write_text(
    '# Reference foundation carrier sources\n\n'
    'Five bundles retain 26 complete source commands and reconstruct 83 required compiler declarations. '
    'The original-source consumers and exact declaration paths to `Iut.Theorem110Invariants.theorem110` '
    'are recorded in `SOURCE_LEDGER.json`.\n\n'
    'These bundles prepare source carriers for the existing private mission. Their arithmetic parents '
    'and the existing abc root graph remain separate. Packet presentation retains the original arbitrary '
    'index type, commutative rings, topologies and designated subsets.\n\n'
    'Every copied source retains its copyright and Apache-2.0 notice, original path and commit. '
    'Original repository commit: `07cb1da58f6d428a670dbb5dd6093d428bcbcdd8`. '
    'Per-file byte identity, license, namespace wrapping and compiler evidence accompany this ledger.\n')
print(json.dumps({'requiredDeclarations': 83, 'sourceCommands': 26, 'bundles': 5}))
