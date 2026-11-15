"""Record the exact source consumers and the prior/new carrier boundary."""
from pathlib import Path
import hashlib, json, shutil

B = Path(__file__).resolve().parent
load = lambda p: json.loads(p.read_text())
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
inventory = load(B / 'inventory.json')
dependencies = load(B / 'dependency-closure.json')
wrappers = {e['module']: e for e in load(B / 'generated-wrapped/foundation-wrapper-report.json')['bundles']}
entries = []
for module in inventory['modules']:
    wrapper = wrappers[module['module']]
    provenance = module['provenance']
    selected = [d for d in module['declarations'] if d['selectedForBundle']]
    roots = [d for d in module['declarations'] if d['name'] in module['selectedSourceCommandCandidates']]
    first, last = min(d['startLine'] for d in roots), max(d['endLine'] for d in roots)
    source_url = (provenance['originalRepository'] + '/blob/' + provenance['originalCommit'] +
        '/' + provenance['originalSourcePath'] + '#L' + str(first) + '-L' + str(last))
    row = {'producer': wrapper['definitionName'], 'kind': 'definition-bundle',
        'stage': 'reference signature and definition-body carrier preparation',
        'owner': 'reference adaptation; actual producer existence obligations keep their original stage',
        'originalModule': module['module'], 'sourceURL': source_url,
        'sourceProvenance': provenance, 'wrappedSourceSha256': wrapper['sha256'],
        'selectedSourceCommands': module['selectedSourceCommandCandidates'],
        'selectedDeclarations': [{'original': d['name'],
            'wrapped': 'AbcAdaptation.Reference.' + d['name'],
            'kind': d['kind'], 'isInstance': d['isInstance'],
            'sourceCommandOwner': dependencies['sourceCommandOwnerCandidates'].get(d['name']),
            'actualOriginalConsumers': d['actualConsumers'],
            'originalConsumerPathToMainTheorem': d['consumerPathToMainTheorem']}
            for d in selected],
        'actualSourceConsumer': 'Iut.Theorem110Invariants.theorem110',
        'consumerEvidence': {'graphJobId': 'ci-012771-ee109b3e',
            'graphSha256': inventory['graphSha256'], 'inventorySha256': sha(B / 'inventory.json')},
        'sourceCommandsPreserved': True, 'definitionBodyProofsPreserved': True,
        'rootGraphMembership': False, 'canonicalC22Connected': False}
    if module['module'].endswith('Container'):
        row['actualScope'] = 'Local presentations, finite fibers and families of regions with finitely many differences from designated integral regions. The original global Container and toSet definitions are not selected. No actual field tensor decomposition is constructed.'
    elif module['module'].endswith('HolomorphicHull'):
        row['actualScope'] = 'A supplied admissible class, a class of unit-scaled regions and a supplied least-region operation; the three retained elementary source proofs are conditional on this record. No existence or holomorphic identity is proved.'
    elif module['module'].endswith('GlobalField'):
        row['actualScope'] = 'Explicit number-field, model-change reduction, j-generated subfield, torsion and bad-place conditions. The ambient Fbar is an arbitrary Field/Algebra here, not assumed algebraically closed.'
        row['sourceEmissionDependency'] = {'owner': 'Iut.solvableClosure',
            'sharedGeneratedConstant': 'Iut.solvableClosure._proof_1',
            'actualConsumer': 'Iut.IsGaloisOfDegreePrimeTo',
            'wholeOwnerResultHasTheoremPath': False,
            'policy': 'Retain the original earlier command to regenerate its shared proof helper; do not invent a separate consumer of the compositum value.'}
    elif module['module'].endswith('PlacesOver'):
        row['actualScope'] = 'Automorphism action on finite places, compatibility with a specified tower map and the original supporting algebraic instance/proofs. No decomposition-group declarations are selected.'
    else:
        row['actualScope'] = 'A unit q of a normed field with norm less than one, plus the existing proof of positive norm. The order, uniformization and a complete/nonarchimedean hypothesis are not supplied by this bundle.'
    entries.append(row)
result = {'schema': 'reference-packet-field-source-ledger-v3', 'entries': entries,
    'sourceCommandCount': sum(len(e['selectedSourceCommands']) for e in entries),
    'selectedDeclarationCount': sum(len(e['selectedDeclarations']) for e in entries),
    'requiredPriorConstants': dependencies['requiredPriorConstants'],
    'priorKernelAuditJob': 'ci-013377-98675e26', 'priorAvailableCount': 110,
    'priorRequiredCount': len(dependencies['requiredPriorConstants']),
    'productionUpstreamDependenciesAdded': False, 'rootGraphMembership': False,
    'paperIdentityAndArithmeticInstantiationCompleted': False}
assert result['sourceCommandCount'] == 32 and result['selectedDeclarationCount'] == 133
(B / 'SOURCE_LEDGER.json').write_text(json.dumps(result, ensure_ascii=False, indent=2) + '\n')
shutil.copy2(B.parents[3] / 'refer/iut/LICENSE', B / 'LICENSE.Apache-2.0')
(B / 'SOURCE_LEDGER.md').write_text(
    '# Packet and global-field carrier sources\n\n'
    'The five bundles retain 32 complete source commands and 133 required compiler declarations. '
    'They use 32 constants from the prior 110 audited declarations. Exact consumers and source paths '
    'are in `SOURCE_LEDGER.json`. The original `solvableClosure` command is retained to regenerate '
    'a shared proof used by `IsGaloisOfDegreePrimeTo`; its compositum result has no invented path to the main theorem.\n\n'
    'Four modules come from iut commit `07cb1da58f6d428a670dbb5dd6093d428bcbcdd8`. '
    'The Tate parameter module comes from tate-curves-theta commit '
    '`ca6c2279d3cea0690cdb01328e727118d5485d68`. Its exact source declares Apache 2.0; '
    'that upstream tree has no separate license file. The source notice is retained and the standard '
    'Apache 2.0 text is supplied in `LICENSE.Apache-2.0`. Git-blob and manifest evidence is retained.\n\n'
    'These private source-preparation bundles remain separate from the abc root graph. '
    'Actual arithmetic construction, paper-object identity and the Joshi bridge remain separate obligations.\n')
print(json.dumps({'bundles': 5, 'sourceCommands': 32, 'selected': 133, 'priorRequired': 32}))
