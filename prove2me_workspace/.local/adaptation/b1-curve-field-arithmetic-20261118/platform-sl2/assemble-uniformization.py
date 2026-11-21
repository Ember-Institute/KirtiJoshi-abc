"""Package the pinned Tate sources and the fixed adapted quotient bridge."""
from collections import Counter
from hashlib import sha256
import json
from pathlib import Path
import re

repo = Path('/home/admin-wsl/Coq/abc')
workspace = repo / 'prove2me_workspace'
upstream = repo / 'ArithmeticTeichmullerSpaces/.lake/packages/tate-curves-theta'
draft = Path(__file__).parent
foundations = workspace / '.local/adaptation/reference-extraction-20261115'
source_receipt = json.loads((foundations / 'c22-graph-source-receipt.json').read_text())
target = 'AbcAdaptation.Reference.Iut.exists_tateUniformization'
root_module = 'TateCurvesTheta.TateCurve.TateUniformization'

def digest(data):
    return sha256(data).hexdigest()

def write_json(path, data):
    path.write_text(json.dumps(data, ensure_ascii=False, indent=2) + '\n')

def module_path(name):
    return Path(name.replace('.', '/') + '.lean')

def source_imports(source):
    return [match[1] for match in re.finditer(r'^import ([\w.]+)$', source, re.M)]

def without_imports(source):
    return re.sub(r'^import [\w.]+\n', '', source, flags=re.M).strip()

def read_modules(module):
    if module in modules:
        return
    path = upstream / module_path(module)
    source = path.read_text()
    dependencies = source_imports(source)
    for name in dependencies:
        if name.startswith('TateCurvesTheta.'):
            read_modules(name)
        else:
            assert name == 'Mathlib' or name.startswith('Mathlib.'), name
            imports.add(name)
    assert digest(source.encode()) == source_receipt['sourceFiles'][module]['rawSha256'] or (
        module == 'TateCurvesTheta.TateCurve.Quotient'
        and digest(source.encode()) == '5a143e7078acb21b78317d3e47e37a37169e2be4b09d37eaea7cfe80085e5290'
    ), module
    modules[module] = source

# The two FactorSeries lemmas duplicate the Weierstrass declarations.
# Retain the Weierstrass proofs and let the original references resolve to them.
duplicate_module = 'TateCurvesTheta.Theta.FactorSeries'
duplicate_start_line = 78
duplicate_end_line = 98
duplicate_names = ('norm_one_sub_qpow', 'one_sub_qpow_ne_zero')

def source_body(module, source):
    if module == duplicate_module:
        source_lines = source.splitlines(keepends=True)
        removed = source_lines[duplicate_start_line - 1:duplicate_end_line]
        assert removed[0].startswith('/-- **Isosceles-triangle estimate')
        assert removed[-1] == '\n'
        assert all(any(line.startswith(f'lemma {name} ') for line in removed)
                   for name in duplicate_names)
        source = ''.join(source_lines[:duplicate_start_line - 1] + source_lines[duplicate_end_line:])
    # The two source-local names occur in distinct modules upstream.
    if module == 'TateCurvesTheta.TateCurve.EisensteinSeries':
        source = re.sub(r'\bnorm_qpow_lt_one\b', 'norm_qpow_lt_one_eisenstein', source)
    if module == 'TateCurvesTheta.TateCurve.IntegralModel':
        source = re.sub(r'\bnorm_ofNat_le_one\b', 'norm_ofNat_le_one_integralModel', source)
    body = without_imports(source)
    # Each original file has an independent option and open-declaration scope.
    unclosed = sum(line == 'noncomputable section' for line in body.splitlines())
    assert unclosed <= 1, module
    if unclosed:
        body += '\n\nend'
    return 'section\n\n' + body + '\n\nend'

imports = set()
modules = {}
read_modules(root_module)

# The upstream TateDatum file is elementary quotient algebra. These imports
# supply its group, zpow, norm, and infinitude lemmas.
imports.remove('Mathlib')
imports.update({
    'Mathlib.Algebra.Group.Equiv.TypeTags',
    'Mathlib.Analysis.SpecialFunctions.Pow.NNReal',
    'Mathlib.GroupTheory.QuotientGroup.Basic',
    'Mathlib.GroupTheory.QuotientGroup.Defs',
    'Definitions.Def_AbcAdaptation_Reference_Iut_Cor312_ThetaData_TateStructure',
    'Definitions.Def_AbcAdaptation_Reference_TateCurvesTheta_TateCurve_Discriminant',
})

proof_parts = {
    # Retain exactly the coordinate projections used by the fixed class bridge.
    'Source_ReferenceIutVariableChangePoint': None,
    'Source_ReferenceIutTateUniformization': None,
    'Source_ReferenceIutTatePointEquation': None,
    'Source_ReferenceIutTateUniformizationLaws': None,
}
bridge_sources = {}
for name in proof_parts:
    path = workspace / 'Solutions' / (name + '.lean')
    proof_parts[name] = without_imports(path.read_text())
    bridge_sources[name] = digest(path.read_bytes())
coords = proof_parts['Source_ReferenceIutVariableChangePoint']
coords = coords[coords.index('/-- The `x`-coordinate of a point'):coords.index('/-- Transport of points along')]
proof_parts['Source_ReferenceIutVariableChangePoint'] = '''namespace AbcAdaptation.Reference.Iut.Anabelian

open WeierstrassCurve

variable {k : Type*} [Field k]

''' + coords.strip() + '''

end AbcAdaptation.Reference.Iut.Anabelian'''
uniformization = proof_parts['Source_ReferenceIutTateUniformization']
proof_parts['Source_ReferenceIutTateUniformization'] = uniformization + '\n\n'
law = proof_parts['Source_ReferenceIutTateUniformizationLaws']
# The two bridge modules used the same private name in separate files.
proof_parts['Source_ReferenceIutTateUniformizationLaws'] = law.replace(
    'upstreamParameter', 'upstreamUniformizationParameter')

target_file = workspace / 'Theorems' / ('Thm_' + target.replace('.', '_') + '.lean')
native_wrapper = (draft.parent / 'tate-structure-platform-draft/Solutions/Review_exists_tateUniformization_native.lean').read_text()
wrapper = without_imports(native_wrapper).removesuffix('\n\n#print axioms solution')
theorem_header = target_file.read_text().split('theorem ' + target, 1)[1].split(' := by', 1)[0]
assert 'theorem solution' + theorem_header + ' := by' in wrapper

headers = '\n'.join('import ' + module for module in sorted(imports))
options = '''set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3'''
parts = [headers, options]
parts.extend(source_body(module, source) for module, source in modules.items())
parts.extend('section\n\n' + source.strip() + '\n\nend' for source in proof_parts.values())
parts.append(wrapper)
solution = '\n\n'.join(parts) + '\n'
path = draft / 'Sol_exists_tateUniformization.lean'
path.write_text(solution)

write_json(draft / 'direct-source-manifest.json', {
    'leanToolchain': 'leanprover/lean4:v4.33.1',
    'mathlibRevision': '0df444a360eaa60ab8c11dca51a86af692955474',
    'tateRevision': 'ca6c2279d3cea0690cdb01328e727118d5485d68',
    'target': target,
    'targetId': '6ee6a3cd-649a-4604-a2d8-1400087da2d8',
    'targetSha256': digest(target_file.read_bytes()),
    'solution': path.name,
    'solutionSha256': digest(solution.encode()),
    'bytes': len(solution.encode()),
    'lines': len(solution.splitlines()),
    'imports': sorted(imports),
    'nativeComparisonReceipt': 'ci-025491-39c02226',
    'sourceGraphJob': source_receipt['jobId'],
    'sourceGraphSha256': source_receipt['graphSha256'],
    'sourceModules': {
        module: {'sha256': digest(source.encode()), 'imports': source_imports(source)}
        for module, source in modules.items()
    },
    'bridgeSources': bridge_sources,
    'mergeNormalization': {
        'triggeringJobId': 'ci-025764-36bd174a',
        'originalSolutionSha256': 'ecf9e569b36e49b4b176c7e61da95d71aa3bef0635c07b3eb32182606535755a',
        'retainedModule': 'TateCurvesTheta.TateCurve.Weierstrass',
        'removedModule': duplicate_module,
        'removedLinesInclusive': [duplicate_start_line, duplicate_end_line],
        'sharedDeclarations': ['TateCurvesTheta.TateParameter.' + name for name in duplicate_names],
    },
    'heartbeatOptions': [
        line for line in solution.splitlines() if re.match(r'^set_option maxHeartbeats ', line)
    ],
})
print(path)
print(len(solution.encode()), 'bytes,', len(solution.splitlines()), 'lines,', len(modules), 'Tate sources,', len(imports), 'imports')
print(digest(solution.encode()))
