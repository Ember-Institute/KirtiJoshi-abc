"""Select Tate proof declarations from the archived compiler graph."""

from collections import defaultdict
from hashlib import sha256
import json
from pathlib import Path
import re
import sys

repo = Path('/home/admin-wsl/Coq/abc')
workspace = repo / 'prove2me_workspace'
upstream = repo / 'ArithmeticTeichmullerSpaces/.lake/packages/tate-curves-theta'
draft = Path(__file__).parent
archive = workspace / '.local/adaptation/reference-extraction-20261115'
direct = draft.parent
tate_prefix = 'TateCurvesTheta.TateParameter.'
adapted_prefix = 'AbcAdaptation.Reference.' + tate_prefix
shared = 'Definitions.Def_AbcAdaptation_Reference_TateCurvesTheta_TateCurve_PointMap'

equation = "tatePoint_mem'"
addition = 'tatePoint_mul'
surjectivity = 'tatePoint_surjective'
goals = {'tatePoint_equation': equation, addition: addition, surjectivity: surjectivity}
cuts = {
    tate_prefix + equation: '''theorem tatePoint_mem' (h12 : (12 : K) ≠ 0)
    (hu : ∀ n : ℤ, (t.q : K) ^ n * (u : K) ≠ 1) :
    t.tateCurve.toAffine.Equation (t.X u) (t.Y u) := by
  let adapted : _root_.AbcAdaptation.Reference.TateCurvesTheta.TateParameter K :=
    ⟨t.q, t.norm_lt_one⟩
  exact _root_.AbcAdaptation.Reference.TateCurvesTheta.TateParameter.tatePoint_equation
    adapted h12 u hu
''',
    tate_prefix + addition: '''theorem tatePoint_mul (u v : Kˣ) :
    t.tatePoint hmem h12 (u * v) = t.tatePoint hmem h12 u + t.tatePoint hmem h12 v := by
  let adapted : _root_.AbcAdaptation.Reference.TateCurvesTheta.TateParameter K :=
    ⟨t.q, t.norm_lt_one⟩
  exact _root_.AbcAdaptation.Reference.TateCurvesTheta.TateParameter.tatePoint_mul
    adapted hmem h12.2 h12.1 u v
''',
}
wrappers = {
    'tatePoint_equation': '''  intro u hu
  exact _root_.TateCurvesTheta.TateParameter.tatePoint_mem'
    ⟨t.q, t.norm_lt_one⟩ h12 hu
''',
    addition: '''  exact _root_.TateCurvesTheta.TateParameter.tatePoint_mul
    ⟨t.q, t.norm_lt_one⟩ hmem ⟨h2, h12⟩ u v
''',
    surjectivity: '''  exact _root_.TateCurvesTheta.TateParameter.tatePoint_surjective
    ⟨t.q, t.norm_lt_one⟩ hmem ⟨h2, h12⟩
''',
}
platform_cuts = {'tatePoint_equation': equation, addition: addition}

# These rfl rewrites are needed at elaboration, including by plain simp.
# Their applications can disappear from the kernel dependency graph.
source_references = {
    tate_prefix + 'tateCurve_equation_iff': tuple(
        tate_prefix + 'tateCurve_a' + index for index in ('₁', '₂', '₃', '₄', '₆')
    ),
    **{
        tate_prefix + consumer: (tate_prefix + 'factorCoeff_zero',)
        for consumer in ('norm_factorCoeff', 'tsum_factorCoeff_eq', 'norm_tsum_sub_one_le')
    },
    **{
        'TateCurvesTheta.' + consumer: ('TateCurvesTheta.qPoch_zero',)
        for consumer in ('gaussBinom_mul_qPoch', 'qPoch_ne_zero', 'qPoch_eq_prod')
    },
    tate_prefix + 'factorCoeff_mul_qPoch': (
        tate_prefix + 'factorCoeff_zero', 'TateCurvesTheta.qPoch_zero',
    ),
    tate_prefix + 'convBlock_injective': (tate_prefix + 'evalAt_apply',),
    tate_prefix + 'norm_a₄_le': (tate_prefix + 'a₄_def',),
}

def digest(data):
    return sha256(data).hexdigest()

def write_json(path, value):
    path.write_text(json.dumps(value, indent=2, ensure_ascii=False) + '\n')

def theorem_module(name):
    slug = (adapted_prefix + name).replace('.', '_')
    return 'Theorems.Thm_' + slug

def theorem_statements():
    submission = json.loads((draft / 'problem-intent.json').read_text())
    return {row['theorem_name'].removeprefix(adapted_prefix): row['formal_statement']
            for row in submission['problems']}

def selected_dependencies(root, known_cuts, rows):
    pending = [root]
    selected = set()
    used_cuts = set()
    while pending:
        name = pending.pop()
        if name not in rows or name in selected or name in used_cuts:
            continue
        row = rows[name]
        if name in known_cuts:
            used_cuts.add(name)
            fields = ('typeDeps',)
        else:
            assert not row['hasSorryAx'], name
            selected.add(name)
            fields = ('typeDeps', 'valueDeps', 'constructors')
            pending.extend(source_references.get(name, ()))
        for field in fields:
            pending.extend(row[field])
    return selected, used_cuts

def append_declaration_modifiers(lines, first):
    """Retain single-command modifiers attached above a compiler declaration span."""
    cursor = first - 1
    while cursor >= 0:
        line = lines[cursor].strip()
        if not line or line.startswith('--'):
            cursor -= 1
            continue
        if re.match(r'^(omit|include|open|set_option) .+ in$', line):
            first = cursor
            cursor -= 1
            continue
        break
    return first

def upstream_source(module, info, spans, selected, used_cuts):
    path = upstream / (module.replace('.', '/') + '.lean')
    raw = path.read_bytes()
    assert digest(raw) == info['sha256'], path
    text = raw.decode()
    # The compiler graph predates the one-line Quotient patch. Correct the
    # end of the modified declaration before deleting it from the pinned source.
    if module == 'TateCurvesTheta.TateCurve.Quotient':
        spans = dict(spans)
        shifted = spans.pop((79, 85))
        assert shifted == {tate_prefix + 'toAnalyticQuotient_q_mul'}
        assert not shifted & (selected | used_cuts)
        assert len(text.splitlines()) == 90 and all(last < 83 for _, last in spans)
        spans[79, 86] = shifted
    lines = text.splitlines(keepends=True)
    retained = {span for span, names in spans.items() if selected & names}
    for first, last in sorted(spans, reverse=True):
        names = spans[(first, last)]
        if names & used_cuts:
            assert len(names & used_cuts) == 1 and (first, last) not in retained, names
            replacement = cuts[next(iter(names & used_cuts))]
            lines[first:last] = [replacement] + [''] * (last - first - 1)
            continue
        if (first, last) in retained:
            continue
        if any(a <= first and last <= b for a, b in retained):
            continue
        cut_start = append_declaration_modifiers(lines, first)
        # Each removed span occupies its original slot so earlier offsets stay valid.
        lines[cut_start:last] = [''] * (last - cut_start)
    body = ''.join(lines)
    body = re.sub(r'^import [\w.]+\n', '', body, flags=re.M)
    body = body.strip()
    if module == 'TateCurvesTheta.TateCurve.EisensteinSeries':
        body = re.sub(r'\bnorm_qpow_lt_one\b', 'norm_qpow_lt_one_eisenstein', body)
    if module == 'TateCurvesTheta.TateCurve.IntegralModel':
        body = re.sub(r'\bnorm_ofNat_le_one\b', 'norm_ofNat_le_one_integralModel', body)
    if module == 'TateCurvesTheta.Theta.FactorSeries':
        # The archive lists the shared declarations under Weierstrass. Preserve
        # the direct proof's normalization for the other upstream copies.
        start = body.index('/-- **Isosceles-triangle estimate for the denominators.**')
        end = body.index('/-- **The multiplicative form of the coefficient recursion.**', start)
        body = body[:start] + body[end:]
    if any(line == 'noncomputable section' for line in body.splitlines()):
        body += '\n\nend'
    return 'section\n\n' + body + '\n\nend'

def load_graph(modules):
    source_graph = archive / 'c22-decl-graph.jsonl'
    receipt = json.loads((archive / 'c22-graph-source-receipt.json').read_text())
    assert digest(source_graph.read_bytes()) == receipt['graphSha256']
    rows = {}
    with source_graph.open() as stream:
        manifest = json.loads(next(stream))
        for line in stream:
            record = json.loads(line)
            if record.get('module') in modules:
                rows[record['name']] = record
    spans = defaultdict(lambda: defaultdict(set))
    for name, row in rows.items():
        extent = row['range']
        if extent and extent['start']['col'] == 0:
            key = extent['start']['line'] - 1, extent['end']['line']
            spans[row['module']][key].add(name)
    return manifest, receipt, rows, spans

def prepare_solution(name, formal, source_modules, graph_info, rows, spans):
    root = tate_prefix + goals[name]
    known_cuts = set(cuts) if name == surjectivity else set()
    selected, used_cuts = selected_dependencies(root, known_cuts, rows)
    assert used_cuts == known_cuts
    active = {rows[item]['module'] for item in selected | used_cuts if rows[item]['range']}
    source_order = [module for module in source_modules if module in active]
    imports = {shared}
    for module in source_order:
        imports.update(dep for dep in source_modules[module]['imports'] if dep.startswith('Mathlib'))
    if 'Mathlib' in imports:
        imports.remove('Mathlib')
        imports.update({'Mathlib.Algebra.Group.Equiv.TypeTags', 'Mathlib.GroupTheory.QuotientGroup.Basic',
                        'Mathlib.GroupTheory.QuotientGroup.Defs', 'Mathlib.Analysis.SpecialFunctions.Pow.NNReal'})
    for child, native in platform_cuts.items():
        if tate_prefix + native in used_cuts:
            imports.add(theorem_module(child))
    if 'TateCurvesTheta.Theta.FactorSeries' in active:
        # Its statement-identical denominator lemmas resolve to Weierstrass.
        assert 'TateCurvesTheta.TateCurve.Weierstrass' in active
    options = '''set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3'''
    statements = '\n'.join('import ' + module for module in sorted(imports))
    module_bodies = [
        upstream_source(module, source_modules[module], spans[module], selected, used_cuts)
        for module in source_order
    ]
    wrapper = (
        'open AbcAdaptation.Reference.TateCurvesTheta\nopen scoped Classical\n\n'
        + formal.removesuffix('\n  sorry').replace('theorem ' + adapted_prefix + name, 'theorem solution')
        + '\n' + wrappers[name].rstrip()
    )
    output = '\n\n'.join([statements, options, *module_bodies, wrapper]) + '\n'
    path = draft.parent / f'Sol_{name}.lean'
    path.write_text(output)
    write_json(draft / f'{name}-source-manifest.json', {
        **graph_info,
        'theorem': adapted_prefix + name,
        'upstreamDeclaration': root,
        'upstreamSourceRange': rows[root]['range'],
        'solution': str(path.relative_to(draft.parent)),
        'sizeBytes': len(output.encode()),
        'lineCount': len(output.splitlines()),
        'sha256': digest(output.encode()),
        'imports': sorted(imports),
        'declarationClosure': {
            'sizeIncludingGenerated': len(selected),
            'sourceModules': source_order,
            'retainedSourceDeclarations': sorted(item for item in selected if rows[item]['range']),
            'theoremImportsAtCuts': sorted(used_cuts),
            'retainedSyntacticReferences': {
                consumer: providers for consumer, providers in source_references.items() if consumer in selected
            },
        },
        'sourceModuleHashes': {module: source_modules[module]['sha256'] for module in source_order},
    })
    print(path.name, len(output.encode()), len(output.splitlines()), len(source_order),
          len(imports), digest(output.encode()))

def main():
    source_manifest = json.loads((direct / 'direct-source-manifest.json').read_text())
    modules = source_manifest['sourceModules']
    graph, receipt, rows, spans = load_graph(modules)
    graph_info = {
        'leanToolchain': source_manifest['leanToolchain'],
        'mathlibRevision': source_manifest['mathlibRevision'],
        'tateRevision': source_manifest['tateRevision'],
        'graphSha256': receipt['graphSha256'],
        'graphJobId': receipt['jobId'],
        'graphCompiler': graph['compilerVersion'],
    }
    statements = theorem_statements()
    for name in sys.argv[1:] or goals:
        prepare_solution(name, statements[name], modules, graph_info, rows, spans)

if __name__ == '__main__':
    main()
