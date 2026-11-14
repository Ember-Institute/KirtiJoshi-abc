from pathlib import Path
import hashlib
import json
import re
import shutil

OLD = Path('/tmp/p2m-regular-ramified-obstruction-next-20261114')
OUT = Path('/tmp/p2m-regular-ramified-obstruction-canonical-v2-20261114')
NS = 'AbcAdaptation.Tripod.Fermat.Proper'
CD = NS + '.CurveDeriv'
PARENT = 'noncriticalRegularRamifiedDerivNotMem'
ledger = json.loads((OLD / 'source-consumer.json').read_text())
rows = {r['local_name']: r for r in ledger['source_declarations_and_consumers']}
for dirname in ['Definitions', 'Theorems', 'Solutions', 'reference']:
    (OUT / dirname).mkdir(exist_ok=True)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def module(name):
    return 'Theorems.Thm_' + name.replace('.', '_')


def public_name(name):
    return NS + '.' + name if name == PARENT else CD + '.' + name


nodes = {
    'exists_irreducible_valuation_lt_one': {
        'deps': [], 'private': ['valuation_algebraMap_rat']},
    'valuation_aeval_derivative_eq_one': {'deps': [], 'private': []},
    'exists_pow_succ_mul_derivAlong_not_mem': {
        'deps': ['exists_irreducible_valuation_lt_one', 'valuation_aeval_derivative_eq_one'],
        'private': ['inv_mem_of_valuation_eq_one', 'ne_zero_of_irreducible',
                    'mul_inv_mem_of_valuation_lt_one', 'derivAlong_self']},
    'exists_eq_div': {'deps': [], 'private': ['mem_of_isIntegral', 'isPrincipalIdealRing_adjoin']},
    'exists_pow_mul_derivAlong_mem_integralClosure': {
        'deps': [], 'private': ['ne_zero_of_irreducible', 'exists_pow_mul_mem',
                               'mem_of_isIntegral', 'isPrincipalIdealRing_adjoin']},
    'exists_pow_mul_derivAlong_mem': {
        'deps': ['exists_eq_div', 'exists_pow_mul_derivAlong_mem_integralClosure'],
        'private': ['inv_mem_of_valuation_eq_one', 'valuation_lt_one_of_irreducible',
                    'mem_of_isIntegral']},
    'derivAlong_mem': {'deps': ['exists_pow_succ_mul_derivAlong_not_mem',
                              'exists_pow_mul_derivAlong_mem'], 'private': []},
    'derivAlong_unit_mul_pow': {
        'deps': ['derivAlong_mem'],
        'private': ['valuation_algebraMap_rat', 'valuation_lt_one_of_irreducible', 'derivAlong_self']},
    'derivAlong_eq_unit_mul_pow_of_aeval': {
        'deps': ['derivAlong_unit_mul_pow', 'valuation_aeval_derivative_eq_one'],
        'private': ['valuation_lt_one_of_irreducible']},
    PARENT: {
        'deps': ['derivAlong_eq_unit_mul_pow_of_aeval'],
        'private': ['eq_zero_of_formallyUnramified', 'ext_of_formallyUnramified',
                    'derivAlong_self', 'derivation_ext_of_eq', 'eq_smul_derivAlong',
                    'derivAlong_eq_smul', 'derivAlong_mul_derivAlong',
                    'inv_mem_of_valuation_eq_one', 'ord_uniformizer', 'uniformizer_ne_zero',
                    'transcendental_of_ord_ne_zero', 'isUnit_iff_ord_eq_zero',
                    'irreducible_of_ord_eq_one', 'exists_valuation_aeval_lt_one',
                    'valuation_eq_one_of_ord_eq_zero', 'ord_eq_zero_of_valuation_eq_one']}}

inventory = {
    'status': 'canonical_static_reorganization_plan_not_elaborated',
    'old_candidate': str(OLD), 'new_candidate': str(OUT),
    'old_source_declarations': len(rows),
    'old_public_theorems_in_Theorems': sum(r['file'].startswith('Theorems/') for r in rows.values()),
    'new_public_node_count': len(nodes),
    'new_Definitions': ['Definitions/Def_FermatCurveFieldUniformizer.lean: actual uniformizer definition only'],
    'nodes': [{'theorem_name': public_name(name), 'module': module(public_name(name)),
               'file': module(public_name(name)).replace('.', '/') + '.lean',
               'direct_node_dependencies': [public_name(dep) for dep in info['deps']],
               'inline_private_closure': [rows[p]['namespace'] + '.' + p for p in info['private']]}
              for name, info in nodes.items()],
    'method': 'Existing source statement and proof names stay unchanged. Select declarations from the previous static candidate, keep their namespace/variable/include/notation context, and add private only to proof-side helpers.',
    'limit': 'This is a static source dependency plan. Root must validate elaborated declarations and exact upload text through MCP-CI before publication.'}
for node in inventory['nodes']:
    node['file'] = 'Theorems/Thm_' + node['theorem_name'].replace('.', '_') + '.lean'
    assert re.fullmatch(r'[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*', node['theorem_name'])
(OUT / 'node-inventory.json').write_text(json.dumps(inventory, indent=2, ensure_ascii=False) + '\n')
print(json.dumps({'inventory': str(OUT / 'node-inventory.json'),
                  'old_public_theorems_in_Theorems': inventory['old_public_theorems_in_Theorems'],
                  'new_nodes': len(nodes)}, indent=2))


def declaration_span(text, name):
    match = re.search(r'^(?:theorem|noncomputable def) ' + re.escape(name) + r'\b', text, re.M)
    assert match, name
    end = re.search(r'\n(?=(?:theorem |noncomputable def |variable |include |omit |end |section |open |local notation |set_option |/--|/-!|@\[))', text[match.end():])
    b = match.end() + end.start() if end else len(text)
    a = match.start()
    while a > 0:
        prev_end = a - 1
        prev_start = text.rfind('\n', 0, prev_end) + 1
        previous = text[prev_start:prev_end]
        if previous.startswith(('omit ', '@[')) or (previous.startswith('/--') and previous.endswith('-/')):
            a = prev_start
        else:
            break
    return a, b, match.start()


all_by_file = {}
for name, row in rows.items():
    all_by_file.setdefault(row['file'], []).append(name)

owners = []


def fragment(rel, selected, private_names, owner_module):
    text = (OLD / rel).read_text()
    # Preserve the original command skeleton, including omit/include and local notation scopes.
    start = text.index('set_option autoImplicit false')
    body = text[start:]
    edits = []
    for name in all_by_file[rel]:
        a, b, token = declaration_span(body, name)
        if name not in selected:
            edits.append((a, b, ''))
        elif name in private_names:
            assert body[token:].startswith('theorem ')
            edits.append((token, token, 'private '))
            row = rows[name]
            raw = body[token:b].rstrip() + '\n'
            owners.append({'module': owner_module,
                           'userName': row['namespace'] + '.' + name,
                           'isPrivate_expected': True,
                           'compiler_private_name': 'pending elaboration; bind by (module,userName)',
                           'source_file': row['source_file'], 'source_name': row['source_name'],
                           'source_line_start': row['line_start'], 'source_line_end': row['line_end'],
                           'source_span_sha256': row['source_span_sha256'],
                           'old_candidate_file': rel,
                           'transported_declaration_sha256_without_private': sha(raw.encode()),
                           'attached_wrapper_text': body[a:token],
                           'statement_and_proof_transport': 'identical to old candidate; private modifier only',
                           'context_transport': 'original source namespace/section/variable/include/notation skeleton retained'})
    for a, b, replacement in sorted(edits, reverse=True):
        body = body[:a] + replacement + body[b:]
    return body


external_imports = {
    'exists_irreducible_valuation_lt_one': ['Definitions.Def_FermatCurveDerivationAdjoin'],
    'valuation_aeval_derivative_eq_one': ['Definitions.Def_FermatCurveDerivationAdjoin'],
    'exists_pow_succ_mul_derivAlong_not_mem': [
        'Definitions.Def_FermatCurveDerivationAdjoin', 'Mathlib.RingTheory.DiscreteValuationRing.Basic',
        'Mathlib.Tactic.FieldSimp', 'Mathlib.Tactic.LinearCombination'],
    'exists_eq_div': ['Definitions.Def_FermatCurveDerivationAdjoin',
                      'Mathlib.RingTheory.Valuation.LocalSubring',
                      'Mathlib.RingTheory.DedekindDomain.IntegralClosure',
                      'Mathlib.RingTheory.DedekindDomain.Dvr', 'Mathlib.Tactic.LinearCombination'],
    'exists_pow_mul_derivAlong_mem_integralClosure': [
        'Definitions.Def_FermatCurveDerivationAdjoin', 'Mathlib.RingTheory.DiscreteValuationRing.Basic',
        'Mathlib.RingTheory.Valuation.LocalSubring',
        'Mathlib.RingTheory.DedekindDomain.IntegralClosure', 'Mathlib.Tactic.FieldSimp'],
    'exists_pow_mul_derivAlong_mem': ['Definitions.Def_FermatCurveDerivationAdjoin',
                                    'Mathlib.RingTheory.DiscreteValuationRing.Basic',
                                    'Mathlib.RingTheory.Valuation.LocalSubring'],
    'derivAlong_mem': ['Definitions.Def_FermatCurveDerivationAdjoin'],
    'derivAlong_unit_mul_pow': ['Definitions.Def_FermatCurveDerivationAdjoin',
                               'Mathlib.RingTheory.DiscreteValuationRing.Basic', 'Mathlib.Tactic.Positivity'],
    'derivAlong_eq_unit_mul_pow_of_aeval': ['Definitions.Def_FermatCurveDerivationAdjoin',
                                          'Mathlib.RingTheory.DiscreteValuationRing.Basic'],
    PARENT: ['Definitions.Def_FermatNoncriticalElementarySource',
             'Definitions.Def_FermatCurveFieldUniformizer', 'Mathlib.RingTheory.Unramified.Field']}

header = '''/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors

Complete source proof transport from pinned Belyi
9ce4d3f793d3bc831f2fc7214b7dbad90ea012d8.
Canonical node layout; source statements and proof bodies stay unchanged.
See source-consumer.json and private-owners.json for every source copy.
-/
'''

for name, info in nodes.items():
    mod = module(public_name(name))
    imports = external_imports[name] + [module(public_name(dep)) for dep in info['deps']]
    content = header + ''.join('import ' + imp + '\n' for imp in imports) + '\n'
    # Emit each proof-side closure before its public consumer. Preserve declaration order per source file.
    grouped = {}
    for private in info['private']:
        grouped.setdefault(rows[private]['file'], set()).add(private)
    primary = rows[name]['file']
    for rel, selected in grouped.items():
        if rel == primary:
            continue
        content += '/- Private proof closure from ' + rel + '. -/\n'
        content += fragment(rel, selected, selected, mod) + '\n'
    own_selected = grouped.get(primary, set()) | {name}
    content += '/- Source node and its local private closure. -/\n'
    content += fragment(primary, own_selected, grouped.get(primary, set()), mod)
    path = OUT / (mod.replace('.', '/') + '.lean')
    path.write_text(content)

uniform_rel = 'Definitions/Def_FermatCurveFieldUniformizer.lean'
old_uniform = (OLD / uniform_rel).read_text()
prefix = old_uniform[:old_uniform.index('set_option autoImplicit false')]
(OUT / uniform_rel).write_text(prefix + fragment(uniform_rel, {'uniformizer'}, set(),
                                                'Definitions.Def_FermatCurveFieldUniformizer'))
for path in (OLD / 'reference').glob('*'):
    if path.is_file():
        shutil.copy2(path, OUT / 'reference' / path.name)
shutil.copy2(OLD / 'LICENSE', OUT / 'LICENSE')
(OUT / 'private-owners.json').write_text(json.dumps(owners, indent=2, ensure_ascii=False) + '\n')

# This provides a structural import plan now. Elaborated dependency facts remain root's CI task.
dag = {'nodes': [{'theorem_name': public_name(name), 'module': module(public_name(name)),
                  'file': module(public_name(name)).replace('.', '/') + '.lean',
                  'direct_node_dependencies': [public_name(dep) for dep in info['deps']],
                  'imports': external_imports[name] + [module(public_name(dep)) for dep in info['deps']]}
                 for name, info in nodes.items()],
       'topological_order': [public_name(name) for name in nodes],
       'validation': 'static source-use mapping; no Lean elaboration or compiler invocation'}
(OUT / 'canonical-import-dag.json').write_text(json.dumps(dag, indent=2, ensure_ascii=False) + '\n')
print(json.dumps({'canonical_Lean_nodes_written': len(nodes), 'private_copies': len(owners),
                  'DAG': str(OUT / 'canonical-import-dag.json')}, indent=2))
