"""Generate local draft payloads. This file has no network or compiler operations."""
from pathlib import Path
import hashlib
import json
import re
import subprocess

HERE = Path(__file__).resolve().parent
CANDIDATE = Path('/tmp/p2m-northcott-next-20261114')
ROOT = Path('/home/admin-wsl/Coq/abc')
WORKSPACE = ROOT / 'prove2me_workspace'
UNIT = 'northcott-sourceproof-20261114'
UNIT_REL = '.local/adaptation/' + UNIT + '/'
ENV = '0df444a360eaa60ab8c11dca51a86af692955474'
ROOT_ID = 'e33ff731-60a7-43ef-87ae-c12aeba23cb5'
PREFIX = 'AbcAdaptation.Tripod.'
NAME_MAP = {
    PREFIX + 'Northcott.norm_embedding_le_mulHeight₁': PREFIX + 'Northcott.norm_embedding_le_mulHeight_one',
    PREFIX + 'Northcott.mulHeight₁_gen_le': PREFIX + 'Northcott.mulHeight_one_gen_le',
}
ORIGINAL_NAMES = {new: old for old, new in NAME_MAP.items()}
HELPERS = [PREFIX + 'Northcott.' + n for n in
           ['norm_embedding_le_mulHeight_one', 'mulHeight_one_gen_le', 'coeff_minpoly_int_mem_Icc']]
CHILDREN = [PREFIX + 'northcottFiniteRoots', PREFIX + 'northcottPolynomialWitness']
PARENT = PREFIX + 'boundedDegreeFiniteness'
NODES = HELPERS + CHILDREN
MODULES = ['TripodNorthcottInputs', 'TripodNorthcottComposition']
PARENT_ID = 'bfd60e2f-e299-4833-ab7e-03d2b7ccfd94'
TITLES = {
    HELPERS[0]: 'Every complex conjugate is bounded by relative multiplicative height',
    HELPERS[1]: 'Explicit multiplicative-height bound in the actual minimal point field',
    HELPERS[2]: 'All integer-minpoly coefficients bounded by all complex conjugates',
    CHILDREN[0]: 'Finite union of roots of the bounded integer polynomials',
    CHILDREN[1]: 'Actual tripod point has a bounded denominator and monic polynomial witness',
}


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def save(name, value):
    path = HERE / name
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, ensure_ascii=False, indent=2) + '\n')


def theorem_relative(name):
    return 'Theorems/Thm_' + name.replace('.', '_') + '.lean'


def original_name(name):
    return ORIGINAL_NAMES.get(name, name)


def planned_relative(relative):
    for old, new in NAME_MAP.items():
        relative = relative.replace('Thm_' + old.replace('.', '_'), 'Thm_' + new.replace('.', '_'))
    return relative


def solution_relative(name):
    return UNIT_REL + 'Solution_' + name.removeprefix(PREFIX).replace('.', '_') + '.lean'


def readback_prose(rows):
    return '\n\n'.join('**' + title + '**\n\n' + '\n\n'.join(
        '`' + row['declaration'] + '`\n\n' + row[lang] for row in rows)
        for lang, title in [('en', 'English'), ('zh_Hans', '简体中文'), ('ja', '日本語')])


def source_statement(text, name):
    short = name.split('.')[-1]
    start = text.index('theorem ' + short) if 'theorem ' + short in text else text.index('theorem ' + name)
    stop = text.index(' :=', start)
    return text[start:stop].replace('theorem ' + short, 'theorem ' + name, 1)


def extract_solution(name):
    raise RuntimeError('Root generates solutions from compiler-bound ASCII sources; original candidate proof text stays unchanged.')


def main():
    registry_path = WORKSPACE / '.local/adaptation/platform-node-registry.json'
    registry = json.loads(registry_path.read_text())
    known = {row['name']: row['id'] for row in registry['published_nodes']}
    assert known[PARENT] == PARENT_ID
    matches = {name: known[name] for name in NODES if name in known}
    save('registry-readonly-candidates.json', {
        'registry_path': str(registry_path), 'registry_sha256': sha(registry_path),
        'root': registry['root'], 'parent_name': PARENT, 'parent_id': PARENT_ID,
        'existing_candidate_matches': matches,
        'note': 'Read-only local registry check. Absence here is not a live platform name-availability claim.'})
    assert all(name.isascii() for name in NODES), 'Platform theorem names must use ASCII.'
    save('theorem-name-map.json', {'original_to_platform': NAME_MAP,
        'reason': 'references/upload_full_project.md:87 prohibits Unicode subscripts in theorem_name',
        'proof_and_type_policy': 'Names and module paths change mechanically; proof mathematics and readback prose stay unchanged.'})
    # Existing names are reused. Only missing names become publication candidates.
    publish_names = [name for name in NODES if name not in matches]
    assert all(not re.search(r'^import Theorems\.', (CANDIDATE / ('Definitions/Def_' + mod + '.lean')).read_text(), re.M) for mod in MODULES)
    source_manifest = json.loads((CANDIDATE / 'SOURCE_MANIFEST.json').read_text())
    quote_source = Path('/tmp/p2m-northcott-mochizuki-quotes-20261114/source-quotes.json')
    quotations = json.loads(quote_source.read_text())
    q = next(row for row in quotations['quotes'] if row['id'] == 'N1')
    display_quote = q['exact_quote_latex']
    math_spans = [r'd', r'C\in\mathbb R', r'\mathcal L_{\mathbb Q}', r'X_{\mathbb Q}',
                  r'x\in X(\overline{\mathbb Q})^{\leq d}',
                  r'\mathrm{ht}_{\overline{\mathcal L}}(x)\leq C']
    replacements = []
    for span in math_spans:
        original, rendered = '(' + span + ')', '$' + span.replace(chr(92) * 2, chr(92)) + '$'
        assert display_quote.count(original) == 1, original
        display_quote = display_quote.replace(original, rendered)
        replacements.append({'original': original, 'rendered': rendered})
    reverted = display_quote
    for item in replacements:
        reverted = reverted.replace(item['rendered'], item['original'])
    assert reverted == q['exact_quote_latex']
    quotations['quotation_display_normalization'] = {
        'quote_id': 'N1', 'original_field_retained': 'quotes[id=N1].exact_quote_latex',
        'normalization': 'Render the six parenthesized mathematical spans with KaTeX inline dollar delimiters. Decode doubled LaTeX backslashes in those spans to single backslashes for rendering. Preserve all English words, punctuation outside math delimiters, item labels, hypotheses, and mathematical content.',
        'replacements': replacements, 'rendered_quote_latex': display_quote}
    save('quote-rendering-normalization.json', quotations['quotation_display_normalization'])
    quote = '> ' + display_quote + '\n\n— Shinichi Mochizuki, *Arithmetic Elliptic Curves in General Position*, §1, Proposition 1.4(iv), p. 6.'
    (HERE / 'mochizuki-quotation.md').write_text(quote + '\n')
    blind_path = Path('/tmp/p2m-northcott-blind-20261114/readbacks.json')
    blind = json.loads(blind_path.read_text())
    lean_files = sorted(CANDIDATE.glob('Definitions/*.lean')) + sorted(CANDIDATE.glob('Theorems/*.lean'))
    owners = {}
    for path in lean_files:
        text = path.read_text()
        namespace = re.search(r'^namespace\s+(\S+)', text, re.M)
        namespace = namespace.group(1) if namespace else ''
        for match in re.finditer(r'^(?:noncomputable\s+)?(def|theorem)\s+([^\s({:]+)', text, re.M):
            name = match.group(2)
            full = name if name.startswith(PREFIX) else namespace + '.' + name
            owners[full] = (path, match.start(), match.group(1))
    assert set(owners) == {row['declaration'] for row in blind['declarations']}
    rows = []
    for original in blind['declarations']:
        row = dict(original)
        path, offset, kind = owners[row['declaration']]
        text = path.read_text()
        signature_end = text.index(' :=', offset)
        old_signature = re.sub(r'\s+', ' ', row['signature']).strip()
        raw_signature = text[offset:signature_end]
        short = row['declaration'].split('.')[-1]
        raw_signature = raw_signature.replace(kind + ' ' + short, kind + ' ' + row['declaration'], 1)
        assert re.sub(r'\s+', ' ', raw_signature).strip() == old_signature, row['declaration']
        row['original_declaration'] = row['declaration']
        row['declaration'] = NAME_MAP.get(row['declaration'], row['declaration'])
        row['original_blind_path'] = row['path']
        row['original_blind_source_file_sha256'] = row['source_file_sha256']
        row['original_candidate_path'] = str(path.relative_to(CANDIDATE))
        row['original_candidate_file_sha256'] = sha(path)
        row['path'] = planned_relative(str(path.relative_to(CANDIDATE)))
        row['source_file_sha256'] = None
        row['root_compiler_rebinding_required'] = True
        row['line'] = text[:offset].count('\n') + 1
        row['source_span_original_blind'] = row.pop('source_span')
        row['status'] = 'independent_semantics_reused_ASCII_name_mapping_root_compiler_binding_pending'
        row['source_quotes'] = ['N1']
        row['en_source_quote'] = q['exact_quote_latex']
        row['en_source_quote_ledger_binding'] = {
            'file': 'source-quotes.json', 'quote_id': 'N1',
            'role': 'direct bounded-degree finiteness context; helper formulas are formal implementation details',
            'no_exact_named_metric_identity_claimed': True}
        rows.append(row)
    save('final-readbacks-draft.json', {'declarations': rows, 'input_file_sha256': {}, 'candidate_input_file_sha256': {
        str(path.relative_to(CANDIDATE)): sha(path) for path in lean_files},
        'independent_readback_source': str(blind_path), 'independent_readback_sha256': sha(blind_path),
        'rebind': 'Original candidate signatures match blind signatures. Two platform names map to ASCII. Original signatures and prose remain unchanged. Root must supply final compiler owners, spans, types, and source hashes.'})
    save('source-quotes.json', quotations)
    row_by_name = {row['declaration']: row for row in rows}
    pin = source_manifest['reference_iut']
    common_source = (
        'Shinichi Mochizuki, Arithmetic Elliptic Curves in General Position, §1, Proposition 1.4(iv), p. 6; '
        + quotations['works']['GenEll']['official_url'] + ' . '
        'This quotation states the bounded-degree finiteness context. It does not assert the exact Lean metric or helper formulas. '
        'Exact proof source: local refer/iut/Iut/Tripod/Northcott.lean, SHA256 ' + pin['source_files'][0]['sha256'] + '. '
        'Archive path /home/admin-wsl/Coq/abc/refer/iut/Iut/Tripod/Northcott.lean; root repository HEAD snapshot context ' + subprocess.check_output(['git', '-C', str(ROOT), 'rev-parse', 'HEAD'], text=True).strip() + '. '
        'Iut upstream revision is not independently verified; the historical d9465c citation is not treated as a verified revision pin. '
        'The actual minimal point fields, all complex embeddings, and normalized absolute logarithmic point height are retained. '
        'No h312 assumption or new open mathematical obligation is added. The mathematical root remains unproved.')
    definitions = []
    for module in MODULES:
        relative = 'Definitions/Def_' + module + '.lean'
        selected = [row for row in rows if row['path'] == relative]
        payload = {'definition_name': module, 'definition_title': module + ' — concrete Northcott bounds and composition',
                   'definition': (CANDIDATE / relative).read_text(),
                   'natural_language_statement': quote + '\n\n' + readback_prose(selected),
                   'source': common_source, 'env': ENV, 'private': True,
                   'tags': ['abc-conjecture', 'arithmetic-geometry']}
        save('def-' + module + '-payload.json', payload)
        definitions.append({'name': module, 'payload': 'def-' + module + '-payload.json',
                            'source': relative, 'source_sha256': sha(CANDIDATE / relative)})
    items = []
    for name in NODES:
        relative = theorem_relative(original_name(name))
        text = (CANDIDATE / relative).read_text()
        preamble = 'import Definitions.Def_TripodNorthcottInputs\n'
        if name == HELPERS[2]:
            preamble += 'import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings\n'
        preamble += '\nset_option autoImplicit false\nopen NumberField Polynomial\nopen AbcAdaptation.Tripod\nopen AbcAdaptation.Tripod.Northcott\nopen scoped Classical'
        item = {'theorem_name': name, 'theorem_title': TITLES[name], 'preamble': preamble,
                'formal_statement': source_statement(text, original_name(name)).replace('theorem ' + original_name(name), 'theorem ' + name, 1) + ' := by sorry',
                'natural_language_statement': quote + '\n\n' + readback_prose([row_by_name[name]]),
                'source': common_source,
                'tags': ['abc-conjecture', 'arithmetic-geometry']}
        if name in publish_names:
            items.append(item)
    save('northcott-children-payload.json', {'problems': items, 'env': ENV, 'private': True})
    # Root regenerates the six real solution files from its compiler-bound ASCII sources.
    # Retain earlier drafts as provenance, but never bind them as current delivery inputs.
    legacy = HERE / 'legacy-unicode-solution-drafts'
    legacy.mkdir(exist_ok=True)
    for path in HERE.glob('Solution_*.lean'):
        path.replace(legacy / path.name)
    for path in HERE.glob('verify-*-request-draft.json'):
        if not path.name.isascii():
            path.replace(legacy / path.name)
    solutions = []
    for name in NODES + [PARENT]:
        relative = solution_relative(name)
        allowed = sorted('Theorems.Thm_' + dep.replace('.', '_') for dep in
                         (HELPERS if name == CHILDREN[1] else CHILDREN if name == PARENT else []))
        request = {'theorem_id': known.get(name), 'theorem_name': name, 'proof_type': 'prove',
                   'file': relative, 'source_sha256': None,
                   'root_generated_solution_required': True,
                   'explanation': quote + '\n\n' + readback_prose([row_by_name[name]]) + '\n\n' + common_source}
        save('verify-' + name.removeprefix(PREFIX).replace('.', '_') + '-request-draft.json', request)
        old_draft = legacy / ('Solution_' + original_name(name).removeprefix(PREFIX).replace('.', '_') + '.lean')
        solutions.append({'name': name, 'original_declaration': original_name(name),
                          'source': relative, 'draft_path': None, 'source_sha256': None,
                          'root_generated_solution_required': True,
                          'legacy_candidate_solution': str(old_draft) if old_draft.exists() else None,
                          'legacy_candidate_solution_sha256': sha(old_draft) if old_draft.exists() else None,
                          'theorem_imports': allowed})
    metadata = {'natural_language_statement': quote + '\n\n' + readback_prose([row_by_name[PARENT]]),
                'source': common_source}
    save('parent-metadata-patch-draft.json', metadata)
    save('delivery-plan.json', {
        'unit': UNIT, 'unit_relative': UNIT_REL, 'candidate_source': str(CANDIDATE),
        'root_id': ROOT_ID, 'parent_name': PARENT, 'parent_id': PARENT_ID,
        'mathlib_rev': ENV, 'visibility': 'private', 'definitions': definitions,
        'new_mathematical_nodes': NODES, 'existing_child_matches': matches,
        'theorem_name_map': NAME_MAP,
        'root_compiler_formals_and_source_hashes_required': True,
        'root_generated_solutions_required': True,
        'solutions': solutions,
        'true_dependencies': {CHILDREN[1]: HELPERS, PARENT: CHILDREN},
        'expected_additions': {'mathematical_nodes': len(publish_names), 'named_math_dependencies': 5,
                               'definitions': len(definitions), 'new_open_mathematical_obligations_after_acceptance': 0},
        'sequence': ['publish TripodNorthcottInputs', 'publish TripodNorthcottComposition',
                     'publish or reuse five theorem nodes',
                     'submit parent composer before proving its two children; expect SKETCH_ACCEPTED',
                     'prove three standalone estimates and finite roots',
                     'prove actual-point polynomial witness using the three accepted estimate modules',
                     'observe parent accepted-sketch propagation to Proved; do not repeat a received submission',
                     'patch parent prose/source only after accepted state; preserve exact formal_statement',
                     'read complete root graph/frontier and record actual dependencies and statuses'],
        'schema_status': 'draft; root agent will align final platform request and evidence schemas',
        'not_executed': ['compiler', 'MCP-CI', 'network', 'platform', 'main workspace edits', 'publish']})
    source = ROOT / 'refer/iut/Iut/Tripod/Northcott.lean'
    oid = subprocess.check_output(['git', '-C', str(ROOT), 'hash-object', str(source)], text=True).strip()
    tracked = subprocess.check_output(['git', '-C', str(ROOT), 'ls-files', '--stage', '--', str(source)], text=True).strip()
    save('source-pin-draft.json', {'source': str(source), 'sha256': sha(source), 'git_content_blob_oid': oid,
         'root_head_at_prepare': subprocess.check_output(['git', '-C', str(ROOT), 'rev-parse', 'HEAD'], text=True).strip(),
         'tracked_blob_entry_at_prepare': tracked or None,
         'tracked_blob_required_before_delivery': False,
         'exact_archive_path': str(source),
         'note': 'Exact archive path plus SHA256 pins this input. Root repository HEAD supplies snapshot context only. The content blob OID is not a tracked-input claim. Historical upstream Iut revision is unverified.'})
    save('draft-preparation-audit.json', {
        'passed_static': True, 'candidate_lean_files': len(lean_files), 'definition_files': 2,
        'new_mathematical_nodes': 5, 'solution_specs': 6, 'new_solution_files_generated': 0, 'independent_readback_rows': len(rows),
        'exact_signature_rebind_checks': len(rows), 'no_theorems_in_definitions': True,
        'no_new_open_nodes': True, 'compiler_or_platform_validation': 'not run',
        'registry_matches': matches})
    print('Prepared 2 Definition payloads, 5 ASCII theorem candidates, 6 root-generated solution specifications, and 16 readbacks with original-name/hash provenance.')
    print('No compiler, network, platform call, or main-workspace mutation ran.')


if __name__ == '__main__':
    main()
