from pathlib import Path
import hashlib
import json
import re
import subprocess

OLD = Path('/tmp/p2m-regular-ramified-obstruction-next-20261114')
OUT = Path('/tmp/p2m-regular-ramified-obstruction-canonical-v2-20261114')
WS = Path('/home/admin-wsl/Coq/abc/prove2me_workspace')
MATHLIB = Path('/home/admin-wsl/Coq/mathlib4-0df444a')
NS = 'AbcAdaptation.Tripod.Fermat.Proper'
inventory = json.loads((OUT / 'node-inventory.json').read_text())
old_ledger = json.loads((OLD / 'source-consumer.json').read_text())
old_rows = {row['local_name']: row for row in old_ledger['source_declarations_and_consumers']}
owners = json.loads((OUT / 'private-owners.json').read_text())


def sha(data):
    return hashlib.sha256(data).hexdigest()


def decl(text, name):
    match = re.search(r'^(private )?(theorem|noncomputable def) ' + re.escape(name) + r'\b', text, re.M)
    assert match, name
    end = re.search(r'\n(?=(?:private theorem |theorem |noncomputable def |variable |include |omit |end |section |open |local notation |set_option |/--|/-!|@\[))', text[match.end():])
    b = match.end() + end.start() if end else len(text)
    return text[match.start():b].rstrip() + '\n'


def unprivate(text):
    return re.sub(r'^private theorem ', 'theorem ', text, count=1)


for line in (OLD / 'SHA256SUMS').read_text().splitlines():
    digest, rel = line.split('  ', 1)
    assert sha((OLD / rel).read_bytes()) == digest, ('old_candidate_changed', rel)

public_checks = []
new_rows = []
decls_by_module = {}
for node in inventory['nodes']:
    name = node['theorem_name'].split('.')[-1]
    assert re.fullmatch(r'[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*', node['theorem_name'])
    assert node['file'] == 'Theorems/Thm_' + node['theorem_name'].replace('.', '_') + '.lean'
    path = OUT / node['file']
    text = path.read_text()
    public_names = re.findall(r'^theorem (\S+)', text, re.M)
    assert public_names == [name], (node['file'], public_names)
    actual = decl(text, name)
    row = old_rows[name]
    expected = decl((OLD / row['file']).read_text(), name)
    assert actual == expected, ('public_declaration_changed', name)
    own = {n: decl(text, n) for n in re.findall(r'^(?:private )?theorem (\S+)', text, re.M)}
    decls_by_module[node['module']] = own
    for dep in node['direct_node_dependencies']:
        dep_name = dep.split('.')[-1]
        assert re.search(r'(?<![A-Za-z0-9_])' + re.escape(dep_name) + r'(?![A-Za-z0-9_])', actual), (name, dep)
    public_checks.append({'module': node['module'], 'userName': node['theorem_name'],
                          'one_public_theorem': True, 'canonical_filename': True,
                          'conservative_ASCII_name': True,
                          'statement_and_proof_byte_exact_to_old_candidate': True,
                          'declaration_sha256': sha(actual.encode()),
                          'direct_node_dependencies': node['direct_node_dependencies']})
    new_rows.append({**row, 'module': node['module'], 'userName': node['theorem_name'],
                     'file': node['file'], 'isPrivate_expected': False,
                     'declaration_sha256': sha(actual.encode()),
                     'status': 'source_statement_and_proof_byte_exact_to_old_candidate'})

private_checks = []
owner_keys = set()
for owner in owners:
    key = (owner['module'], owner['userName'])
    assert key not in owner_keys, key
    owner_keys.add(key)
    name = owner['userName'].split('.')[-1]
    own = decls_by_module[owner['module']]
    actual = own[name]
    assert actual.startswith('private theorem ')
    expected = decl((OLD / owner['old_candidate_file']).read_text(), name)
    assert unprivate(actual) == expected, key
    assert sha(expected.encode()) == owner['transported_declaration_sha256_without_private']
    # Verify actual same-module uses in declaration bodies, not file labels or documentation.
    consumers = []
    for consumer_name, consumer_decl in own.items():
        if consumer_name == name:
            continue
        if re.search(r'(?<![A-Za-z0-9_])' + re.escape(name) + r'(?![A-Za-z0-9_])', consumer_decl):
            consumers.append(consumer_name)
    assert consumers, ('unused_private_copy', key)
    old_text = (OLD / owner['old_candidate_file']).read_text()
    new_file = OUT / (owner['module'].replace('.', '/') + '.lean')
    new_text = new_file.read_text()
    context_commands = [line for line in old_text.splitlines()
                        if line.startswith(('variable ', 'include ', 'omit ', 'local notation ',
                                            'set_option quotPrecheck', 'section ', 'namespace '))]
    for command in context_commands:
        # Omit wrappers belong only to their own selected declarations.
        if command.startswith('omit '):
            continue
        assert command in new_text, ('context_command_missing', key, command)
    assert owner['attached_wrapper_text'] + 'private theorem ' + name in new_text
    private_checks.append({**owner, 'actual_same_module_consumers': consumers,
                           'statement_and_proof_byte_exact_except_private_modifier': True,
                           'context_commands_retained': context_commands})
    row = old_rows[name]
    new_rows.append({**row, 'module': owner['module'], 'userName': owner['userName'],
                     'file': str(new_file.relative_to(OUT)), 'isPrivate_expected': True,
                     'actual_same_module_consumers': consumers,
                     'declaration_sha256_without_private': sha(unprivate(actual).encode()),
                     'status': 'source_statement_and_proof_byte_exact_except_private_modifier'})

uniform_file = 'Definitions/Def_FermatCurveFieldUniformizer.lean'
uniform = (OUT / uniform_file).read_text()
assert re.findall(r'^(?:private )?theorem ', uniform, re.M) == []
assert decl(uniform, 'uniformizer') == decl((OLD / uniform_file).read_text(), 'uniformizer')
assert not re.search(r'^import Theorems\.', uniform, re.M)
new_rows.append({**old_rows['uniformizer'], 'file': uniform_file,
                 'module': uniform_file.removesuffix('.lean').replace('/', '.'),
                 'userName': NS + '.Place.uniformizer', 'isPrivate_expected': False,
                 'status': 'actual_source_def_byte_exact_to_old_candidate'})
assert {row['local_name'] for row in new_rows} == set(old_rows)
assert len(new_rows) == 45

target_name = 'noncriticalRegularRamifiedDerivNotMem'
target_file = next(node['file'] for node in inventory['nodes'] if node['theorem_name'].endswith('.' + target_name))
def target(text):
    a = text.index('theorem ' + target_name)
    return text[a:text.index(':= by', a)]
assert target((OUT / target_file).read_text()) == target((OLD / target_file).read_text())
assert target((OUT / target_file).read_text()) == target((WS / target_file).read_text())

graph = {node['theorem_name']: node['direct_node_dependencies'] for node in inventory['nodes']}
reached = set()
def visit(node):
    if node in reached:
        return
    reached.add(node)
    for dep in graph[node]:
        visit(dep)
visit(NS + '.' + target_name)
assert reached == set(graph)
position = {name: i for i, name in enumerate(graph)}
assert all(position[dep] < position[name] for name, deps in graph.items() for dep in deps)

closure = {}
pending = [uniform_file] + [node['file'] for node in inventory['nodes']]
while pending:
    rel = pending.pop()
    if rel in closure:
        continue
    path = OUT / rel if (OUT / rel).is_file() else WS / rel
    text = path.read_text()
    imports = re.findall(r'^import (\S+)', text, re.M)
    assert not any(re.search(r'(^|\.)(Act2|Scene2|Prologue|Obligations)(\.|$)', name) for name in imports)
    assert not any(name == 'Mathlib' or name.startswith('Belyi.') for name in imports)
    if rel.startswith('Definitions/'):
        assert not any(name.startswith('Theorems.') for name in imports), rel
    for imp in imports:
        if imp.startswith('Mathlib.'):
            assert (MATHLIB / (imp.replace('.', '/') + '.lean')).is_file(), imp
        elif imp.startswith(('Definitions.', 'Theorems.')):
            pending.append(imp.replace('.', '/') + '.lean')
        else:
            raise AssertionError(imp)
    closure[rel] = {'sha256': sha(path.read_bytes()), 'imports': imports,
                    'source': 'canonical_v2' if path.is_relative_to(OUT) else 'existing_workspace'}

checks = 'import ' + next(node['module'] for node in inventory['nodes'] if node['theorem_name'].endswith('.' + target_name)) + '\n\n'
for node in inventory['nodes']:
    checks += '#print axioms ' + node['theorem_name'] + '\n'
(OUT / 'Solutions/Checks_FermatRegularRamifiedObstructionCanonical.lean').write_text(checks)

whitespace_checks = []
for path in [*OUT.glob('Definitions/*.lean'), *OUT.glob('Theorems/*.lean'), *OUT.glob('Solutions/*.lean')]:
    text = path.read_text()
    assert not re.search(r'\b(sorry|admit|axiom|unsafe)\b', text), path
    assert 'maxHeartbeats' not in text
    assert text.endswith('\n')
    r = subprocess.run(['git', 'diff', '--no-index', '--check', '/dev/null', str(path)],
                       text=True, capture_output=True)
    assert r.returncode in (0, 1) and not r.stdout and not r.stderr, path
    whitespace_checks.append({'file': str(path.relative_to(OUT)), 'no_whitespace_diagnostics': True})

report = {
    'status': 'canonical_static_source_checks_passed_uncompiled_draft',
    'old_candidate_preserved_and_all_old_hashes_match': True,
    'old_inventory': {'declarations': 34, 'actual_defs': 1, 'theorems': 33,
                       'Definitions_declarations': 15, 'Theorems_declarations': 19},
    'new_inventory': {'public_nodes': 10, 'private_copies': 34, 'unique_private_sources': 23,
                       'actual_defs': 1, 'total_emitted_declarations': 45,
                       'unique_source_declarations': 34},
    'public_nodes': public_checks,
    'private_copies': private_checks,
    'node_DAG_is_acyclic_and_all_nodes_reached_by_original_target': True,
    'Definitions_only_actual_uniformizer_def_and_no_Theorems_import': True,
    'original_target_byte_exact_to_old_candidate_and_workspace': True,
    'original_target_sha256': sha(target((OUT / target_file).read_text()).encode()),
    'source_pin': old_ledger['reference_pin'], 'source_hashes': old_ledger['reference_hashes'],
    'source_construction_alignment': old_ledger['derivAlong_alignment'],
    'project_import_closure': closure,
    'whitespace_checks': whitespace_checks,
    'no_new_Open_node_or_axiom': True,
    'compiler_run': False, 'MCP_CI_run': False, 'platform_API_run': False,
    'main_workspace_edits': False, 'cache_edits': False,
    'validation_limit': 'Static source checks only. Expected compiler owners use (module,userName); private compiler names and elaborated types require root MCP-CI facts.'}
(OUT / 'static-review.json').write_text(json.dumps(report, indent=2, ensure_ascii=False) + '\n')
(OUT / 'private-owners.json').write_text(json.dumps(private_checks, indent=2, ensure_ascii=False) + '\n')
(OUT / 'blind-source-bindings.json').write_text(json.dumps({
    'source_semantic_rows': 34, 'emitted_instances': 45,
    'binding_key': ['module', 'userName'],
    'compiler_name_status': 'private internal indices remain pending root elaboration',
    'rows': [{'module': row['module'], 'userName': row['userName'],
              'isPrivate_expected': row['isPrivate_expected'],
              'source_file': row['source_file'], 'source_name': row['source_name'],
              'source_span_sha256': row['source_span_sha256'],
              'old_source_candidate_file': old_rows[row['local_name']]['file'],
              'new_candidate_file': row['file']}
             for row in new_rows]}, indent=2, ensure_ascii=False) + '\n')
new_ledger = {**old_ledger,
              'status': 'canonical_v2_uncompiled_source_proof_draft',
              'old_candidate': str(OLD),
              'canonical_rules': {'reference': str(WS / 'references/upload_full_project.md'),
                                  'relevant_lines': [39, 40, 46, 85, 87],
                                  'one_public_node_per_Thm_file': True,
                                  'filename_slug_matches_full_theorem_name': True,
                                  'conservative_ASCII_node_names': True},
              'source_declarations_and_consumers': new_rows,
              'source_copy_identity': '(module,userName), not userName alone',
              'canonical_import_DAG': 'canonical-import-dag.json',
              'private_owner_inventory': 'private-owners.json',
              'blind_source_instance_bindings': 'blind-source-bindings.json',
              'inline_private_count': 34, 'public_node_count': 10,
              'Definitions': 'Only actual uniformizer def; structural theorem helpers moved to real private proof closures.',
              'files': {str(path.relative_to(OUT)): {'sha256': sha(path.read_bytes()), 'lines': len(path.read_text().splitlines())}
                        for path in [*OUT.glob('Definitions/*.lean'), *OUT.glob('Theorems/*.lean')]},
              'static_review': 'static-review.json'}
(OUT / 'source-consumer.json').write_text(json.dumps(new_ledger, indent=2, ensure_ascii=False) + '\n')
print(json.dumps({'status': report['status'], 'public_nodes': 10, 'private_copies': 34,
                  'unique_source_declarations': 34, 'original_target_byte_exact': True,
                  'old_candidate_preserved': True}, indent=2))
