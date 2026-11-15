#!/usr/bin/env python3
"""Subtract complete commands using accepted Lean parser/compiler facts only.

This program performs no compilation, CI, API, Git, declaration-name scan, or
reference extraction. Its only source edits are an AST-bound import-header
replacement and removal of excluded complete declaration commands. All other
bytes, including all original contexts, module docs, and license, survive.
Original peer and delivered dependency imports retain exact 4.35 type identity.
"""
import argparse
import bisect
import hashlib
import json
from pathlib import Path

from carrier_contract import (MODULES, unit_config, dependency_evidence, validate_import_graph,
                              validate_source_imports, project_name)
TASK = Path(__file__).resolve().parent
ALLOWED_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}


def require(ok, message):
    if not ok:
        raise ValueError(message)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def file_hash(path):
    return digest(Path(path).read_bytes())


def load(path):
    return json.loads(Path(path).read_text())


def jsonl(path):
    return [json.loads(line) for line in Path(path).read_text().splitlines() if line.strip()]


def walk(node):
    yield node
    for child in node.get('children', []):
        yield from walk(child)


def span(value):
    require(isinstance(value, dict), 'Absent parser range')
    return value['start']['offset'], value['end']['offset']


class Coordinates:
    def __init__(self, data):
        self.data = data
        self.starts = [0] + [i + 1 for i, char in enumerate(data) if char == 10]

    def position(self, offset):
        require(isinstance(offset, int) and 0 <= offset <= len(self.data), 'Invalid source offset')
        line = bisect.bisect_right(self.starts, offset) - 1
        col = len(self.data[self.starts[line]:offset].decode('utf-8'))
        return {'line': line + 1, 'col': col, 'offset': offset}

    def range(self, start, end):
        require(start <= end, 'Inverted source range')
        return {'start': self.position(start), 'end': self.position(end)}

    def verify(self, value):
        a, b = span(value)
        require(value == self.range(a, b), 'Parser offset/line/column mismatch')
        return a, b


def accept_ci(args, acceptance):
    require(acceptance['schema'] == 'foundation-parser-acceptance-v1', 'Unsupported acceptance schema')
    require(acceptance['status'] == 'accepted' and acceptance['noPanicOrErrorDiagnostics'] is True,
            'Parser acceptance not successful')
    require(file_hash(args.parser_ci_result) == acceptance['compilerReceiptSha256'], 'CI receipt hash mismatch')
    ci = load(args.parser_ci_result)
    result = ci['result']
    require(ci['job_id'] == acceptance['job_id'] and ci['status'] == 'succeeded'
            and result['exit_code'] == 0, 'Parser CI not accepted terminal success')
    require(all(d.get('severity') == 'warning' for d in result.get('diagnostics', [])), 'Compiler diagnostics contain errors')
    text = (result.get('stdout', '') + '\n' + result.get('stderr', '')).casefold()
    require('panic' not in text and 'error:' not in text, 'Compiler output contains panic/error')
    snap = result['snapshot']
    require(snap['workspace_mode'] == 'exclusive_worktree' and snap['snapshot_id'] is None,
            'Parser CI did not use exclusive workspace')
    resources = ci['resources']
    require(resources.get('peak_rss_bytes') is not None and resources['peak_rss_bytes'] <= 16 * 1024**3,
            'Parser physical peak RSS unknown or exceeds 16 GiB')
    request = ci['request']
    require(request['language'] == 'lean' and request['task_type'] == 'leaf' and request['target'] == 'file',
            'Unexpected parser CI request')
    query = Path(args.parser_query).resolve()
    source = Path(request['parameters']['source'])
    if not source.is_absolute():
        source = Path(request['workspace']) / source
    require(source.resolve() == query, 'CI source is not authenticated parser query')
    actual = result['actual_arguments']
    require(len(actual) == 2 and Path(actual[0]).name == 'lean' and actual[1] == request['parameters']['source'],
            'Unexpected compiler actual arguments')
    require(Path(request['environment']['FOUNDATION_PARSER_CONFIG']).resolve() == Path(args.parser_config).resolve(),
            'CI parser config path mismatch')
    return ci


def assemble(data, edits, original_source):
    """Copy retained ranges once, record each copied byte's original coordinate."""
    result = bytearray()
    provenance = []
    original = Coordinates(data)
    previous = 0
    for a, b, replacement, reason in sorted(edits, key=lambda item: (item[0], item[1])):
        require(previous <= a <= b <= len(data), 'Overlapping/outside AST edits')
        if previous < a:
            start = len(result)
            result.extend(data[previous:a])
            provenance.append({'kind': 'copied', 'outputStart': start, 'outputEnd': len(result),
                               'originalSource': original_source, 'originalRange': original.range(previous, a),
                               'sha256': digest(data[previous:a])})
        if replacement:
            start = len(result)
            result.extend(replacement)
            provenance.append({'kind': 'generated-import-header', 'outputStart': start,
                               'outputEnd': len(result), 'replacementForOriginalRange': original.range(a, b),
                               'sha256': digest(replacement), 'reason': reason})
        previous = b
    if previous < len(data):
        start = len(result)
        result.extend(data[previous:])
        provenance.append({'kind': 'copied', 'outputStart': start, 'outputEnd': len(result),
                           'originalSource': original_source, 'originalRange': original.range(previous, len(data)),
                           'sha256': digest(data[previous:])})
    output = bytes(result)
    coords = Coordinates(output)
    for piece in provenance:
        piece['outputRange'] = coords.range(piece.pop('outputStart'), piece.pop('outputEnd'))
        x, y = span(piece['outputRange'])
        require(digest(output[x:y]) == piece['sha256'], 'Provenance output hash mismatch')
        if piece['kind'] == 'copied':
            a, b = span(piece['originalRange'])
            require(output[x:y] == data[a:b], 'Provenance copied bytes changed')
    return output, provenance


def remap_range(value, provenance):
    a, b = span(value)
    owners = [p for p in provenance if p['kind'] == 'copied'
              and span(p['originalRange'])[0] <= a <= b <= span(p['originalRange'])[1]]
    require(len(owners) == 1, 'Retained syntax is not fully covered by a unique copied source span')
    owner = owners[0]
    delta = span(owner['outputRange'])[0] - span(owner['originalRange'])[0]
    return a + delta, b + delta


def extract_one(entry, artifact, config, selected_names, args, import_plan):
    module = entry['module']
    require(file_hash(artifact['path']) == artifact['sha256'], 'Parser JSONL hash mismatch: ' + module)
    facts = jsonl(artifact['path'])
    source, = [f for f in facts if f['kind'] == 'source']
    summary, = [f for f in facts if f['kind'] == 'summary']
    require(facts[0] == source and facts[-1] == summary, 'Parser fact stream has invalid framing')
    require(source['schema'] == 'foundation-parser-ranges-v1' and source['module'] == module
            and source['mode'] == 'parser-only-no-reelaboration'
            and source['offsetCoordinate'] == 'lean-normalized-utf8'
            and source['normalization'] == 'String.crlfToLf', 'Parser fact source identity mismatch')
    require(summary['status'] == 'success' and summary['module'] == module
            and summary['mode'] == 'parser-only-no-reelaboration', 'Parser terminal summary mismatch')
    require(source['acceptedGraphSha256'] == config['acceptedGraphSha256'], 'Parser graph binding mismatch')
    require(Path(source['source']).resolve() == Path(entry['source']).resolve(), 'Original source path mismatch')
    raw = Path(source['source']).read_bytes()
    data = Path(source['coordinateSource']).read_bytes()
    require(digest(raw) == entry['sourceSha256'] == source['sourceSha256Expected'], 'Raw source hash mismatch')
    require(data == raw.replace(b'\r\n', b'\n') and len(raw) == source['rawByteLength'], 'Source normalization mismatch')
    require(digest(data) == entry['normalizedSha256'] == source['normalizedSha256Expected']
            == artifact['normalizedSha256'] and len(data) == source['byteLength'], 'Normalized source hash mismatch')
    coords = Coordinates(data)
    for fact in facts:
        for field in ['commandSyntax', 'contextSyntax', 'headerSyntax']:
            if isinstance(fact.get(field), dict):
                for node in walk(fact[field]):
                    if node.get('range') is not None:
                        coords.verify(node['range'])
    commands = [f for f in facts if f['kind'] == 'command']
    declarations = [f for f in facts if f['kind'] == 'compilerDecl']
    parsed_decls = {f['commandIndex']: f for f in facts if f['kind'] == 'decl'}
    require(len(commands) == summary['commandCount'] and [c['commandIndex'] for c in commands] == list(range(len(commands))),
            'Incomplete/reordered command inventory')
    expected = {d['name']: d for d in entry['compilerDeclarations']}
    actual = {d['name']: d for d in declarations}
    require(len(actual) == len(declarations) == len(expected) == summary['compilerDeclarationCount']
            and set(actual) == set(expected), 'Incomplete compiler declaration inventory')
    require({d['name'] for d in declarations if d['selected']} == selected_names, 'Selected declaration set mismatch')
    selected_groups = {}
    no_range = []
    for name, declaration in actual.items():
        expected_decl = expected[name]
        for key in ['selected', 'sourceRootCandidate', 'sourceHelper']:
            require(declaration[key] == expected_decl[key], 'Compiler selection/config mismatch: ' + name)
        require(declaration['declarationKind'] == expected_decl['kind'], 'Compiler kind mismatch: ' + name)
        value = declaration['compilerRange']
        if value is None:
            require(not expected_decl['hasCompilerRange'] and not declaration['containingCommandIndices'], 'Null compiler range mismatch')
            if declaration['selected']:
                no_range.append(name)
            continue
        a, b = coords.verify(value)
        require(expected_decl['hasCompilerRange'] and (a, b) == (expected_decl['expectedStartOffset'], expected_decl['expectedEndOffset']),
                'Compiler offset changed: ' + name)
        owners = [c['commandIndex'] for c in commands if c['range'] is not None
                  and span(c['range'])[0] <= a <= b <= span(c['range'])[1]]
        require(owners == declaration['containingCommandIndices'], 'Compiler/parser owner join mismatch: ' + name)
        if declaration['selected']:
            require(len(owners) == 1, 'Selected declaration lacks unique complete command: ' + name)
            selected_groups.setdefault(owners[0], []).append(name)
        for index in owners:
            require(commands[index]['isDeclaration'], 'Parser misclassified compiler declaration as context: ' + name)
    require(len(selected_groups) == summary['selectedCommandCount'], 'Selected command count mismatch')
    require(sum(d['selected'] and d['compilerRange'] is not None for d in declarations)
            == summary['selectedRangedDeclarationCount'] and len(no_range) == summary['selectedNoRangeDeclarationCount'],
            'Compiler selected summary mismatch')
    ha, hb = coords.verify(source['headerSyntax']['range'])
    source_info = next(s for s in unit_config(args.unit_config)['sources'] if s['module'] == module)
    require(digest(data[:ha]) == source_info['provenance']['sourceHeaderSha256'],
            'Parser-bounded original author/license header differs from provenance')
    imports = import_plan['source435Imports']
    require(imports and len(imports) == len(set(imports)), 'Empty/duplicate reviewed precise imports')
    validate_source_imports(module, imports, args.prior_modules)
    replacement = '\n'.join('import ' + m for m in imports).encode()
    edits = [(ha, hb, replacement, 'Reviewed precise imports; original 4.35 small source')]
    retained = []
    removed = []
    end = hb
    for command in commands:
        if command['range'] is None:
            require(command['syntaxKind'] == 'Lean.Parser.Command.eoi' and not command['selected'], 'Non-EOI command missing range')
            continue
        a, b = coords.verify(command['range'])
        require(end <= a <= b, 'Commands overlap or precede header')
        end = b
        stx = command['commandSyntax']
        require(stx['range'] == command['range'] and stx['syntaxKind'] == command['syntaxKind'], 'Command AST mismatch')
        # Independent AST check of the query's declaration/context classifier.
        ast_decl = any(n['syntaxKind'] in {'Lean.Parser.Command.declaration', 'Lean.Parser.Command.declId'} for n in walk(stx))
        require(ast_decl == command['isDeclaration'], 'Declaration classifier not reproducible from original AST')
        require(command['selected'] == (command['commandIndex'] in selected_groups)
                and set(command['selectedCompilerDeclarations']) == set(selected_groups.get(command['commandIndex'], [])),
                'Command selection does not match compiler ranges')
        if command['isDeclaration']:
            decl = parsed_decls[command['commandIndex']]
            require(decl['range'] == command['range'] and decl['selected'] == command['selected'], 'Declaration AST record mismatch')
        item = {'commandIndex': command['commandIndex'], 'syntaxKind': command['syntaxKind'],
                'originalRange': command['range'], 'sha256': digest(data[a:b]),
                'selectedCompilerDeclarations': command['selectedCompilerDeclarations']}
        if command['isDeclaration'] and not command['selected']:
            removed.append(item)
            edits.append((a, b, b'', 'Excluded whole declaration command'))
        else:
            require(not command['selected'] or command['generationIssue'] is None, 'Unsupported selected atomic group')
            item['role'] = 'selected-declaration' if command['selected'] else 'original-context'
            retained.append(item)
    require(all(c['commandIndex'] in parsed_decls for c in commands if c['isDeclaration']), 'Declaration AST inventory missing command')
    output, provenance = assemble(data, edits, source['source'])
    for piece in provenance:
        piece['offsetCoordinate'] = 'lean-normalized-utf8'
        piece['originalCoordinateSource'] = source['coordinateSource']
    output_coords = Coordinates(output)
    for item in retained:
        a, b = remap_range(item['originalRange'], provenance)
        item['outputRange'] = output_coords.range(a, b)
        require(digest(output[a:b]) == item['sha256'], 'Retained command bytes changed')
    owners = {name: item for item in retained for name in item['selectedCompilerDeclarations']}
    return output, {'module': module, 'originalSource': source['source'],
                    'originalCoordinateSource': source['coordinateSource'],
                    'offsetCoordinate': 'lean-normalized-utf8', 'rawSha256': digest(raw),
                    'normalizedSha256': digest(data), 'parserFacts': artifact,
                    'retainedCommands': retained, 'removedDeclarations': removed,
                    'provenance': provenance, 'noRangeReconstructionObligations': no_range,
                    'selectedCompilerDeclarations': sorted(selected_names), 'source435Imports': imports,
                    'formalAcceptance': {'smallSourceInfoTree': False, 'generatedAuxiliaryIdentity': False,
                                         'allowedAxiomsAndNoSorryAx': False, 'wrappedKernelComparison': False}}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for arg in ['parser-acceptance', 'parser-ci-result', 'parser-config', 'parser-query', 'graph', 'imports', 'reviewed-imports', 'unit-config', 'out']:
        parser.add_argument('--' + arg, required=True)
    args = parser.parse_args()
    out = Path(args.out).resolve()
    require(TASK in out.parents, 'Output must be below assigned unique temporary directory')
    out.mkdir(parents=True, exist_ok=True)
    report = {'schema': 'foundation-small-source-report-v1', 'status': 'inputs-pending', 'modules': [],
              'compilation': 'not-run', 'api': 'not-used', 'git': 'not-used',
              'scope': 'Five next-level original carriers; no mathematical parent obligation completion claim'}
    pending_outputs = []
    try:
        for key, value in vars(args).items():
            if key != 'out':
                require(Path(value).is_file(), 'Required input missing: ' + value)
        unit = unit_config(args.unit_config)
        prior_constants, prior_modules, dependencies = dependency_evidence(unit)
        args.prior_modules = prior_modules
        acceptance = load(args.parser_acceptance)
        ci = accept_ci(args, acceptance)
        for arg, key in [('parser_config', 'configSha256'), ('parser_query', 'querySha256'), ('graph', 'graphSha256')]:
            require(file_hash(getattr(args, arg)) == acceptance[key], 'Acceptance input hash mismatch: ' + arg)
        config = load(args.parser_config)
        require(config['schema'] == 'reference-foundation-parser-config-v1' and config['acceptedGraphSha256'] == file_hash(args.graph),
                'Parser config/graph identity mismatch')
        entries = {e['module']: e for e in config['sources']}
        artifacts = {e['module']: e for e in acceptance['outputs']}
        candidates = {e['module']: e for e in load(args.imports)}
        reviewed = load(args.reviewed_imports)
        require(reviewed['schema'] == 'foundation-precise-import-review-v1' and reviewed['status'] == 'reviewed'
                and reviewed['importsCandidateSha256'] == file_hash(args.imports), 'Precise import plan not reviewed/bound')
        plans = {e['module']: e for e in reviewed['modules']}
        validate_import_graph(plans, prior_modules)
        require(set(entries) == set(artifacts) == set(candidates) == set(plans) == set(MODULES), 'Unexpected five-module set')
        rows = {r['name']: r for r in jsonl(args.graph) if r.get('record') == 'decl'}
        selected = {d['name'] for entry in entries.values() for d in entry['compilerDeclarations'] if d['selected']}
        for name in selected:
            row = rows[name]
            require(not row['hasSorryAx'] and set(row['axioms']) <= ALLOWED_AXIOMS, 'Unreviewed original axioms: ' + name)
            dependencies = set(row.get('typeDeps', []) + row.get('valueDeps', []) + row.get('constructors', []))
            require(dependencies <= selected | set(prior_constants),
                    'Missing carrier/proof dependency: ' + name + ': ' + str(sorted(dependencies - selected - set(prior_constants))))
        for module in MODULES:
            allowed = ({i['sourceCompilerTermModule'] for i in candidates[module]['candidates'] if i['source435PathExists']}
                       | set(candidates[module].get('source435Imports', [])))
            require(set(plans[module]['source435Imports']) <= allowed, 'Imports absent from reviewed original-compiler candidates')
            selected_names = {d['name'] for d in entries[module]['compilerDeclarations'] if d['selected']}
            output, entry_report = extract_one(entries[module], artifacts[module], config, selected_names, args, plans[module])
            path = out / 'CarrierSmall' / (MODULES[module] + '.lean')
            source_info = next(s for s in unit['sources'] if s['module'] == module)
            entry_report.update(source=str(path), sourceSha256=digest(output), byteLength=len(output),
                                adaptationProvenance=source_info['provenance'])
            pending_outputs.append((path, output))
            report['modules'].append(entry_report)
        # Validate every module before writing any Lean output.
        for path, output in pending_outputs:
            path.parent.mkdir(exist_ok=True)
            path.write_bytes(output)
        del args.prior_modules
        report.update(status='small-source-draft-generated-needs-main-CI', parserJobId=ci['job_id'],
                      dependencyMaps=unit.get('dependencies', []),
                      inputs={key: {'path': str(Path(value).resolve()), 'sha256': file_hash(value)}
                              for key, value in vars(args).items() if key != 'out'},
                      nextStep='Main agent submits each small source to accepted Lean 4.35 InfoTree oracle; validate original auxiliary names, dependencies, axioms, then generate AbcAdaptation.Reference wrappers from accepted refs.')
    except (ValueError, KeyError, OSError, TypeError, AttributeError) as error:
        report.update(status='refused-unbound-or-unsupported-input', error=str(error))
    (out / 'foundation-small-source-report.json').write_text(json.dumps(report, ensure_ascii=False, indent=2) + '\n')
    print(json.dumps({'status': report['status'], 'error': report.get('error'),
                      'modules': [{k: e[k] for k in ['module', 'source', 'sourceSha256', 'byteLength']} for e in report['modules'] if 'source' in e]}, indent=2))
    return 0 if report['status'] == 'small-source-draft-generated-needs-main-CI' else 2


if __name__ == '__main__':
    raise SystemExit(main())
