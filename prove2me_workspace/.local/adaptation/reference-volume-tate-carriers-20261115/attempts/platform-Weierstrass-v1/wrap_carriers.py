#!/usr/bin/env python3
"""Generate five next-level Definitions bundles from accepted small-source facts.

No compilation, CI submission, API, Git, source declaration scan, or reference
rewriting. Whole source contexts are nested inside AbcAdaptation.Reference.
"""
import argparse
import copy
import json
from pathlib import Path

from subtract_carriers import (TASK, MODULES, ALLOWED_AXIOMS, Coordinates,
                                 require, digest, file_hash, load, jsonl, span, walk)

PREFIX = 'AbcAdaptation.Reference'
from carrier_contract import (unit_config, dependency_evidence, validate_import_graph,
                              validate_platform_imports, project_name, PROJECT_PREFIXES)
UNIT = None
SEMANTIC_OPTIONS = [
    {'name': 'relaxedAutoImplicit', 'type': 'bool', 'value': False},
    {'name': 'maxSynthPendingDepth', 'type': 'nat', 'value': 3},
]


def adaptation_provenance(module):
    require(module in MODULES and UNIT is not None, 'Unexpected provenance source module')
    p = next(s['provenance'] for s in UNIT['sources'] if s['module'] == module)
    return {'insertedByAdaptation': True, **p, 'originalNoticeRetained': True}


def adaptation_header(module):
    info = adaptation_provenance(module)
    return ('/-\n'
            'Adaptation provenance: this block was inserted by the adaptation; it is not an original source notice.\n'
            'Original source path: ' + info['originalSourcePath'] + '\n'
            'Original authors: ' + info['originalAuthors'] + '\n'
            'Original repository: ' + info['originalRepository'] + '\n'
            'Original commit: ' + info['originalCommit'] + '\n'
            'Original license: ' + info['originalLicense'] + '; the original copyright and license notice is retained below.\n'
            + ('Effective compiler source override: accepted graph ' + info['acceptedGraphJobId'] + '; upstream source differs from the compiler input.\n'
               'Effective source SHA256: ' + info['effectiveSourceOverride']['effectiveSourceSha256'] + '\n'
               'Exact upstream/effective patch SHA256: ' + info['effectiveSourceOverride']['patch']['sha256'] + '\n'
               if info.get('sourceOverridden', False) else '')
            + '-/\n')


def name_parts(value):
    if value == []:
        return []
    require(isinstance(value, list) and len(value) == 3 and value[1] in {'str', 'num'}, 'Invalid structural Lean.Name')
    require((value[1] == 'str' and isinstance(value[2], str))
            or (value[1] == 'num' and isinstance(value[2], int)), 'Invalid typed Lean.Name component')
    return name_parts(value[0]) + [(value[1], value[2])]


def encode_parts(parts):
    value = []
    for kind, part in parts:
        value = [value, kind, part]
    return value


def source_name(text):
    # Module and namespace identifiers supplied by this generator are explicit
    # string components. Original constant Names always come from the compiler.
    return encode_parts([('str', part) for part in text.split('.')])


def add_prefix(value):
    return encode_parts(name_parts(source_name(PREFIX)) + name_parts(value))


def name_text(value):
    return '.'.join(str(part) for _, part in name_parts(value))


def accept_terminal(path, expected_job, expected_hash, allow_runtime=False):
    require(file_hash(path) == expected_hash, 'Compiler receipt changed')
    ci = load(path)
    result = ci['result']
    require(ci['job_id'] == expected_job and ci['status'] == 'succeeded'
            and result['exit_code'] == 0, 'Compiler job not terminal success')
    require(result['snapshot']['workspace_mode'] == 'exclusive_worktree'
            and result['snapshot']['snapshot_id'] is None, 'Compiler workspace not exclusive')
    rss = ci['resources'].get('peak_rss_bytes')
    require(rss is not None and rss <= 16 * 1024**3, 'Compiler physical RSS unknown or above 16 GiB')
    require(all(d.get('severity') == 'warning' for d in result.get('diagnostics', [])), 'Compiler error diagnostic')
    text = (result.get('stdout', '') + '\n' + result.get('stderr', '')).casefold()
    require('panic' not in text and 'error:' not in text, 'Compiler panic/error output')
    request = ci['request']
    require(request['language'] == 'lean', 'Unexpected compiler language')
    actual = result['actual_arguments']
    require(actual and Path(actual[0]).name == 'lean', 'Unexpected compiler executable')
    if request['task_type'] == 'full' and request['target'] == 'module':
        require(allow_runtime, 'Runtime receipt is invalid for a leaf compiler gate')
        arguments = request['parameters']['args']
        require(len(arguments) == 3 and arguments[0] == '--run' and actual[1:] == arguments,
                'Runtime actual arguments differ from structured single-config driver request')
    else:
        require(request['task_type'] == 'leaf' and request['target'] == 'file',
                'Unexpected compiler request kind')
        require(len(actual) == 2 and actual[1] == request['parameters']['source'],
                'Compiler actual source differs from request')
    return ci


def oracle_config_path(ci):
    request = ci['request']
    if request['task_type'] == 'full':
        return request['parameters']['args'][2]
    return request['environment']['REFERENCE_STAGE2_CONFIG']


def accept_driver(acceptance_path, ci_path):
    require(acceptance_path and ci_path, 'Runtime oracle needs driver leaf acceptance and receipt')
    accepted = load(acceptance_path)
    require(accepted['schema'] == 'reference-runtime-oracle-driver-acceptance-v1'
            and accepted['status'] == 'accepted', 'Runtime driver leaf not accepted')
    ci = accept_terminal(ci_path, accepted['job_id'], accepted['compilerReceiptSha256'])
    request = ci['request']
    source = Path(request['parameters']['source'])
    if not source.is_absolute():
        source = Path(request['workspace']) / source
    require(source.resolve() == Path(accepted['source']).resolve()
            and file_hash(source) == accepted['sourceSha256'], 'Runtime driver source identity changed')
    return accepted


def accepted_oracle(receipt_path, ci_path, driver_acceptance=None, driver_ci=None):
    receipt = load(receipt_path)
    if 'receiptValidation' not in receipt:
        # Accept the compiler's authentic raw index directly. Bind it to the
        # terminal scheduler receipt, config path/content, and all source/output
        # artifacts before constructing the equivalent validation in memory.
        raw_ci = load(ci_path)
        accept_terminal(ci_path, raw_ci['job_id'], file_hash(ci_path), allow_runtime=True)
        require(receipt['schema'] == 'reference-stage2-index-v1' and receipt['complete'] is True
                and receipt['requestedFiles'] == receipt['finishedFiles'] == len(receipt['results']) == 1,
                'Raw InfoTree index is not complete single-module success')
        config_path = oracle_config_path(raw_ci)
        require(Path(config_path).resolve() == Path(receipt['configPath']).resolve()
                and load(config_path) == receipt['config'], 'Raw InfoTree index config differs from compiler config')
        require(Path(receipt_path).resolve() == (Path(receipt['config']['outputDir']) / 'index.json').resolve(),
                'Raw InfoTree index path differs from configured output directory')
        receipt = copy.deepcopy(receipt)
        result, = receipt['results']
        configured, = receipt['config']['files']
        require(result['status'] == 'success' and result['module'] == configured['module']
                and result['file'] == configured['file']
                and Path(result['source']).resolve() == Path(configured['source']).resolve(), 'Raw index source config mismatch')
        for path_key, hash_key in [('source', 'rawSha256'), ('coordinateSource', 'normalizedSha256'),
                                   ('output', 'outputSha256'), ('diagnostics', 'diagnosticsSha256')]:
            result[hash_key] = file_hash(result[path_key])
        require(result['rawSha256'] == configured['sourceSha256']
                and result['normalizedSha256'] == configured['normalizedSha256'], 'Raw index source hash differs from compiler config')
        receipt.update(receiptValidation='source-output-sha256-and-terminal-summaries-v1',
                       noPanicOrErrorDiagnostics=True, compilerJobId=raw_ci['job_id'],
                       compilerReceiptSha256=file_hash(ci_path), configSha256=file_hash(config_path))
    require(receipt['receiptValidation'] == 'source-output-sha256-and-terminal-summaries-v1'
            and receipt['complete'] is True and receipt['noPanicOrErrorDiagnostics'] is True,
            'Small-source InfoTree receipt not accepted')
    ci = accept_terminal(ci_path, receipt['compilerJobId'], receipt['compilerReceiptSha256'], allow_runtime=True)
    if ci['request']['task_type'] == 'full':
        accepted_driver = accept_driver(driver_acceptance, driver_ci)
        driver = Path(ci['request']['parameters']['args'][1])
        if not driver.is_absolute():
            driver = Path(ci['request']['workspace']) / driver
        require(driver.resolve() == Path(accepted_driver['source']).resolve(), 'Runtime oracle uses another driver')
    require(file_hash(receipt['configPath']) == receipt['configSha256']
            and load(receipt['configPath']) == receipt['config'], 'Small-source config changed')
    require(Path(oracle_config_path(ci)).resolve() == Path(receipt['configPath']).resolve(),
            'Compiler small-source config path mismatch')
    require(receipt['config']['namePrefixes'] == [] and receipt['config']['options'] == SEMANTIC_OPTIONS,
            'Small-source InfoTree scope/semantic options differ')
    result, = receipt['results']
    require(result['status'] == 'success', 'Small-source InfoTree module failed')
    for path_key, hash_key in [('source', 'rawSha256'), ('coordinateSource', 'normalizedSha256'),
                               ('output', 'outputSha256'), ('diagnostics', 'diagnosticsSha256')]:
        require(file_hash(result[path_key]) == result[hash_key], 'Small-source artifact changed: ' + path_key)
    diagnostic = load(result['diagnostics'])
    require(diagnostic['hasErrors'] is False, 'Small-source compiler reported errors')
    require(not any(any(word in message.casefold() for word in ['sorry', 'panic', 'error:'])
                    for message in diagnostic['messages']), 'Small-source diagnostic requires proof review')
    facts = jsonl(result['output'])
    source, = [f for f in facts if f['kind'] == 'source']
    summary, = [f for f in facts if f['kind'] == 'summary']
    require(facts[0] == source and facts[-1] == summary and summary['status'] == 'success', 'Invalid InfoTree framing')
    require(source['schema'] == 'reference-stage2-v1' and source['module'] == result['module'] == summary['module']
            and source['mainModule'] == result['module'] and source['namePrefixes'] == []
            and source['offsetCoordinate'] == 'lean-normalized-utf8', 'Small-source InfoTree identity mismatch')
    for count, kind in [('declarationCount', 'decl'), ('referenceCount', 'ref')]:
        require(sum(f['kind'] == kind for f in facts) == summary[count] == result[count], 'Small-source fact count mismatch')
    data = Path(result['coordinateSource']).read_bytes()
    require(data == Path(result['source']).read_bytes().replace(b'\r\n', b'\n')
            and len(data) == source['byteLength'] == result['byteLength'], 'Small-source normalized bytes mismatch')
    coords = Coordinates(data)
    for fact in facts:
        if fact.get('range') is not None:
            coords.verify(fact['range'])
        for field in ['headerSyntax', 'contextSyntax']:
            if isinstance(fact.get(field), dict):
                for node in walk(fact[field]):
                    if node.get('range') is not None:
                        coords.verify(node['range'])
        if fact['kind'] == 'ref':
            coords.verify({'start': fact['start'], 'end': fact['end']})
    return result, facts, ci


class Composer:
    def __init__(self, source, data, original_report):
        self.source = source
        self.data = data
        self.coords = Coordinates(data)
        self.original_report = original_report
        self.output = bytearray()
        self.pieces = []

    def generated(self, text, kind, **metadata):
        value = text.encode() if isinstance(text, str) else text
        a = len(self.output)
        self.output.extend(value)
        if value:
            self.pieces.append({'kind': kind, 'start': a, 'end': len(self.output),
                                'sha256': digest(value), **metadata})

    def copied(self, a, b, kind):
        if a == b:
            return
        start = len(self.output)
        self.output.extend(self.data[a:b])
        part = {'kind': kind, 'start': start, 'end': len(self.output),
                'sha256': digest(self.data[a:b]), 'smallSource': self.source,
                'smallSourceRange': self.coords.range(a, b)}
        overlaps = []
        for original in self.original_report['provenance']:
            x, y = span(original['outputRange'])
            lo, hi = max(a, x), min(b, y)
            if lo >= hi:
                continue
            detail = {'smallSourceRange': self.coords.range(lo, hi), 'kind': original['kind']}
            if original['kind'] == 'copied':
                oa, _ = span(original['originalRange'])
                source_data = Path(original['originalCoordinateSource']).read_bytes()
                original_coords = Coordinates(source_data)
                old_a, old_b = oa + lo - x, oa + hi - x
                require(source_data[old_a:old_b] == self.data[lo:hi], 'Composed original provenance bytes mismatch')
                detail.update(originalSource=original['originalSource'],
                              originalCoordinateSource=original['originalCoordinateSource'],
                              originalRange=original_coords.range(old_a, old_b))
            overlaps.append(detail)
        require(sum(span(o['smallSourceRange'])[1] - span(o['smallSourceRange'])[0] for o in overlaps) == b - a,
                'Original provenance does not cover copied wrapper bytes')
        part['originalProvenance'] = overlaps
        self.pieces.append(part)

    def gap(self, a, b, final=False):
        original = self.data[a:b]
        if original.strip(b' \t\r\n') == b'':
            self.generated('\n\n', 'normalized-gap', replacedSmallSourceRange=self.coords.range(a, b))
        else:
            # Comments outside commands, if any, remain byte-identical.
            self.copied(a, b, 'copied-intercommand-comment')
            if not original.endswith(b'\n\n'):
                self.generated('\n\n' if not original.endswith(b'\n') else '\n', 'gap-separator')

    def finish(self):
        result = bytes(self.output)
        coords = Coordinates(result)
        for p in self.pieces:
            p['outputRange'] = coords.range(p.pop('start'), p.pop('end'))
            a, b = span(p['outputRange'])
            require(digest(result[a:b]) == p['sha256'], 'Wrapper provenance output hash mismatch')
        require(sum(span(p['outputRange'])[1] - span(p['outputRange'])[0] for p in self.pieces) == len(result),
                'Wrapper provenance does not partition all output bytes')
        require(result.endswith(b'\n') and not result.endswith(b'\n\n'), 'Wrapper EOF is not a single newline')
        for line in result.splitlines():
            require(line == line.rstrip(b' \t'), 'Original command has trailing whitespace; command bytes cannot be cleaned')
        return result, self.pieces


def imports_from_ast(header):
    result = []
    for node in walk(header):
        if node['syntaxKind'] == 'Lean.Parser.Module.import':
            identifiers = [child['identifier'] for child in walk(node) if 'identifier' in child]
            require(len(identifiers) == 1, 'Unsupported original import AST')
            result.append(identifiers[0])
    return result


def make_wrapper(module, split, oracle, facts, platform_imports, original_parser):
    data = Path(oracle['coordinateSource']).read_bytes()
    require(digest(data) == split['sourceSha256'], 'Small-source input differs from original subtraction')
    source, = [f for f in facts if f['kind'] == 'source']
    require(imports_from_ast(source['headerSyntax']) == split['source435Imports'], 'Small-source import AST differs from subtraction')
    ha, hb = span(source['headerSyntax']['range'])
    commands = [f for f in facts if f['kind'] == 'command' and f['syntaxKind'] != 'Lean.Parser.Command.eoi']
    expected = [c for c in split['retainedCommands'] if c['syntaxKind'] != 'Lean.Parser.Command.eoi']
    require(len(commands) == len(expected), 'Small-source command inventory differs from original subtraction')
    declarations = [f for f in facts if f['kind'] == 'decl']
    require(len(declarations) == sum(c['role'] == 'selected-declaration' for c in expected), 'Small-source has extra/missing declaration command')
    for cmd, old in zip(commands, expected):
        require(cmd['range'] == old['outputRange'] and cmd['syntaxKind'] == old['syntaxKind']
                and cmd['isDeclaration'] == (old['role'] == 'selected-declaration'), 'Small-source command order/range/classification changed')
        require(digest(data[slice(*span(cmd['range']))]) == old['sha256'], 'Original command bytes changed')
        if cmd['isDeclaration']:
            decl, = [d for d in declarations if (d['declStart']['offset'], d['declEnd']['offset']) == span(cmd['range'])]
            require(not decl['generationIssue'] and decl['privateTok'] is None, 'Unsupported private/atomic source declaration')
    composer = Composer(oracle['source'], data, split)
    composer.generated(adaptation_header(module), 'inserted-adaptation-provenance',
                       provenance=adaptation_provenance(module))
    composer.copied(0, ha, 'copied-license-prefix')
    composer.generated('\n'.join('import ' + name for name in platform_imports), 'platform-import-header',
                       replacedSmallSourceRange=source['headerSyntax']['range'])
    composer.generated('\n\nset_option relaxedAutoImplicit false\nset_option maxSynthPendingDepth 3\n\nnamespace ' + PREFIX,
                       'semantic-options-and-namespace')
    previous = hb
    command_maps = []
    original_decls = {f['commandIndex']: f for f in original_parser if f['kind'] == 'decl'}
    for command, old in zip(commands, expected):
        a, b = span(command['range'])
        require(previous <= a < b, 'Small-source commands overlap')
        composer.gap(previous, a)
        start = len(composer.output)
        composer.copied(a, b, 'copied-original-command')
        mapping = {'originalCommandIndex': old['commandIndex'], 'syntaxKind': old['syntaxKind'],
                   'role': old['role'], 'originalRange': old['originalRange'], 'smallSourceRange': old['outputRange'],
                   'wrapperStart': start, 'wrapperEnd': len(composer.output), 'sha256': old['sha256'],
                   'selectedCompilerDeclarations': old['selectedCompilerDeclarations'], 'bodyRanges': []}
        if old['role'] == 'selected-declaration':
            original_decl = original_decls[old['commandIndex']]
            require(original_decl['range'] == old['originalRange'], 'Original parser declaration map changed')
            oa, ob = span(old['originalRange'])
            original_data = Path(split['originalCoordinateSource']).read_bytes()
            for value in original_decl['proofAndDefinitionBodyRanges']:
                x, y = span(value)
                require(oa <= x <= y <= ob, 'Original body range outside selected command')
                small_a, small_b = a + x - oa, a + y - oa
                require(data[small_a:small_b] == original_data[x:y], 'Original proof/definition body changed')
                mapping['bodyRanges'].append({'originalRange': value,
                                              'smallSourceRange': Coordinates(data).range(small_a, small_b),
                                              'wrapperStart': start + x - oa, 'wrapperEnd': start + y - oa,
                                              'sha256': digest(original_data[x:y])})
        command_maps.append(mapping)
        previous = b
    composer.gap(previous, len(data), final=True)
    composer.generated('end ' + PREFIX + '\n', 'namespace-close')
    output, provenance = composer.finish()
    coords = Coordinates(output)
    for mapping in command_maps:
        mapping['wrapperRange'] = coords.range(mapping.pop('wrapperStart'), mapping.pop('wrapperEnd'))
        require(digest(output[slice(*span(mapping['wrapperRange']))]) == mapping['sha256'], 'Wrapped complete command changed')
        for body in mapping['bodyRanges']:
            body['wrapperRange'] = coords.range(body.pop('wrapperStart'), body.pop('wrapperEnd'))
            require(digest(output[slice(*span(body['wrapperRange']))]) == body['sha256'], 'Wrapped proof/definition body changed')
    return output, provenance, command_maps


def blind_packet(data, provenance, command_maps, original_parser):
    """Remove narrative by AST ranges, the license prefix, and inserted provenance.

    Small-oracle command ranges bind the unchanged original command bytes. The
    original parser supplies nested field/constructor docs that the canonical
    small-source oracle does not currently serialize as a whole declaration AST.
    """
    parser_commands = {f['commandIndex']: f for f in original_parser if f['kind'] == 'command'}
    removals = []
    for piece in provenance:
        if piece['kind'] in {'copied-license-prefix', 'inserted-adaptation-provenance'}:
            a, b = span(piece['outputRange'])
            kind = ('license-prefix-before-authenticated-import-header'
                    if piece['kind'] == 'copied-license-prefix' else 'inserted-adaptation-provenance')
            removals.append((a, b, kind))
    for command in command_maps:
        wa, wb = span(command['wrapperRange'])
        oa, ob = span(command['originalRange'])
        original = parser_commands[command['originalCommandIndex']]
        require(original['range'] == command['originalRange'], 'Blind packet original parser command mismatch')
        for node in walk(original['commandSyntax']):
            if node['syntaxKind'] not in {'Lean.Parser.Command.docComment', 'Lean.Parser.Command.moduleDoc'}:
                continue
            x, y = span(node['range'])
            require(oa <= x <= y <= ob, 'Documentation AST range outside original complete command')
            removals.append((wa + x - oa, wa + y - oa, node['syntaxKind']))
    maximal = []
    for a, b, kind in sorted(set(removals), key=lambda x: (x[0], -x[1])):
        if maximal and maximal[-1][0] <= a and b <= maximal[-1][1]:
            continue
        require(not maximal or maximal[-1][1] <= a, 'Overlapping blind AST deletion ranges')
        maximal.append((a, b, kind))
    output = bytearray()
    previous = 0
    mapping = []
    coords = Coordinates(data)
    for a, b, kind in maximal:
        output.extend(data[previous:a])
        mapping.append({'productionRange': coords.range(a, b), 'kind': kind,
                        'removedSha256': digest(data[a:b])})
        previous = b
    output.extend(data[previous:])
    # The final namespace close already ends in exactly one newline. No semantic
    # source token is reformatted in this independent readback packet.
    return bytes(output), mapping


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for arg in ['small-source-report', 'parser-acceptance', 'original-exprs', 'original-exprs-acceptance',
                'original-exprs-ci-result', 'imports', 'reviewed-imports', 'unit-config', 'out']:
        parser.add_argument('--' + arg, required=True)
    parser.add_argument('--oracle-receipt', action='append', required=True)
    parser.add_argument('--oracle-ci-result', action='append', required=True)
    parser.add_argument('--oracle-driver-acceptance')
    parser.add_argument('--oracle-driver-ci-result')
    args = parser.parse_args()
    out = Path(args.out).resolve()
    require(TASK in out.parents, 'Output outside assigned task directory')
    out.mkdir(parents=True, exist_ok=True)
    report = {'schema': 'foundation-wrapper-generation-v1', 'status': 'inputs-pending', 'bundles': [],
              'compilation': 'not-run', 'api': 'not-used', 'git': 'not-used'}
    writes = []
    try:
        for key, value in vars(args).items():
            if key != 'out' and value is not None:
                for path in value if isinstance(value, list) else [value]:
                    require(Path(path).is_file(), 'Required input missing: ' + path)
        global UNIT
        UNIT = unit_config(args.unit_config)
        prior_constants, prior_modules, dependencies = dependency_evidence(UNIT)
        split_report = load(args.small_source_report)
        require(split_report['inputs']['unit_config']['sha256'] == file_hash(args.unit_config), 'Unit config differs from source subtraction')
        require(split_report['status'] == 'small-source-draft-generated-needs-main-CI', 'Subtraction report not successful')
        splits = {s['module']: s for s in split_report['modules']}
        parser_acceptance = load(args.parser_acceptance)
        require(parser_acceptance['status'] == 'accepted' and parser_acceptance['job_id'] == split_report['parserJobId'], 'Original parser acceptance mismatch')
        original_parser = {f['module']: f for f in parser_acceptance['outputs']}
        candidates = {m['module']: m for m in load(args.imports)}
        reviewed = load(args.reviewed_imports)
        require(reviewed['schema'] == 'foundation-precise-import-review-v1' and reviewed['status'] == 'reviewed'
                and reviewed['importsCandidateSha256'] == file_hash(args.imports), 'Platform import review unbound')
        plans = {m['module']: m for m in reviewed['modules']}
        validate_import_graph(plans, prior_modules)
        require(set(splits) == set(original_parser) == set(candidates) == set(plans) == set(MODULES), 'Unexpected module set')
        original_acceptance = load(args.original_exprs_acceptance)
        require(original_acceptance['schema'] == 'foundation-original-exprs-acceptance-v1'
                and original_acceptance['status'] == 'accepted'
                and original_acceptance['noPanicOrErrorDiagnostics'] is True
                and original_acceptance['originalExprsSha256'] == file_hash(args.original_exprs), 'Original Expr export not accepted/bound')
        original_ci = accept_terminal(args.original_exprs_ci_result, original_acceptance['job_id'], original_acceptance['compilerReceiptSha256'])
        export_env = original_ci['request']['environment']
        export_keys = [k for k in ['FOUNDATION_EXPORT_CONFIG', 'NEXT_CARRIER_EXPORT_CONFIG'] if k in export_env]
        require(len(export_keys) == 1, 'Original exporter config environment key is ambiguous/missing')
        original_config_path = export_env[export_keys[0]]
        require(file_hash(original_config_path) == original_acceptance['configSha256'], 'Original exporter config hash changed')
        original_config = load(original_config_path)
        require(Path(original_config['outputFile']).resolve() == Path(args.original_exprs).resolve(), 'Original Expr output path mismatch')
        originals = load(args.original_exprs)
        require(originals['schema'] == 'foundation-original-exprs-v2' and originals['compilerVersion'] == '4.35.0-rc3'
                and originals['inventorySha256'] == original_acceptance['inventorySha256']
                and originals['graphSha256'] == parser_acceptance['graphSha256'], 'Original Expr source identity mismatch')
        require(original_config['inventorySha256'] == originals['inventorySha256']
                and original_config['graphSha256'] == originals['graphSha256'], 'Original exporter config identity mismatch')
        original_records = {r['name']: r for r in originals['records']}
        require(len(original_records) == len(originals['records']), 'Duplicate original compiler name')
        require(len(args.oracle_receipt) == len(args.oracle_ci_result) == 5, 'Need five single-module accepted InfoTree receipts')
        oracles = {}
        for rp, cp in zip(args.oracle_receipt, args.oracle_ci_result):
            result, facts, ci = accepted_oracle(rp, cp, args.oracle_driver_acceptance, args.oracle_driver_ci_result)
            module = result['module']
            require(module in MODULES and module not in oracles, 'Duplicate/unknown small-source oracle module')
            oracles[module] = (result, facts, ci)
        constants = list(prior_constants.values())
        module_map = []
        for module in MODULES:
            split = splits[module]
            result, facts, ci = oracles[module]
            artifact = original_parser[module]
            require(artifact['sha256'] == file_hash(artifact['path']) == split['parserFacts']['sha256'], 'Original parser artifact changed')
            pf = jsonl(artifact['path'])
            require(pf[-1]['status'] == 'success', 'Original parser terminal summary missing')
            platform_imports = plans[module]['platform433Candidates']
            allowed = ({m['platform433Candidate'] for m in candidates[module]['candidates'] if m['platform433CandidatePathExists']}
                       | {m for m in candidates[module].get('platform433Candidates', []) if m.startswith('Definitions.Def_')})
            require(platform_imports and len(platform_imports) == len(set(platform_imports))
                    and set(platform_imports) <= allowed
                    , 'Unreviewed platform import')
            validate_platform_imports(module, platform_imports, prior_modules)
            data, provenance, command_maps = make_wrapper(module, split, result, facts, platform_imports, pf)
            slug = 'AbcAdaptation_Reference_' + module.replace('.', '_')
            wrapped_module = 'Definitions.Def_' + slug
            path = out / 'Definitions' / ('Def_' + slug + '.lean')
            payload_path = out / 'payloads' / (slug + '.json')
            payload = {'definition_name': slug, 'code': data.decode()}
            writes.extend([(path, data), (payload_path, (json.dumps(payload, ensure_ascii=False, indent=2) + '\n').encode())])
            blind, blind_removals = blind_packet(data, provenance, command_maps, pf)
            blind_path = out / 'blind' / ('Def_' + slug + '.lean')
            blind_payload_path = out / 'blind-payloads' / (slug + '.json')
            writes.extend([(blind_path, blind), (blind_payload_path,
                          (json.dumps({'definition_name': slug, 'code': blind.decode()}, ensure_ascii=False, indent=2) + '\n').encode())])
            records = [r for r in originals['records'] if r['module'] == module]
            selected = {r['name'] for r in records if r['selected']}
            require(selected == set(split['selectedCompilerDeclarations']), 'Original/small selected compiler set differs')
            compiler_facts = {f['name']: f for f in pf if f['kind'] == 'compilerDecl'}
            for record in records:
                require(name_text(record['nameExpr']) == record['name'], 'Original structural Name mismatch')
                for field in ['axioms', 'typeAxioms', 'valueAxioms']:
                    require(set(record[field]) <= ALLOWED_AXIOMS, 'Original constant has unreviewed axiom')
                require(record['sourceSha256'] == split['normalizedSha256'], 'Original compiler source SHA differs')
                compiler_fact = compiler_facts[record['name']]
                owner = next((m for m in command_maps if m['originalCommandIndex'] in compiler_fact['containingCommandIndices']), None)
                expectation = ('required-selected' if record['selected'] else 'original-range-retained-command' if owner
                               else 'original-no-range-unclassified' if compiler_fact['compilerRange'] is None
                               else 'original-range-removed-command')
                constants.append({'originalName': record['name'], 'originalNameExpr': record['nameExpr'],
                                  'sourceName': record['name'], 'sourceNameExpr': record['nameExpr'],
                                  'wrappedName': PREFIX + '.' + record['name'], 'wrappedNameExpr': add_prefix(record['nameExpr']),
                                  'originalModule': module, 'originalModuleExpr': source_name(module),
                                  'sourceModule': module, 'sourceModuleExpr': source_name(module),
                                  'wrappedModule': wrapped_module, 'wrappedModuleExpr': source_name(wrapped_module),
                                  'originalConstantKind': record['constantKind'], 'levelParams': record['levelParams'],
                                  'originalIsProposition': record['isProposition'], 'selected': record['selected'],
                                  'presenceExpectation': expectation, 'originalCompilerRange': compiler_fact['compilerRange'],
                                  'owningRetainedCommand': owner['originalCommandIndex'] if owner else None,
                                  'mappingRole': 'current-unit', 'mappingIdentity': 'candidate-only-until-actual-compiler-audit',
                                  'mappingStatus': 'structural-prefix-candidate; source and wrapped generated identities require kernel audit'})
            refs = [f for f in facts if f['kind'] == 'ref' and project_name(f['const'])]
            require(all(f['const'] in original_records or f['const'] in prior_constants for f in refs),
                    'Small-source InfoTree has missing project/proof carrier references: ' +
                    str(sorted({f['const'] for f in refs if f['const'] not in original_records and f['const'] not in prior_constants})))
            module_map.append({'originalModule': module, 'originalModuleExpr': source_name(module),
                               'sourceModule': module, 'sourceModuleExpr': source_name(module),
                               'sourcePath': result['source'], 'sourceSha256': result['normalizedSha256'],
                               'wrappedModule': wrapped_module, 'wrappedModuleExpr': source_name(wrapped_module),
                               'wrappedPath': str(path), 'wrappedSha256': digest(data), 'definitionName': slug,
                               'originalExprRecordNames': [r['name'] for r in records], 'selectedConstantNames': sorted(selected)})
            preamble_end = span(command_maps[0]['wrapperRange'])[0]
            preamble = data[:preamble_end]
            report['bundles'].append({'module': module, 'definitionName': slug, 'wrappedModule': wrapped_module,
                                      'adaptationProvenance': adaptation_provenance(module),
                                      'path': str(path), 'sha256': digest(data), 'payload': str(payload_path),
                                      'payloadSha256': digest((json.dumps(payload, ensure_ascii=False, indent=2) + '\n').encode()),
                                      'sourceOracleJobId': ci['job_id'], 'platformImports': platform_imports,
                                      'sourceImports': split['source435Imports'], 'semanticOptions': SEMANTIC_OPTIONS,
                                      'preamble': preamble.decode(), 'preambleSha256': digest(preamble),
                                      'preambleRange': Coordinates(data).range(0, preamble_end),
                                      'wholeSourceNamespaceWrapper': PREFIX, 'projectOccurrenceEdits': [],
                                      'provenance': provenance, 'commandMaps': command_maps,
                                      'blindReadback': {'path': str(blind_path), 'sha256': digest(blind),
                                                       'payload': str(blind_payload_path), 'removedNarrative': blind_removals,
                                                       'basis': 'Authenticated original AST nested docs mapped through byte-identical small-oracle command ranges; license prefix bounded by authenticated import header; adaptation provenance removed by generated segment range'},
                                      'formalAcceptance': {'platformCompiler': False, 'typeValueKernelAudit': False,
                                                           'generatedIdentityAudit': False, 'axiomAudit': False}})
        mapping = {'schema': 'foundation-typed-name-module-map-v1', 'status': 'compiler-original-bound; source/wrapped-kernel-audit-pending',
                   'prefix': PREFIX, 'prefixExpr': source_name(PREFIX), 'originalExprsPath': str(Path(args.original_exprs).resolve()),
                   'originalExprsSha256': file_hash(args.original_exprs), 'originalExprJobId': original_ci['job_id'],
                   'modules': module_map, 'constants': constants,
                   'projectPrefixes': list(PROJECT_PREFIXES), 'dependencyMaps': dependencies,
                   'priorModules': list(prior_modules.values()),
                   'auditRule': 'Require all required-selected entries. Discover actual generated names from source/wrapped compiler environments; do not treat unclassified original no-range entries as established mappings.'}
        writes.append((out / 'typed-original-source-wrapped-map.json', (json.dumps(mapping, ensure_ascii=False, indent=2) + '\n').encode()))
        imports_map = {'schema': 'foundation-import-preamble-map-v1',
                       'bundles': [{k: b[k] for k in ['module', 'definitionName', 'wrappedModule', 'platformImports', 'sourceImports',
                                                       'semanticOptions', 'wholeSourceNamespaceWrapper', 'preamble',
                                                       'preambleSha256', 'preambleRange', 'adaptationProvenance']} for b in report['bundles']]}
        writes.append((out / 'import-preamble-map.json', (json.dumps(imports_map, ensure_ascii=False, indent=2) + '\n').encode()))
        for path, value in writes:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(value)
        report.update(status='five-wrapper-drafts-generated-main-platform-CI-and-kernel-audit-pending',
                      definitionsBundleCount=5, selectedConstantCount=sum(r['selected'] for r in constants),
                      inputHashes={k: [dict(path=str(Path(p).resolve()), sha256=file_hash(p)) for p in v]
                                   if isinstance(v, list) else dict(path=str(Path(v).resolve()), sha256=file_hash(v))
                                   for k, v in vars(args).items() if k != 'out' and v is not None})
    except (ValueError, KeyError, OSError, TypeError, AttributeError) as error:
        report.update(status='refused-unbound-or-unsupported-input', error=str(error))
    (out / 'foundation-wrapper-report.json').write_text(json.dumps(report, ensure_ascii=False, indent=2) + '\n')
    print(json.dumps({'status': report['status'], 'error': report.get('error'),
                      'bundles': [{k: b[k] for k in ['module', 'path', 'sha256', 'definitionName']} for b in report['bundles']]}, indent=2))
    return 0 if report['status'].startswith('five-wrapper-drafts-generated') else 2


if __name__ == '__main__':
    raise SystemExit(main())
