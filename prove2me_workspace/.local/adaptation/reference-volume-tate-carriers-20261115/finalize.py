#!/usr/bin/env python3
"""Validate actual delivery and prepare a narrow registry update; no CI/API/Git."""
import sys
sys.dont_write_bytecode = True
from pathlib import Path
import argparse
import copy
import json
import math
import runpy
from common import (ROOT, WORKSPACE, UNIT, REGISTRY, PREFIX, NAMES, DEFINITIONS,
                    TERMINAL, digest, exact_path, load_list, read, require, write_new)


def resources(receipt, name):
    q, rs, v = receipt['request'], receipt.get('result') or {}, receipt.get('resources') or {}
    status = receipt['status']
    require(status in TERMINAL, 'Receipt is not terminal: ' + name)
    cpu, user, system = [v.get(k) for k in ['cpu_time_seconds', 'cpu_user_seconds', 'cpu_system_seconds']]
    summed = user + system if user is not None and system is not None else None
    require(cpu is None or summed is None or math.isclose(cpu, summed, abs_tol=0.1),
            'CPU total differs from user + system: ' + name)
    manifest = q.get('worktree_manifest', {})
    return {'receipt': name, 'receipt_sha256': digest(UNIT / name), 'job_id': receipt['job_id'],
        'status': status, 'input_head': manifest.get('head'),
        'source_sha256': manifest.get('source_sha256'), 'input_hashes': manifest.get('input_hashes'),
        'workspace': q.get('workspace'), 'parameters': q.get('parameters'),
        'actual_arguments': rs.get('actual_arguments'), 'snapshot': rs.get('snapshot'),
        'exit_code': rs.get('exit_code'), 'diagnostics': rs.get('diagnostics'),
        'stdout': rs.get('stdout'), 'stderr': rs.get('stderr'),
        'wall_time_seconds': v.get('wall_time_seconds'), 'cpu_time_seconds': cpu,
        'cpu_user_seconds': user, 'cpu_system_seconds': system, 'cpu_user_system_sum_seconds': summed,
        'peak_rss_bytes': v.get('peak_rss_bytes'), 'peak_pss_bytes': v.get('peak_pss_bytes'),
        'resource_source': v.get('source'), 'resource_degraded': v.get('degraded')}


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--packet', required=True, type=Path)
    p.add_argument('--ready', required=True, type=Path)
    p.add_argument('--journal', required=True, type=Path)
    p.add_argument('--evidence-list', type=Path, action='append', required=True)
    p.add_argument('--kernel-receipt', required=True, help='Unit-relative final successful retry receipt')
    p.add_argument('--production-receipt', required=True, help='Unit-relative successful production-gates receipt')
    p.add_argument('--plan', required=True, type=Path, help='Existing plan containing unchecked S2-04')
    p.add_argument('--out', required=True, type=Path, help='New directory outside the repository')
    p.add_argument('--write-registry', action='store_true', help='Install the validated candidate after local review')
    a = p.parse_args()
    require(not a.out.resolve().is_relative_to(ROOT.resolve()) and not a.out.exists(), 'Use a new external output directory')
    before_bytes = REGISTRY.read_bytes()
    before = json.loads(before_bytes)
    names = []
    for path in a.evidence_list:
        names += load_list(path)
    require(len(names) == len(set(names)), 'Duplicate evidence paths')
    files = {n: exact_path(UNIT, n) for n in names}
    # run_path loads the audited offline helpers without importing API code or producing pycache.
    delivery = runpy.run_path(str(UNIT / 'delivery.py'))
    packet = delivery['preflight'](a.packet, a.ready)
    ready = read(a.ready)
    records, by_job = [], {}
    # Do not omit a failed/retry result that appeared after the reviewed list was made.
    actual_results = {str(path.relative_to(UNIT)) for path in UNIT.rglob('*-result.json')
                      if path.is_file() and '__pycache__' not in path.parts}
    require(actual_results <= set(files), 'Add new result receipts to exact evidence list: ' + str(sorted(actual_results - set(files))))
    for name in sorted(files):
        if not name.endswith('-result.json'):
            continue
        receipt = read(files[name])
        if not {'job_id', 'request', 'status'} <= set(receipt):
            continue  # Platform publish receipts remain in the package; CI resources do not apply.
        require(isinstance(receipt['request'], dict), 'Malformed CI request in result: ' + name)
        row = resources(receipt, name)
        records.append(row)
        require(row['job_id'] not in by_job or by_job[row['job_id']]['receipt_sha256'] == row['receipt_sha256'],
                'Conflicting job receipts')
        by_job[row['job_id']] = row
    selected = {}
    for key, name, gates in [
        ('kernel_audit', a.kernel_receipt, ['wrapped_kernel_type_identity']),
        ('production_gates', a.production_receipt, ['checks_axioms', 'import_audit', 'act1scene1', 'axiom_audit'])]:
        require(name in files, 'Selected final receipt is not allowlisted: ' + name)
        receipt = read(files[name])
        require(receipt['status'] == 'succeeded' and receipt['result']['exit_code'] == 0,
                'Selected final receipt did not succeed: ' + name)
        for gate in gates:
            require(str(files[name].resolve()) in {str(Path(v).resolve()) for v in ready['ci_receipts'][gate]},
                    'Ready gate does not bind selected final receipt: ' + gate)
        selected[key] = {'job_id': receipt['job_id'], 'receipt': name, 'sha256': digest(files[name])}
    journal = a.journal.resolve()
    require(journal.is_relative_to(UNIT.resolve()), 'Journal must be in the current evidence unit')
    def journal_read(name):
        rel = (journal / name).relative_to(UNIT).as_posix()
        require(rel in files, 'Journal evidence not allowlisted: ' + rel)
        return read(files[rel])
    summary = journal_read('delivery-summary.json')
    ids = journal_read('published-ids.json')
    binding = journal_read('packet-binding.json')
    require(binding == {'packet_sha256': digest(a.packet), 'mission_id': delivery['MISSION'], 'names': NAMES}, 'Journal packet binding differs')
    require(set(ids) == set(NAMES) and len(set(ids.values())) == 5 and all(isinstance(v, str) and v for v in ids.values()), 'Expected five actual unique publication IDs')
    require(summary == {'published_ids': ids, 'definition_count': 5, 'verification_jobs': 0,
        'mission_id': delivery['MISSION'], 'root_id': delivery['ROOT'], 'environment': delivery['ENV'],
        'visibility': 'private', 'scope': delivery['SCOPE'], 'root_graph_membership': False,
        'canonicalC22Connected': False, 'root_graph_unchanged': True}, 'Delivery summary scope differs')
    graph_before, graph_after = [journal_read(n) for n in ['root-graph-before.json', 'root-graph-after.json']]
    require(graph_before == graph_after, 'Root graph changed')
    require(not set(ids.values()) & {value for n in graph_after.get('nodes', []) for value in [n.get('theorem_id'), n.get('node_id')]}, 'Detached Definition appears in root graph')
    for row in packet['publications']:
        tag, payload = row['tag'], row['payload']
        require(journal_read(tag + '-intent.json') == row, 'Changed durable publication intent')
        submitted, job, item = [journal_read(tag + suffix) for suffix in ['-submit.json', '-result.json', '-published-item.json']]
        require(submitted.get('job_id') == job['id'] and not submitted.get('errors') and
                job['status'] == 'PUBLISHED' and job['theorem_id'] == ids[tag], 'Publication job is not accepted')
        delivery['check_job'](job, row)
        require(item['definition_id'] == ids[tag] and item['visibility'] == 'private' and item['mathlib_rev'] == delivery['ENV'], 'Published item scope differs')
        require(all(item[k] == payload[k] for k in ['definition_name', 'definition_title', 'definition', 'natural_language_statement', 'source']), 'Published item differs from exact payload')
    plan_bytes = a.plan.read_bytes()
    import re
    lines = [line for line in plan_bytes.decode().splitlines() if 'S2-04' in line]
    require(any(re.search(r'-\s*\[ \].*S2-04', line) for line in lines) and
            not any(re.search(r'-\s*\[[xX]\].*S2-04', line) for line in lines), 'S2-04 is not unchecked')
    after = copy.deepcopy(before)
    preparation = after['reference_source_preparation']
    require(preparation['canonicalC22Connected'] is False and preparation['scope'] == delivery['SCOPE'], 'Registry preparation scope differs')
    require('packet_field_unit' in preparation, 'Prior packet-field unit is missing')
    require('volume_tate_unit' not in preparation, 'Current unit already recorded; review instead of overwriting')
    require(not set(NAMES) & {r['name'] for r in preparation['definitions']}, 'Definition names already recorded')
    require(not set(ids.values()) & {r['id'] for r in preparation['definitions']}, 'Definition IDs already recorded')
    preparation['definitions'].extend({'name': n, 'id': ids[n], 'status': 'PUBLISHED', 'visibility': 'private',
        'source_unit': str(UNIT.relative_to(WORKSPACE)), 'root_graph_membership': False} for n in NAMES)
    preparation['volume_tate_unit'] = {'source_unit': str(UNIT.relative_to(WORKSPACE)), 'definitions': ids,
        'packet_sha256': digest(a.packet), 'ready_sha256': digest(a.ready), 'selected_final_ci': selected,
        'canonicalC22Connected': False, 'root_graph_unchanged': True, 'root_graph_membership': False,
        'paper_identity_and_arithmetic_instantiation_completed': False,
        'S2-04_completed': False}
    # Equality check proves every other registry field is unchanged.
    stripped = copy.deepcopy(after)
    stripped['reference_source_preparation']['definitions'] = before['reference_source_preparation']['definitions']
    del stripped['reference_source_preparation']['volume_tate_unit']
    require(stripped == before, 'Registry update escaped the allowed scope')
    a.out.mkdir(parents=True)
    write_new(a.out / 'platform-node-registry.candidate.json', after)
    write_new(a.out / 'finalization-summary.json', {'schema': 'reference-volume-tate-finalization-v3',
        'actual_delivery_validated': True, 'published_ids': ids, 'selected_final_ci': selected,
        'ci_attempts': records, 'registry_before_sha256': __import__('hashlib').sha256(before_bytes).hexdigest(),
        'root_graph_unchanged': True, 'S2-04_completed': False,
        'plan': str(a.plan.resolve()), 'plan_sha256': digest(a.plan),
        'source_sha256': {n: digest(ROOT / n) for n in DEFINITIONS}})
    write_new(a.out / 'registry-update-scope.json', {'changed_fields': [
        'reference_source_preparation.definitions (append five records)',
        'reference_source_preparation.volume_tate_unit (new)'],
        'root_graph_unchanged': True, 'obligations_closed': 0, 'main_docs_changed': False})
    require(a.plan.read_bytes() == plan_bytes and REGISTRY.read_bytes() == before_bytes, 'Inputs changed during finalization')
    if a.write_registry:
        # No other input, document, database or registry field is touched.
        with REGISTRY.open('wb') as f:
            f.write((a.out / 'platform-node-registry.candidate.json').read_bytes())
    print('Validated real delivery; registry', 'installed' if a.write_registry else 'candidate only', a.out)


if __name__ == '__main__':
    main()
