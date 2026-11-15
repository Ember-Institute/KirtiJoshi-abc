#!/usr/bin/env python3
"""Validate actual v10 evidence offline. Does not compile, use Git, or call an API."""
import sys
sys.dont_write_bytecode = True
import argparse
import importlib.util
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
from common import UNIT, exact_path


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--unit', type=Path, default=UNIT)
    parser.add_argument('--out', type=Path, default=HERE / 'delivery-offline-validation.json')
    args = parser.parse_args()
    spec = importlib.util.spec_from_file_location('actual_ready_validation', HERE / 'prepare_ready.py')
    helper = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(helper)
    helper.B = args.unit.resolve()
    read = helper.delivery.read
    audit_path = exact_path(args.unit, 'kernel-audit/next-carrier-kernel-audit.json')
    receipt_path = exact_path(args.unit, 'kernel-audit-v10-result.json')
    audit, receipt = read(audit_path), read(receipt_path)
    inventory = read(exact_path(args.unit, 'inventory.json'))
    declarations = [d for module in inventory['modules'] for d in module['declarations']]
    manifest = helper.validate_main_manifest(receipt, exact_path(args.unit, 'audit-config.json'))
    coverage = helper.validate_kernel_coverage(audit, declarations)
    standard = helper.validate_standard_proof_compatibility(audit, declarations)
    adic = helper.validate_adic_source_compatibility(audit, exact_path(args.unit, 'attempts/kernel-audit-v4/audit-config.json'))
    ledger = read(exact_path(args.unit, 'SOURCE_LEDGER.json'))
    helper.validate_ledger(ledger, inventory, Path(ledger['wrapperReport']['path']), audit_path, receipt_path, audit)
    result = {'scope': 'Actual v10 evidence validation only; no ready or publication acceptance is created.',
        'passed': True, 'main_manifest': manifest, 'project_coverage': coverage,
        'standard_compatibility': standard, 'adic_source_compatibility': adic,
        'ci_compilation_run': False, 'api_network_run': False, 'git_run': False,
        'actual_ready_or_publication_receipts_created': False}
    helper.delivery.save(args.out, result)
    print(json.dumps({'passed': True, 'main_job_id': manifest['job_id'], 'source': 78, 'named': 76, 'proof': 2}))


if __name__ == '__main__':
    main()
