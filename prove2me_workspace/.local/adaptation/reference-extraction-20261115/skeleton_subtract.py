#!/usr/bin/env python3
"""Subtract only compiler-oracle ranges from their hashed normalized artifact.

Usage: python3 skeleton_subtract.py PLAN REFERENCE_ROOT OUTPUT_ROOT
Never apply normalized offsets to original raw source bytes. This stage
preserves original imports. Rewrite import AST ranges and validate
the exact platform text in a separate stage before treating output as staged.
"""
import json
import hashlib
import sys
from pathlib import Path


def main():
    plan = json.loads(Path(sys.argv[1]).read_text())
    for receipt in plan.get("validatedStage2Receipts", []):
        if hashlib.sha256(Path(receipt["path"]).read_bytes()).hexdigest() != receipt["sha256"]:
            raise ValueError("Validated Stage2 receipt changed after planning")
    if not plan.get("validatedStage2Receipts") or not plan.get("graphReceipt"):
        raise ValueError("Plan lacks mandatory bound compiler receipts")
    graph_receipt = plan["graphReceipt"]
    if hashlib.sha256(Path(graph_receipt["path"]).read_bytes()).hexdigest() != graph_receipt["sha256"]:
        raise ValueError("Graph receipt changed after planning")
    source_root, output_root = Path(sys.argv[2]).resolve(), Path(sys.argv[3]).resolve()
    if output_root == source_root or source_root in output_root.parents:
        raise ValueError("Output must be outside the reference input tree")
    for file, facts in plan["files"].items():
        if facts.get("offsetCoordinate") != "lean-normalized-utf8":
            raise ValueError("Refusing offsets without a normalized coordinate artifact: " + file)
        source, output = Path(facts["coordinateSource"]), output_root / file
        if not source.is_absolute() or not facts.get("normalizedSha256"):
            raise ValueError("Missing normalized source path/hash: " + file)
        data = source.read_bytes()
        if hashlib.sha256(data).hexdigest() != facts["normalizedSha256"]:
            raise ValueError("Normalized coordinate source hash differs: " + file)
        if len(data) != facts["byteLength"]:
            raise ValueError("Source length changed since extraction: " + file)
        spans = sorted((d["start"], d["end"]) for d in facts["declarations"] if not d["keep"])
        previous = 0
        for start, end in spans:
            if not (previous <= start <= end <= len(data)):
                raise ValueError("Overlapping or invalid oracle ranges: " + file)
            previous = end
        for start, end in reversed(spans):
            data = data[:start] + data[end:]
        output.parent.mkdir(parents=True, exist_ok=True)
        output.write_bytes(data)


if __name__ == "__main__":
    main()
