#!/usr/bin/env python3
"""Validate a successful batch index and hash its exact sources and outputs.

Usage: python3 hash_stage2_receipts.py INDEX_JSON OUT_JSON
This reads compiler facts; it does not infer declarations or references.
"""
import hashlib
import json
import sys
from pathlib import Path


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def main():
    index_path, output = Path(sys.argv[1]), Path(sys.argv[2])
    index = json.loads(index_path.read_text())
    if json.loads(Path(index["configPath"]).read_text()) != index["config"]:
        raise ValueError("Config changed after Stage2 recorded its input")
    if not index["complete"] or index["finishedFiles"] != index["requestedFiles"]:
        raise ValueError("Stage2 batch is incomplete")
    configured = {r["module"]: r for r in index["config"]["files"]}
    for result in index["results"]:
        if result["status"] != "success":
            raise ValueError("Stage2 batch contains a failed file")
        expected = configured[result["module"]]
        source_hash = digest(result["source"])
        if expected.get("sourceSha256") and expected["sourceSha256"] != source_hash:
            raise ValueError("Source SHA256 changed since configuration: " + result["source"])
        if result.get("offsetCoordinate") != "lean-normalized-utf8":
            raise ValueError("Unknown or missing offset coordinate: " + result["module"])
        raw = Path(result["source"]).read_bytes()
        normalized = Path(result["coordinateSource"]).read_bytes()
        if normalized != raw.replace(b"\r\n", b"\n"):
            raise ValueError("Normalized artifact differs from String.crlfToLf input: " + result["module"])
        normalized.decode("utf-8")
        normalized_hash = hashlib.sha256(normalized).hexdigest()
        if expected.get("normalizedSha256") and expected["normalizedSha256"] != normalized_hash:
            raise ValueError("Normalized SHA256 differs from configuration: " + result["module"])
        if len(normalized) != result["byteLength"] or len(raw) != result["rawByteLength"]:
            raise ValueError("Raw/normalized byte length mismatch: " + result["module"])

        def validate_ranges(value):
            if isinstance(value, dict):
                if "offset" in value:
                    offset = value["offset"]
                    if not isinstance(offset, int) or not 0 <= offset <= len(normalized):
                        raise ValueError("Offset outside normalized input: " + result["module"])
                    if offset < len(normalized) and 0x80 <= normalized[offset] < 0xC0:
                        raise ValueError("Offset splits a UTF-8 code point: " + result["module"])
                for child in value.values():
                    validate_ranges(child)
            elif isinstance(value, list):
                for child in value:
                    validate_ranges(child)
        counts = {"decl": 0, "ref": 0}
        first, last = None, None
        with Path(result["output"]).open() as handle:
            for line in handle:
                fact = json.loads(line)
                first = first or fact
                last = fact
                validate_ranges(fact)
                if fact["kind"] in counts:
                    counts[fact["kind"]] += 1
        if not first or first["kind"] != "source" or first["module"] != result["module"]:
            raise ValueError("Missing or mismatched source fact: " + result["output"])
        if (first.get("offsetCoordinate") != "lean-normalized-utf8"
                or first.get("coordinateSource") != result["coordinateSource"]
                or first["byteLength"] != len(normalized)
                or first.get("rawByteLength") != len(raw)):
            raise ValueError("Source coordinate metadata mismatch: " + result["output"])
        if first.get("rawSha256Expected") not in (None, source_hash):
            raise ValueError("Source fact raw SHA256 mismatch: " + result["output"])
        if first.get("normalizedSha256Expected") not in (None, normalized_hash):
            raise ValueError("Source fact normalized SHA256 mismatch: " + result["output"])
        if not last or last["kind"] != "summary" or last["status"] != "success":
            raise ValueError("Missing terminal success summary: " + result["output"])
        for key, kind in [("declarationCount", "decl"), ("referenceCount", "ref")]:
            if counts[kind] != result[key] or counts[kind] != last[key]:
                raise ValueError("Fact count mismatch: " + result["output"])
        result["sourceSha256"] = source_hash
        result["rawSha256"] = source_hash
        result["normalizedSha256"] = normalized_hash
        result["outputSha256"] = digest(result["output"])
        result["diagnosticsSha256"] = digest(result["diagnostics"])
    index["indexInputSha256"] = digest(index_path)
    index["configSha256"] = digest(index["configPath"])
    index["receiptValidation"] = "source-output-sha256-and-terminal-summaries-v1"
    index["validationScope"] = "InfoTree syntax extraction, exact source/output hashes, terminal per-file summaries; no proof transplant acceptance"
    output.write_text(json.dumps(index, ensure_ascii=False, indent=2) + "\n")


if __name__ == "__main__":
    main()
