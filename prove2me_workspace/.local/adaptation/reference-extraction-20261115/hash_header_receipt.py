#!/usr/bin/env python3
"""Attach SHA256 to the header-parser receipt; do not parse Lean source.

Usage: python3 hash_header_receipt.py REPORT OUT [LOCK_OR_CONFIG...]
Keep reference inputs stable from parsing through this command. Missing source
is retained as missing; a successful parser job alone does not prove closure.
"""
import hashlib
import json
import sys
from pathlib import Path


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def main():
    report_path, output = Path(sys.argv[1]), Path(sys.argv[2])
    report = json.loads(report_path.read_text())
    report["positionCoordinate"] = "normalized_input_utf8 (CRLF converted to LF by Lean.mkInputContext); never slice raw CRLF bytes using these offsets"
    for module in report["modules"]:
        if "source" not in module:
            continue
        source = Path(module["source"])
        data = source.read_bytes()
        if len(data) != module["parserInputUtf8ByteLength"]:
            raise ValueError("Source changed after header parsing: " + str(source))
        module["sourceSha256"] = hashlib.sha256(data).hexdigest()
        module["sourceBytes"] = len(data)
        normalized = data.replace(b"\r\n", b"\n")
        module["normalizedSourceSha256"] = hashlib.sha256(normalized).hexdigest()
        module["normalizedSourceBytes"] = len(normalized)
        module["rawOffsetsEqualParserOffsets"] = data == normalized
    auxiliary = list(dict.fromkeys([str(report_path), report["configPath"], *sys.argv[3:]]))
    report["auxiliaryInputs"] = [{"path": path, "sha256": sha(path)} for path in auxiliary]
    report["validationScope"] = "Lean parser header import closure and exact source hashes; no declaration elaboration or theorem verification"
    output.write_text(json.dumps(report, ensure_ascii=False, indent=2) + "\n")


if __name__ == "__main__":
    main()
