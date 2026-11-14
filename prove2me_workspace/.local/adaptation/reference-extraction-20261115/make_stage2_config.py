#!/usr/bin/env python3
"""Select source files from the accepted compiler-header graph, not source text.

Usage: python3 make_stage2_config.py HEADER_JSON CONFIG_DIR OUTPUT_DIR
       --group canonical-c22 --prefix Iut --prefix Genl --prefix TateCurvesTheta
       [--chunk-size N] [--source-overrides MODULE_TO_ABSOLUTE_PATH_JSON]
N=0 (default) makes one full batch; N>0 makes dependency-first smaller batches.
"""
import argparse
import hashlib
import json
from pathlib import Path


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("header")
    ap.add_argument("config_dir")
    ap.add_argument("output_dir")
    ap.add_argument("--group", default="canonical-c22")
    ap.add_argument("--prefix", action="append", required=True)
    ap.add_argument("--chunk-size", type=int, default=0)
    ap.add_argument("--source-overrides", help="JSON object mapping exact module names to actual patched source paths")
    args = ap.parse_args()
    if args.chunk_size < 0:
        ap.error("chunk-size must be nonnegative")
    header_path = Path(args.header).resolve()
    report = json.loads(header_path.read_text())
    group, = [g for g in report["groups"] if g["name"] == args.group]
    if group["missing"] or group["headerErrors"]:
        raise ValueError("Selected header closure is incomplete")
    rows = {r["module"]: r for r in report["modules"]}
    selected = {n for n in group["modules"]
                if any(n == p or n.startswith(p + ".") for p in args.prefix)}
    if not selected:
        raise ValueError("No source modules selected")
    overrides = json.loads(Path(args.source_overrides).read_text()) if args.source_overrides else {}
    unknown = set(overrides) - selected
    if unknown:
        raise ValueError("Source override outside selected closure: " + ", ".join(sorted(unknown)))
    ordered, seen, visiting = [], set(), set()

    def visit(name):
        if name in seen:
            return
        if name in visiting:
            raise ValueError("Import cycle in header graph: " + name)
        visiting.add(name)
        row = rows[name]
        if row["status"] != "parsed":
            raise ValueError("Source header not parsed: " + name)
        for dependency in row["imports"]:
            if dependency in selected:
                visit(dependency)
        visiting.remove(name)
        seen.add(name)
        ordered.append(name)

    for name in sorted(selected):
        visit(name)
    files = []
    for name in ordered:
        row = rows[name]
        source = Path(overrides.get(name, row["source"]))
        if not source.is_absolute():
            raise ValueError("Actual source override must be absolute: " + name)
        data = source.read_bytes()
        data.decode("utf-8")  # The Lean parser reads UTF-8 strings.
        normalized = data.replace(b"\r\n", b"\n")
        # Phase0's parser offsets can already refer to normalized input, so
        # never compare its offset length with raw file length as identity.
        files.append({"module": name, "source": str(source), "file": row["relativePath"],
                      "headerSource": row["source"], "sourceOverridden": name in overrides,
                      "sourceSha256": hashlib.sha256(data).hexdigest(), "rawByteLength": len(data),
                      "normalizedSha256": hashlib.sha256(normalized).hexdigest(),
                      "byteLength": len(normalized), "offsetCoordinate": "lean-normalized-utf8"})
    config_dir, output_dir = Path(args.config_dir).resolve(), Path(args.output_dir).resolve()
    config_dir.mkdir(parents=True, exist_ok=True)
    size = args.chunk_size or len(files)
    batches = []
    for number, start in enumerate(range(0, len(files), size), 1):
        batch = files[start:start + size]
        label = f"stage2-batch-{number:03d}"
        config = {"files": batch, "outputDir": str(output_dir / label),
                  "namePrefixes": [], "options": [], "failFast": True,
                  "sourceHeaderReceipt": str(header_path),
                  "sourceHeaderReceiptSha256": hashlib.sha256(header_path.read_bytes()).hexdigest(),
                  "selectedGroup": args.group, "selectedModulePrefixes": args.prefix}
        if args.source_overrides:
            config["sourceOverrides"] = str(Path(args.source_overrides).resolve())
            config["sourceOverridesSha256"] = hashlib.sha256(Path(args.source_overrides).read_bytes()).hexdigest()
        path = config_dir / (label + ".json")
        path.write_text(json.dumps(config, ensure_ascii=False, indent=2) + "\n")
        batches.append({"config": str(path), "files": len(batch),
                        "modules": [entry["module"] for entry in batch]})
    manifest = {"group": args.group, "moduleCount": len(files), "batches": batches}
    (config_dir / "batches.json").write_text(json.dumps(manifest, ensure_ascii=False, indent=2) + "\n")
    print(json.dumps({"moduleCount": len(files), "batchCount": len(batches),
                      "manifest": str(config_dir / "batches.json")}, ensure_ascii=False))


if __name__ == "__main__":
    main()
