#!/usr/bin/env python3
"""Plan from compiler JSONL only; never infer a Lean declaration from source text.

Usage: python3 plan_reference.py GRAPH --graph-receipt GRAPH_RECEIPT --receipt STAGE2_RECEIPT... --out PLAN
This does not compile, alter Lean sources, publish, or contact an API.
"""
import argparse
import json
import hashlib
from collections import defaultdict
from pathlib import Path


def load_lines(path):
    return [json.loads(line) for line in Path(path).read_text().splitlines() if line.strip()]


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("graph")
    ap.add_argument("--receipt", action="append", required=True)
    ap.add_argument("--graph-receipt", required=True)
    ap.add_argument("--out", required=True)
    args = ap.parse_args()
    facts = load_lines(args.graph)
    manifest, = [f for f in facts if f.get("record") == "manifest"]
    rows = {f["name"]: f for f in facts if f.get("record") == "decl"}
    if len(rows) != sum(f.get("record") == "decl" for f in facts):
        raise ValueError("Duplicate Stage1 declaration names")
    roots = set(manifest["roots"])
    graph_receipt = json.loads(Path(args.graph_receipt).read_text())
    sha = lambda path: hashlib.sha256(Path(path).read_bytes()).hexdigest()
    if graph_receipt.get("graphSha256") != sha(args.graph):
        raise ValueError("Graph digest differs from explicit graph receipt")
    graph_sources = graph_receipt.get("sourceFiles", {})
    syntax = []
    source_receipts = {}
    validated_receipts = []
    for receipt_path in args.receipt:
        receipt = json.loads(Path(receipt_path).read_text())
        if receipt.get("receiptValidation") != "source-output-sha256-and-terminal-summaries-v1" or not receipt.get("complete"):
            raise ValueError("Require validated successful Stage2 receipt: " + receipt_path)
        if receipt.get("configSha256") != sha(receipt["configPath"]) or json.loads(Path(receipt["configPath"]).read_text()) != receipt["config"]:
            raise ValueError("Stage2 config differs from validated receipt: " + receipt_path)
        validated_receipts.append({"path": str(Path(receipt_path).resolve()), "sha256": sha(receipt_path)})
        for result in receipt["results"]:
            module = result["module"]
            if module in source_receipts:
                raise ValueError("Duplicate Stage2 module: " + module)
            if result["status"] != "success" or result["outputSha256"] != sha(result["output"]):
                raise ValueError("Stage2 JSONL hash/status mismatch: " + module)
            if result["rawSha256"] != sha(result["source"]) or result["normalizedSha256"] != sha(result["coordinateSource"]):
                raise ValueError("Stage2 source hash mismatch: " + module)
            if graph_sources.get(module) != {"rawSha256": result["rawSha256"], "normalizedSha256": result["normalizedSha256"]}:
                raise ValueError("Stage1/Stage2 source identities differ or lack binding: " + module)
            loaded = load_lines(result["output"])
            sources = [f for f in loaded if f["kind"] == "source"]
            if len(sources) != 1 or sources[0]["module"] != module or sources[0]["file"] != result["file"]:
                raise ValueError("Stage2 source identity mismatch: " + module)
            if sources[0].get("namePrefixes") != []:
                raise ValueError("Context planning requires unfiltered Stage2 constant refs: " + module)
            if not loaded or loaded[-1]["kind"] != "summary" or loaded[-1]["status"] != "success":
                raise ValueError("Stage2 terminal summary absent: " + module)
            for key, kind in [("declarationCount", "decl"), ("referenceCount", "ref")]:
                if sum(f["kind"] == kind for f in loaded) != result[key] or loaded[-1][key] != result[key]:
                    raise ValueError("Stage2 fact counts differ: " + module)
            source_receipts[module] = result
            syntax.extend(loaded)
    decls_by_file = defaultdict(list)
    files = {}
    commands_by_file, refs_by_file = defaultdict(list), defaultdict(list)
    for fact in syntax:
        if fact["kind"] == "source":
            file = fact["file"]
            # Run Stage 2 with source paths relative to the reference root.
            if Path(file).is_absolute():
                raise ValueError("Pass root-relative source paths to Stage 2: " + file)
            if fact.get("offsetCoordinate") != "lean-normalized-utf8":
                raise ValueError("Stage2 must identify its normalized coordinate artifact: " + file)
            if file in files:
                raise ValueError("Duplicate Stage2 source fact: " + file)
            result = source_receipts[fact["module"]]
            files[file] = {"byteLength": fact["byteLength"], "declarations": [],
                           "offsetCoordinate": fact["offsetCoordinate"],
                           "coordinateSource": fact["coordinateSource"],
                           "normalizedSha256": result["normalizedSha256"]}
        elif fact["kind"] == "decl":
            if fact.get("generationIssue"):
                raise ValueError("Unsupported atomic declaration command: " + fact["file"] + ": " + fact["generationIssue"])
            decls_by_file[fact["file"]].append(fact)
        elif fact["kind"] == "command":
            if fact["syntaxKind"] == "Lean.Parser.Command.mutual":
                raise ValueError("Mutual command unsupported for per-node generation: " + fact["file"])
            commands_by_file[fact["file"]].append(fact)
        elif fact["kind"] == "ref":
            refs_by_file[fact["file"]].append(fact)
    for module in manifest["participatingModules"]:
        file = module.replace(".", "/") + ".lean"
        if file not in files:
            raise ValueError("Missing Stage 2 extraction for participating module: " + file)

    def deps(name):
        row = rows[name]
        return set(row["typeDeps"] + row["valueDeps"] + row["constructors"])

    def closure(seed):
        reached, work = set(), list(seed)
        while work:
            name = work.pop()
            if name in reached:
                continue
            if name not in rows:
                raise ValueError("Incomplete compiler graph, missing project constant: " + name)
            reached.add(name)
            work.extend(deps(name) - reached)
        return reached

    # This small planner supports only structural contexts and variable
    # declarations. Attribute/export/open/notation/macro or unknown commands
    # need a separately audited environment-difference extractor. Empty refs
    # never authorize those commands. Reject rather than guess dependencies.
    safe_context = {"Lean.Parser.Command.namespace", "Lean.Parser.Command.section",
                    "Lean.Parser.Command.end", "Lean.Parser.Command.variable",
                    "Lean.Parser.Command.include", "Lean.Parser.Command.omit",
                    "Lean.Parser.Command.moduleDoc", "Lean.Parser.Command.eoi"}
    context_roots = set()
    context_evidence = []
    for file, commands in commands_by_file.items():
        for command in commands:
            if command.get("generationIssue"):
                raise ValueError("Unsupported command: " + file + ": " + command["generationIssue"])
            if command["isDeclaration"]:
                continue
            kind = command["syntaxKind"]
            if kind not in safe_context:
                raise ValueError("Unaudited preserved context command: " + file + ": " + kind)
            span = command["range"]
            if span is None:
                if kind == "Lean.Parser.Command.eoi":
                    continue
                raise ValueError("Context command has no range: " + file)
            dependencies = {r["const"] for r in refs_by_file[file]
                            if span["start"]["offset"] <= r["start"]["offset"]
                            and r["end"]["offset"] <= span["end"]["offset"] and r["const"] in rows}
            context_roots |= dependencies
            context_evidence.append({"file": file, "syntaxKind": kind, "range": span,
                                     "projectDependencies": sorted(dependencies)})

    # Position joins use compiler selection coordinates, with the outer syntax
    # command as the subtraction unit. Private names do not need text matching.
    groups, group_members = {}, defaultdict(set)
    for name, row in rows.items():
        if row["startLine"] == 0:
            continue
        point = (row.get("selectionRange") or row["range"])["start"]
        point = point["line"], point["col"]
        matches = [f for f in decls_by_file[row["sourceFile"]]
                   if (f["declStart"]["line"], f["declStart"]["col"]) <= point
                   < (f["declEnd"]["line"], f["declEnd"]["col"])]
        if len(matches) > 1:
            raise ValueError("Ambiguous compiler/syntax join: " + name)
        if not matches:
            raise ValueError("Unexplained nonzero-span compiler declaration; context provenance unsupported: " + name)
        if matches:
            fact = matches[0]
            key = row["sourceFile"], fact["declStart"]["offset"], fact["declEnd"]["offset"]
            groups[name] = (key, fact)
            group_members[key].add(name)

    target_closure = closure(roots)
    instances = {n for n, r in rows.items() if r["isInstance"]}
    reached = closure(roots | instances | context_roots)
    atomic_companions = set()
    while True:
        # A mutual block, structure, and its projections remain one source command.
        companions = set().union(*(group_members[groups[n][0]]
                                   for n in reached if n in groups)) if reached else set()
        extra = companions - reached
        if not extra:
            break
        atomic_companions |= extra
        reached |= closure(extra)

    consumers = defaultdict(list)
    for consumer in sorted(reached):
        row = rows[consumer]
        for field, edge in [("typeDeps", "type"), ("valueDeps", "value"),
                            ("constructors", "constructor")]:
            for producer in row[field]:
                if producer in reached:
                    consumers[producer].append({"declaration": consumer, "edge": edge})

    source_names = {n for n in reached if n in groups}
    # A source structure supplies its projection theorems and constructors.
    provided = set()
    for name in source_names:
        row = rows[name]
        key, _ = groups[name]
        if row["kind"] in {"ctor", "rec"}:
            provided.add(name)
        elif row["kind"] == "theorem" and any(
                rows[m]["kind"] == "inductive" for m in group_members[key]):
            provided.add(name)

    definitions = {n for n in source_names - provided if rows[n]["kind"] != "theorem"}
    # Preserved supported contexts must remain proved. Context generators are
    # rejected above, so no notation-generated Def seed is silently omitted.
    definitions |= context_roots
    # All theorem material required by definitions must remain proved in bundles.
    def_closure = closure(definitions) if definitions else set()
    embedded = {n for n in def_closure & source_names if rows[n]["kind"] == "theorem"} - provided
    if embedded & roots:
        raise ValueError("Target required inside proved context/Def bundle; node split needs explicit review")
    statement_required = set()
    for n in reached:
        statement_required |= closure(rows[n]["typeDeps"])

    proof_lines = {}
    for n in source_names:
        _, fact = groups[n]
        proof_lines[n] = (fact["declEnd"]["line"] - fact["valStart"]["line"]
                          if fact["valStart"] else 0)
    candidates = {n for n in source_names - embedded - provided if rows[n]["kind"] == "theorem"}
    nodes = (roots & candidates) | {n for n in candidates if not rows[n]["isPrivate"]
                                   and (proof_lines[n] > 40 or n in statement_required)}
    paper_named = set()  # Add only explicit, reviewed SOURCE_LEDGER annotations.
    proof_consumers = defaultdict(set)
    while True:
        proof_consumers = defaultdict(set)
        for node in nodes:
            work, seen = list(rows[node]["valueDeps"]), set()
            while work:
                n = work.pop()
                if n in seen:
                    continue
                seen.add(n)
                proof_consumers[n].add(node)
                if n not in nodes:
                    work.extend(deps(n) - seen)
        promote = set()
        for n in candidates - nodes:
            row, fact = rows[n], groups[n][1]
            cross_file = any(rows[c["declaration"]]["module"] != row["module"]
                             for c in consumers[n])
            signal = len(proof_consumers[n]) >= 2 or cross_file or bool(fact["docstring"]) or n in paper_named
            must_export = n in statement_required
            if (not row["isPrivate"] or must_export) and (
                    must_export or (11 <= proof_lines[n] <= 40 and signal)):
                promote.add(n)
        if not promote:
            break
        nodes |= promote

    plan_rows = []
    for name in sorted(reached):
        row = rows[name]
        if row["startLine"] == 0:
            classification = "compiler-companion"
        elif name not in groups:
            raise ValueError("Unexplained source declaration: " + name)
        elif name in provided:
            classification = "provided-by-command"
        elif name in embedded:
            classification = "def-embedded-theorem"
        elif name in nodes:
            classification = "node"
        elif row["kind"] == "theorem":
            classification = "inline-helper"
        else:
            classification = "def-material"
        need_public = row["isPrivate"] and (name in statement_required or name in def_closure)
        plan_rows.append({"name": name, "module": row["module"], "class": classification,
            "consumers": consumers[name], "proofConsumers": sorted(proof_consumers[name]),
            "explicitTarget": name in roots, "targetClosure": name in target_closure,
            "instanceContextRoot": name in instances, "retainedContextRoot": name in context_roots,
            "atomicCompanion": name in atomic_companions,
            "statementRequired": name in statement_required, "deprivatize": need_public,
            "proofLines": proof_lines.get(name), "axioms": row["axioms"],
            "unexpectedAxioms": [a for a in row["axioms"]
                                  if a not in {"propext", "Classical.choice", "Quot.sound"}],
            "command": list(groups[name][0]) if name in groups else None})

    keep = {groups[n][0] for n in reached if n in groups}
    for file, facts_in_file in decls_by_file.items():
        for fact in facts_in_file:
            start, end = fact["declStart"]["offset"], fact["declEnd"]["offset"]
            files[file]["declarations"].append({"start": start, "end": end,
                "keep": (file, start, end) in keep})
    if nodes & def_closure:
        raise ValueError("A retained Def/context proof path crosses a theorem stub")
    out = {"validatedStage2Receipts": validated_receipts,
           "graphReceipt": {"path": str(Path(args.graph_receipt).resolve()), "sha256": sha(args.graph_receipt)},
           "contextDependencies": context_evidence,
           "defProofClosure": sorted(def_closure),
           "schema": "reference-plan-v1", "roots": sorted(roots),
           "participatingModules": manifest["participatingModules"],
           "discardedUnreachableCount": len(rows) - len(reached),
           "declarations": plan_rows, "files": files,
           "status": "draft-plan-requires-compiled-extraction-and-exact-text-validation"}
    Path(args.out).write_text(json.dumps(out, ensure_ascii=False, indent=2) + "\n")


if __name__ == "__main__":
    main()
