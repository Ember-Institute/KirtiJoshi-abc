#!/usr/bin/env python3
import argparse
import hashlib
import json
import subprocess
from pathlib import Path


REPO = Path("/home/admin-wsl/Coq/abc")
WORKSPACE = REPO / "prove2me_workspace"
UNIT = WORKSPACE / ".local/adaptation/b1-tripod-height-correspondence-20261121/curve-input-assembly"
REFERENCE = REPO / "refer/iut"
OVERLAY = UNIT / "real-source-project"
REFERENCE_FACTS = UNIT / "real-source-facts.json"
TARGET_FACTS = UNIT / "target-from-real-source-facts.json"


def git(*args):
    return subprocess.check_output(("git", "-C", str(REPO), *args)).decode(
        errors="surrogateescape"
    )


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read_json(path):
    return json.loads(path.read_text())


def refresh_worktree(manifest, source, facts_inputs):
    modified = set()
    untracked = set()
    entries = iter(git("status", "--porcelain=v1", "-z", "--untracked-files=all").split("\0"))
    for entry in entries:
        if not entry:
            continue
        status, path = entry[:2], entry[3:]
        if status == "??":
            untracked.add(path)
        else:
            modified.add(path)
            if "R" in status or "C" in status:
                modified.add(next(entries))
    for path in (source, *facts_inputs):
        relative = str(path.relative_to(REPO))
        tracked = git("ls-files", "--", relative)
        if not tracked:
            untracked.add(relative)
    manifest.update({
        "worktree_id": str(REPO),
        "head": git("rev-parse", "HEAD").strip(),
        "modified_files": sorted(modified),
        "untracked_files": sorted(untracked),
        "source_sha256": digest(source),
    })


def reference_inputs(request, source):
    manifest = request["worktree_manifest"]
    del manifest["proof_input_receipt"]
    artifact_dir = OVERLAY / ".lake/build/lib/lean"
    plan = read_json(UNIT / "missing-reference-artifacts.json")
    artifacts = [
        artifact_dir / Path(*row["module"].split(".")).with_suffix(".olean")
        for row in plan
    ]
    original = REFERENCE / "Iut/Tripod/CurveFacts.lean"
    staged = OVERLAY / "Iut/Tripod/CurveFacts.lean"
    configuration = [OVERLAY / "lean-toolchain", REFERENCE / "lake-manifest.json",
                     REFERENCE / "lakefile.toml"]
    patches = sorted((UNIT / "reference-compatibility").glob("*.patch"))
    manifest["input_hashes"] = {
        str(path): digest(path)
        for path in (source, original, staged, *configuration, *artifacts, *patches)
    }
    manifest["original_source"] = str(original)
    manifest["original_source_sha256"] = manifest["input_hashes"][str(original)]
    manifest["required_artifacts"] = request["environment"]["LEAN_PATH"].split(":") + [
        str(path) for path in artifacts
    ]
    request["environment"]["TRIPOD_CURVE_INPUTS_FACTS"] = str(REFERENCE_FACTS)
    return [staged, configuration[0], *patches]


def target_inputs(request, source):
    facts = read_json(REFERENCE_FACTS)
    expected = {
        "schema": "tripod-curve-inputs/v1",
        "owner": "Iut.Tripod.CurveFacts",
        "compiler": "4.35.0-rc3",
        "constructor": "Iut.Tripod.curveInputs",
        "explicitSL2Supplier": False,
    }
    if any(facts.get(key) != value for key, value in expected.items()):
        raise ValueError(f"Expected the original CurveFacts evidence at {REFERENCE_FACTS}")
    manifest = request["worktree_manifest"]
    inputs = [WORKSPACE / name for name in manifest["input_hashes"]
              if not name.endswith("/source-replay-facts.json")]
    manifest["input_hashes"] = {str(path): digest(path) for path in (*inputs, source, REFERENCE_FACTS)}
    manifest["required_artifacts"].append(str(REFERENCE_FACTS))
    manifest["resource_estimate_basis"] = "ci-026600-5a180380: wall 127.57 s, peak RSS 8.10 GiB"
    request["environment"]["TRIPOD_CURVE_INPUTS_SOURCE_FACTS"] = str(REFERENCE_FACTS)
    request["environment"]["TRIPOD_CURVE_INPUTS_FACTS"] = str(TARGET_FACTS)
    return [REFERENCE_FACTS]


def render(role, session, agent):
    if role == "reference":
        receipt = UNIT / "reference-receipts/ci-026744-8bcc1160.result.json"
        source = UNIT / "QueryTripodCurveInputsSource.lean"
        inputs = reference_inputs
        duration, memory = "60s", "16GiB"
    else:
        receipt = UNIT / "ci-026600-5a180380.result.json"
        source = UNIT / "AuditTripodCurveInputsTarget.lean"
        inputs = target_inputs
        duration, memory = "150s", "9GiB"
    base = read_json(receipt)["request"]
    request = {key: base[key] for key in ("language", "project_id", "environment",
                                        "session_id", "agent_id", "worktree_manifest")}
    request.update({
        "workspace": str(WORKSPACE),
        "exclusive": True,
        "task_type": "review",
        "target": "file",
        "parameters": {"source": str(source.relative_to(WORKSPACE))},
        "expected_duration": duration,
        "expected_memory": memory,
        "session_id": session or request["session_id"],
        "agent_id": agent or request["agent_id"],
    })
    facts_inputs = inputs(request, source)
    refresh_worktree(request["worktree_manifest"], source, facts_inputs)
    encoded = json.dumps(request, ensure_ascii=True, sort_keys=True).encode()
    request["idempotency_key"] = f"tripod-curve-facts-{role}-{hashlib.sha256(encoded).hexdigest()[:24]}"
    return request


def main():
    parser = argparse.ArgumentParser(description="Render an MCP-CI review request for CurveFacts.")
    parser.add_argument("role", choices=("reference", "target"))
    parser.add_argument("--session-id")
    parser.add_argument("--agent-id")
    args = parser.parse_args()
    try:
        request = render(args.role, args.session_id, args.agent_id)
    except (OSError, ValueError) as error:
        parser.error(str(error))
    print(json.dumps(request, ensure_ascii=True, indent=2))


if __name__ == "__main__":
    main()
