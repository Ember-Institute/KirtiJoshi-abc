#!/usr/bin/env python3
"""Stage pinned reference modules and render one structured MCP-CI artifact request."""

import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess

REPO = Path("/home/admin-wsl/Coq/abc")
WORKSPACE = REPO / "prove2me_workspace"
UNIT = Path(".local/adaptation/b1-tripod-height-correspondence-20261121/curve-input-assembly")
DEFAULT_WORKDIR = UNIT / "real-source-project"
ARTIFACT_DIR = Path(".lake/build/lib/lean")
DRAFT = Path(__file__).resolve().parent
REFERENCE = REPO / "refer/iut"
GENL = Path("/home/admin-wsl/Coq/abc.old/refer/iut/.lake/packages/genl")


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def module_path(module, extension):
    return Path(*module.split(".")).with_suffix(extension)


def git(repo, *args):
    return subprocess.check_output(["git", "-C", str(repo), *args])


def stage_inputs(rows, directory):
    files = [(REFERENCE / "lean-toolchain", directory / "lean-toolchain")]
    for row in rows:
        relative = module_path(row["module"], ".lean")
        source = Path(row["source"])
        if sha256(source) != row["source_sha256"]:
            raise ValueError(f"Pinned source changed at {source}")
        files.append((source, directory / relative))
        (directory / ARTIFACT_DIR / relative.parent).mkdir(parents=True, exist_ok=True)
    for source, destination in files:
        contents = source.read_bytes()
        destination.parent.mkdir(parents=True, exist_ok=True)
        if not destination.exists():
            destination.write_bytes(contents)
        elif destination.read_bytes() != contents:
            raise ValueError(f"Different source already staged at {destination}")


def stage_cached_namespaces(directory, receipt):
    # Lean chooses the first search root containing the namespace directory.
    # Populate both namespace trees before the first job reads the overlay.
    output_root = directory / ARTIFACT_DIR
    roots = map(Path, receipt["request"]["environment"]["LEAN_PATH"].split(os.pathsep))
    for root in roots:
        for namespace in ("Iut", "Genl"):
            for artifact in sorted((root / namespace).rglob("*")):
                if artifact.is_file():
                    destination = output_root / artifact.relative_to(root)
                    destination.parent.mkdir(parents=True, exist_ok=True)
                    if not destination.exists():
                        destination.symlink_to(artifact.resolve())


def worktree_manifest():
    modified, untracked = set(), set()
    entries = iter(git(REPO, "status", "--porcelain=v1", "-z", "--untracked-files=all")
                   .decode(errors="surrogateescape").split("\0"))
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
    return {
        "worktree_id": str(REPO),
        "head": git(REPO, "rev-parse", "HEAD").decode().strip(),
        "modified_files": sorted(modified),
        "untracked_files": sorted(untracked),
    }


def render_request(rows, receipt, args):
    directory = (WORKSPACE / args.working_directory).resolve()
    workdir = directory.relative_to(WORKSPACE)
    output_root = directory / ARTIFACT_DIR
    pending = [row for row in rows
               if not (output_root / module_path(row["module"], ".olean")).is_file()]
    if args.module:
        selected = next((row for row in pending if row["module"] == args.module), None)
        if selected is None:
            raise ValueError(f"Module is outside the plan or its artifact exists: {args.module}")
    elif pending:
        selected = pending[0]
    else:
        raise ValueError("All 31 reference artifacts are present")

    module = selected["module"]
    source = module_path(module, ".lean")
    output = ARTIFACT_DIR / module_path(module, ".olean")
    if sha256(directory / source) != selected["source_sha256"]:
        raise ValueError(f"Staged source changed at {directory / source}")

    env = receipt["request"]["environment"]
    source_env = receipt["request"]["worktree_manifest"]
    toolchain = (REFERENCE / "lean-toolchain").read_text().strip()
    if (directory / "lean-toolchain").read_text().strip() != toolchain:
        raise ValueError(f"Staged toolchain differs from {REFERENCE / 'lean-toolchain'}")
    if toolchain != source_env["effective_compiler"]:
        raise ValueError("Reference toolchain differs from the source replay receipt")

    iut_lock = REFERENCE / "lake-manifest.json"
    if sha256(iut_lock) != source_env["dependency_lock_sha256"]:
        raise ValueError(f"Reference lock changed at {iut_lock}")
    iut_packages = json.loads(iut_lock.read_text())["packages"]
    genl_revision = next(package["rev"] for package in iut_packages if package["name"] == "genl")
    if git(GENL, "rev-parse", "HEAD").decode().strip() != genl_revision:
        raise ValueError(f"Genl checkout differs from {genl_revision}")

    cache_roots = [Path(root) for root in env["LEAN_PATH"].split(":")
                   if "b1-source-replay-v104-20261117" not in root and Path(root).is_dir()]
    lean_olean = next(root / "Lean.olean" for root in cache_roots if (root / "Lean.olean").is_file())
    with lean_olean.open("rb") as handle:
        expected_header = handle.read(80)
    artifact_paths = [Path(path) for path in selected["existing_imports"].values()]
    artifact_paths.extend(output_root / module_path(dep, ".olean")
                          for dep in selected["missing_imports"])
    for artifact in artifact_paths:
        with artifact.open("rb") as handle:
            if handle.read(80) != expected_header:
                raise ValueError(f"Incompatible source Lean artifact at {artifact}")

    overlay_imports = [output_root / module_path(name, ".olean")
                       for name in selected["existing_imports"]
                       if name.split(".", 1)[0] in ("Iut", "Genl")]
    input_paths = [directory / source, directory / "lean-toolchain", iut_lock,
                   REFERENCE / "lakefile.toml", lean_olean, *artifact_paths, *overlay_imports]
    manifest = worktree_manifest()
    manifest["untracked_files"] = sorted(set(manifest["untracked_files"]) | {
        str((directory / source).relative_to(REPO)),
        str((directory / "lean-toolchain").relative_to(REPO)),
    })
    manifest.update({
        "toolchain": toolchain,
        "dependency_lock": str(iut_lock),
        "dependency_lock_sha256": source_env["dependency_lock_sha256"],
        "external_dependencies": source_env["external_dependencies"] + [
            {"path": str(GENL), "revision": genl_revision},
        ],
        "source_mathlib_dependency": source_env["source_mathlib_dependency"],
        "original_source": selected["source"],
        "source_sha256": selected["source_sha256"],
        "required_artifacts": [str(path) for path in [output_root, *cache_roots, *artifact_paths]],
        "input_hashes": {str(path): sha256(path) for path in input_paths},
    })
    request = {
        "language": "lean",
        "project_id": receipt["request"]["project_id"],
        "workspace": str(WORKSPACE),
        "exclusive": True,
        "working_directory": str(workdir),
        "task_type": "full",
        "target": "module",
        "parameters": {"args": [str(source), "-o", str(output)]},
        "environment": {
            "PATH": env["PATH"],
            "LEAN_PATH": os.pathsep.join(str(path) for path in [output_root, *cache_roots]),
        },
        "expected_duration": args.duration,
        "expected_memory": args.memory,
        "session_id": args.session_id,
        "agent_id": args.agent_id,
        "worktree_manifest": manifest,
    }
    digest = hashlib.sha256(json.dumps(request, sort_keys=True).encode()).hexdigest()[:20]
    request["idempotency_key"] = f"reference-build-{module}-{digest}"
    return request


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--stage-inputs", type=Path, metavar="DIRECTORY",
                        help="Copy the pinned source inputs into an independent directory")
    parser.add_argument("--working-directory", type=Path, default=DEFAULT_WORKDIR)
    parser.add_argument("--module",
                        help="Module to build. Defaults to the first missing module in dependency order")
    parser.add_argument("--session-id", default=os.environ.get("CODEX_SESSION_ID"))
    parser.add_argument("--agent-id", default="/root")
    parser.add_argument("--duration", default="60s")
    parser.add_argument("--memory", default="16GiB")
    args = parser.parse_args()
    rows = json.loads((DRAFT / "missing-reference-artifacts.json").read_text())
    try:
        receipt = json.loads((WORKSPACE / UNIT / "ci-026542-7fccbe6b.result.json").read_text())
        if args.stage_inputs:
            stage_inputs(rows, args.stage_inputs)
            stage_cached_namespaces(args.stage_inputs, receipt)
        else:
            if not args.session_id:
                parser.error("Supply the actual session with --session-id")
            print(json.dumps(render_request(rows, receipt, args), indent=2, ensure_ascii=False))
    except (OSError, ValueError) as error:
        parser.error(str(error))


if __name__ == "__main__":
    main()
