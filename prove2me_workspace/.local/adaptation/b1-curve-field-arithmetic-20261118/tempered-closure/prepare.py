#!/usr/bin/env python3
"""Prepare the pinned tempered fundamental group source closure for MCP-CI."""

import argparse
from hashlib import sha256
from io import BytesIO
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import tarfile
from tempfile import TemporaryDirectory
from urllib.request import urlopen

TOOLCHAIN = "leanprover/lean4:v4.33.1"
MATHLIB_REVISION = "0df444a360eaa60ab8c11dca51a86af692955474"
SOURCES = {
    "Pi1": ("pi1", "ca7def953193f861a462aa0831eec8f0a31ff69f"),
    "TemperedFundamentalGroups": (
        "tempered-fundamental-groups",
        "2006651f52b70ea2fe3388238c7d9db14d21748f",
    ),
    "EllipticCurves": ("elliptic-curves", "bebec3fc9f2602e81c83e5236789572a541c85fb"),
}
ENTRIES = (
    "Pi1.Orbifold.Comparison",
    "TemperedFundamentalGroups.Setup.Orbifold",
    "TemperedFundamentalGroups.Orbicurve.Orbifold",
)
TARGET = "TemperedSourceClosure"
ARTIFACTS = (".olean", ".olean.server", ".olean.private", ".ir", ".ir.sig")
HEADER_TOKEN = re.compile(
    rb"\s+|--[^\n]*|/-|(?P<module>module)\b|prelude\b|"
    rb"(?:(?:public|private|meta)\s+)*import\s+(?:all\s+)?(?P<import>[^\s]+)"
)
BLOCK_TOKEN = re.compile(rb"/-|-/")
HERE = Path(__file__).resolve().parent


def git(directory, *args):
    return subprocess.check_output(
        ["git", "-c", f"safe.directory={directory.resolve()}", "-c", "core.autocrlf=false",
         "-C", str(directory), *args],
        text=True,
    ).strip()


def write_json(path, data, *, sort_keys=True):
    path.write_text(json.dumps(data, indent=2, sort_keys=sort_keys) + "\n")


def file_hash(path):
    return sha256(path.read_bytes()).hexdigest()


def read_header(data):
    """Read import clauses and skip line comments and nested block comments."""
    modular = False
    imports = []
    offset = 0
    while token := HEADER_TOKEN.match(data, offset):
        offset = token.end()
        if token.group() == b"/-":
            depth = 1
            for delimiter in BLOCK_TOKEN.finditer(data, offset):
                depth += 1 if delimiter.group() == b"/-" else -1
                if depth == 0:
                    offset = delimiter.end()
                    break
            if depth:
                raise ValueError("Unclosed Lean header comment")
        if token.group("module"):
            modular = True
        if imported := token.group("import"):
            imports.append(imported.decode())
    return modular, imports


def stage_sources(workspace):
    modules = {}
    source_pins = {}
    licenses = workspace / "LICENSES"
    licenses.mkdir()
    for namespace, (repository, revision) in SOURCES.items():
        root = f"{repository}-{revision}/"
        url = f"https://codeload.github.com/lana-agents/{repository}/tar.gz/{revision}"
        with urlopen(url, timeout=60) as response:
            compressed = response.read()
        with tarfile.open(fileobj=BytesIO(compressed), mode="r:gz") as archive:
            source_toolchain = archive.extractfile(root + "lean-toolchain").read().decode().strip()
            license_path = root + "LICENSE"
            if license_path in archive.getnames():
                (licenses / f"{repository}.txt").write_bytes(
                    archive.extractfile(license_path).read()
                )
            for member in archive:
                if member.isfile() and member.name.startswith(root + namespace + "/"):
                    relative = Path(member.name.removeprefix(root))
                    if relative.suffix == ".lean":
                        module = ".".join(relative.with_suffix("").parts)
                        modules[module] = archive.extractfile(member).read()
        source_pins[namespace] = {
            "repository": f"https://github.com/lana-agents/{repository}",
            "revision": revision,
            "original_toolchain": source_toolchain,
        }

    pending = list(ENTRIES)
    local = {}
    external = set()
    while pending:
        module = pending.pop()
        if module in local or module in external:
            continue
        if module not in modules:
            if not module.startswith("Mathlib.") and module != "Mathlib":
                raise ValueError(f"Missing source for {module}")
            external.add(module)
            continue
        relative = Path(*module.split(".")).with_suffix(".lean")
        destination = workspace / relative
        destination.parent.mkdir(parents=True, exist_ok=True)
        data = modules[module]
        destination.write_bytes(data)
        _, imports = read_header(data)
        local[module] = {
            "file": relative.as_posix(),
            "upstream_sha256": sha256(data).hexdigest(),
            "imports": imports,
        }
        pending.extend(imports)
    if len(local) != 60:
        raise ValueError(f"Expected 60 local modules. Found {len(local)}.")

    patch = HERE / "lean433.patch"
    git(workspace, "apply", "--check", str(patch))
    git(workspace, "apply", str(patch))
    for row in local.values():
        staged = (workspace / row["file"]).read_bytes()
        if read_header(staged)[1] != row["imports"]:
            raise ValueError(f"The patch changes imports in {row['file']}")
        row["sha256"] = sha256(staged).hexdigest()
    return source_pins, local, sorted(external)


def lake_manifest(name, packages):
    return {
        "version": "1.3.0",
        "packagesDir": ".lake/packages",
        "packages": packages,
        "name": name,
        "lakeDir": ".lake",
        "fixedToolchain": True,
    }


def stage_mathlib(workspace, mathlib):
    if git(mathlib, "rev-parse", "HEAD") != MATHLIB_REVISION:
        raise ValueError(f"Use Mathlib revision {MATHLIB_REVISION}")
    if (mathlib / "lean-toolchain").read_text().strip() != TOOLCHAIN:
        raise ValueError(f"Use Mathlib with {TOOLCHAIN}")
    lock_path = mathlib / "lake-manifest.json"
    lock = json.loads(lock_path.read_text())
    if lock != json.loads(git(mathlib, "show", "HEAD:lake-manifest.json")):
        raise ValueError("Use the Mathlib dependency lock at the pinned revision")
    checkouts = {mathlib: MATHLIB_REVISION}
    for package in lock["packages"]:
        directory = mathlib / lock["packagesDir"] / package["name"]
        if git(directory, "rev-parse", "HEAD") != package["rev"]:
            raise ValueError(f"Use {directory.name} at revision {package['rev']}")
        checkouts[directory.resolve()] = package["rev"]

    wrapper = workspace / "prebuilt-mathlib"
    artifacts = wrapper / "artifacts"
    artifacts.mkdir(parents=True)
    (wrapper / "lakefile.toml").write_text(
        'name = "prebuilt_mathlib"\nbuildDir = "."\nleanLibDir = "artifacts"\n'
        "enableArtifactCache = false\n"
    )
    write_json(
        wrapper / "lake-manifest.json",
        lake_manifest("prebuilt_mathlib", []),
        sort_keys=False,
    )
    package = {
        "type": "path",
        "scope": "",
        "name": "prebuilt_mathlib",
        "manifestFile": "lake-manifest.json",
        "inherited": False,
        "dir": "prebuilt-mathlib",
        "configFile": "lakefile.toml",
    }
    write_json(
        workspace / "lake-manifest.json",
        lake_manifest("tempered_dependencies", [package]),
        sort_keys=False,
    )

    links = {}
    for checkout in checkouts:
        build_dir = checkout / ".lake/build/lib/lean"
        if not build_dir.is_dir():
            continue
        for artifact in sorted(build_dir.iterdir()):
            if artifact.is_dir() or artifact.name.endswith(ARTIFACTS):
                (artifacts / artifact.name).symlink_to(artifact)
                links[artifact.name] = str(artifact)
    write_json(wrapper / "ARTIFACT_LINKS.json", links)
    return checkouts, links


def check_artifacts(workspace, direct_imports, checkouts, toolchain):
    artifacts = workspace / "prebuilt-mathlib/artifacts"
    pending = list(direct_imports)
    visited = set()
    while pending:
        module = pending.pop()
        if module in visited:
            continue
        visited.add(module)
        relative = Path(*module.split("."))
        source_path = relative.with_suffix(".lean")
        lean_sources = toolchain / "src/lean"
        if module == "Lake" or module.startswith("Lake."):
            lean_sources /= "lake"
        core_source = lean_sources / source_path
        if core_source.is_file():
            source = core_source
            artifact_root = toolchain / "lib/lean"
        else:
            source = next(
                (checkout / source_path for checkout in checkouts
                 if (checkout / source_path).is_file()),
                None,
            )
            if source is None:
                raise ValueError(f"Missing source for dependency {module}")
            artifact_root = artifacts
        modular, imports = read_header(source.read_bytes())
        extensions = ARTIFACTS if modular and source != core_source else (".olean",)
        for extension in extensions:
            artifact = artifact_root / relative.with_suffix(extension)
            if not artifact.is_file():
                raise ValueError(f"Missing artifact for {module}: {artifact}")
        pending.extend(imports)
    return len(visited)


def prepare(workspace, args):
    # Keep Git's working tree at the exact staged bytes.
    git(workspace, "init", "--quiet")
    source_pins, local, external = stage_sources(workspace)
    checkouts, links = stage_mathlib(workspace, args.mathlib)
    dependencies_checked = check_artifacts(workspace, external, checkouts, args.toolchain)
    shutil.copyfile(HERE / "lakefile.lean.in", workspace / "lakefile.lean")
    shutil.copyfile(HERE / "lean433.patch", workspace / "lean433.patch")
    (workspace / ".gitignore").write_text(".lake/\n")
    (workspace / "lean-toolchain").write_text(TOOLCHAIN + "\n")
    (workspace / f"{TARGET}.lean").write_text(
        "".join(f"import {module}\n" for module in ENTRIES)
    )
    manifest = {
        "toolchain": TOOLCHAIN,
        "sources": source_pins,
        "entry_modules": ENTRIES,
        "modules": local,
        "direct_mathlib_imports": external,
        "dependency_modules_checked": dependencies_checked,
        "mathlib": {
            "path": str(args.mathlib),
            "revision": MATHLIB_REVISION,
            "lock_sha256": file_hash(args.mathlib / "lake-manifest.json"),
        },
        "patch_sha256": file_hash(workspace / "lean433.patch"),
    }
    write_json(workspace / "SOURCE_MANIFEST.json", manifest)
    git(workspace, "add", ".")
    git(workspace, "-c", "user.name=Tempered source closure", "-c",
        "user.email=tempered-source-closure@localhost",
        "-c", "commit.gpgSign=false", "commit", "--quiet", "-m",
        "Stage the pinned tempered fundamental group source closure")
    if git(workspace, "status", "--porcelain"):
        raise ValueError("The staged Git worktree has changes")
    head = git(workspace, "rev-parse", "HEAD")
    configs = [
        "lean-toolchain", "lakefile.lean", "lake-manifest.json", "SOURCE_MANIFEST.json",
        "lean433.patch", "prebuilt-mathlib/lakefile.toml",
        "prebuilt-mathlib/lake-manifest.json", "prebuilt-mathlib/ARTIFACT_LINKS.json",
    ]
    request = {
        "language": "lean",
        "task_type": "full",
        "project_id": TARGET,
        "workspace": str(args.workspace),
        "target": TARGET,
        "parameters": {},
        "environment": {
            "PATH": os.pathsep.join((str(args.toolchain / "bin"), os.environ["PATH"])),
        },
        "exclusive": True,
        "expected_duration": "2400s",
        "expected_memory": "48GiB",
        "session_id": args.session_id,
        "agent_id": args.agent_id,
        "worktree_manifest": {
            "worktree_id": str(args.workspace),
            "head": head,
            "modified_files": [],
            "untracked_files": [],
            "toolchain": TOOLCHAIN,
            "dependency_lock": "lake-manifest.json",
            "dependency_lock_sha256": file_hash(workspace / "lake-manifest.json"),
            "configuration_hashes": {file: file_hash(workspace / file) for file in configs},
            "external_dependencies": [
                {"path": str(checkout), "head": rev} for checkout, rev in checkouts.items()
            ],
            "required_artifacts": sorted(set(links.values())) + [str(args.toolchain / "lib/lean")],
            "resource_estimate_basis": (
                "ci-025463-78f105ec ran the first partial closure build at 1,646.50 s "
                "and 46.02 GiB peak RSS. ci-025634-2505f374 completed the closure with "
                "cached modules at 609.70 s and 8.47 GiB peak RSS."
            ),
        },
        "idempotency_key": "tempered-source-closure-" + sha256(
            f"{args.workspace}\n{head}".encode()
        ).hexdigest(),
    }
    return request


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--workspace", type=Path, required=True, help="New Git worktree")
    parser.add_argument("--mathlib", type=Path, required=True, help="Pinned Mathlib checkout")
    parser.add_argument("--toolchain", type=Path, required=True, help="Lean v4.33.1 installation")
    parser.add_argument("--session-id", required=True)
    parser.add_argument("--agent-id", required=True)
    args = parser.parse_args()

    for name in ("workspace", "mathlib", "toolchain"):
        setattr(args, name, getattr(args, name).resolve())
    if args.workspace.exists():
        parser.error(f"Use a new workspace path: {args.workspace}")
    for binary in ("lean", "lake"):
        if not (args.toolchain / "bin" / binary).is_file():
            parser.error(f"Missing {binary} in {args.toolchain / 'bin'}")
    with TemporaryDirectory(prefix=".tempered-source-", dir=args.workspace.parent) as temporary:
        staging = Path(temporary)
        request = prepare(staging, args)
        staging.rename(args.workspace)
    print(json.dumps(request, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
