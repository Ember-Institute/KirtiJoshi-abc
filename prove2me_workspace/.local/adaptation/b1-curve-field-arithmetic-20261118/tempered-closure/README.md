# Tempered fundamental group dependency build

`TemperedSourceClosure` builds the 60 pinned Pi1, TemperedFundamentalGroups, and EllipticCurves modules needed by the étale comparison and the two orbifold constructions. The preparation script records the source revisions and the hashes before and after the Lean 4.33.1 compatibility patch. [Patch](lean433.patch)

- `ValuationInertia` uses `MonoidHom.domRestrict` for the restricted homomorphism.
- `Specialization` makes the valuative square reducible and applies the lift factorization at the closed point.
- `Projective` infers properness of the degree-zero isomorphism through its finite morphism instance.
- `Category` uses the underlying scheme morphisms for the multiplication law and reduces the fibre action after rewriting.

## Prepare a workspace

Use Python 3.10 or later, Git, and access to the pinned GitHub archives. Use Lean `v4.33.1` and the prebuilt artifacts for Mathlib commit `0df444a360eaa60ab8c11dca51a86af692955474`.

Choose a new workspace path with an existing parent directory. Replace the paths and the session and agent identifiers in the command.

```bash
python3 prepare.py \
  --workspace /path/to/tempered-dependency-worktree \
  --mathlib /path/to/mathlib4-0df444a \
  --toolchain /path/to/leanprover--lean4---v4.33.1 \
  --session-id SESSION_ID \
  --agent-id AGENT_ID \
  > tempered-dependency-request.json
```

The archived patch omits the single-space context markers on blank lines. Its reverse application was checked against the successful build tree. The receipt retains the exact submitted patch hash.

The script checks the pinned Mathlib dependency lock and the required artifacts. It stages the patched files in a new Git worktree and writes the source hashes to `SOURCE_MANIFEST.json`. The `prebuilt_mathlib` package links to the existing artifacts and defines zero build targets. The script writes the MCP-CI request to standard output. [Preparation script](prepare.py)

## Build with MCP-CI

1. Pass the request to `ci_submit`. It specifies `task_type: "full"`, `target: "TemperedSourceClosure"`, and `exclusive: true`.
2. Record the job ID. Keep the workspace and the linked dependencies stable until the job ends.
3. Use `ci_wait` with the same job ID and `timeout_seconds: 25`. Repeat while the job is active.
4. Use `ci_result` to check the exit code, workspace, arguments, and resource data. Read the log for diagnostics.

The request estimates 2,400 seconds and 48 GiB for a new closure workspace with prebuilt Mathlib. The first partial build took 1,646.50 seconds and peaked at 46.02 GiB RSS. The successful build with cached closure modules took 609.70 seconds and peaked at 8.47 GiB RSS. [MCP-CI receipts](receipts.json)

After the build succeeds, add the workspace's `.lake/build/lib/lean` directory to the consumer's `LEAN_PATH`. Record the workspace revision and the closure job ID in the consumer's MCP-CI manifest.

## Verified input

MCP-CI job `ci-025634-2505f374` built `TemperedSourceClosure` in exclusive mode and exited with code 0. The preparation test matched all 60 Lean sources, the entry module, the patch, and the six build configuration files to that job's input. It also checked the presence of prebuilt artifacts for 10,403 external modules. [MCP-CI receipts](receipts.json)
