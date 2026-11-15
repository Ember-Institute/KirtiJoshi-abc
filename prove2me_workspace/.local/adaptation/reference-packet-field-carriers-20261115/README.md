# Packet and field carrier evidence drafts

This unit publishes five private Definition bundles after kernel audit `ci-013658-36534ff1` and production gates `ci-013620-b1070538`. The exact source correspondence covers 131 named declarations and two genuine internal proof values. Publication IDs and exact GET readbacks are in `delivery-journal/`; all 26 CI attempts are retained in the finalization summary. The abc root graph is unchanged and S2-04 remains incomplete. The procedures below describe the evidence tools and their replay inputs.

`package_evidence.py` reads the exact unit-relative paths in `unit-evidence-allowlist.json`. This list also names the final blind readbacks and seven `readback-metadata/` files supplied by the main agent. It captures the current evidence files, including failed and retry requests/results, exact Lean compiler inputs, provenance, parser/runtime output, generated wrappers, source ledgers and paper evidence. The script also includes the five installed Definitions and these reproducibility drafts. It never runs Git, CI, a compiler, or an API. It never deletes an input or stages a path. New receipts cause a completeness failure until the reviewer explicitly extends the list. Add any new kernel helper sources, maps, readbacks and reviews by name in a separate JSON list.

The packager writes a new review tree outside the repository. Within the unit, every Lean input, parser/runtime output and every file larger than 65,536 bytes is stored only as deterministic gzip. This includes original Expr JSON, parser/runtime sources and historical attempts. It verifies each archive by streaming decompression and SHA-256. `archive-manifest.json` binds original paths, exact byte counts and hashes to packaged paths. The resulting `staging-allowlist.json` lists individual repository-relative files; it contains no directory or wildcard. Original inputs remain available in the active workspace. Review and install only those packaged paths through the main agent's existing workflow.

Example before delivery (choose a fresh output directory):

```sh
python3 /tmp/p2m-packet-field-evidence-finalize-v3-20261115/package_evidence.py \
  --out /tmp/p2m-packet-field-evidence-review-before-delivery
```

`finalize.py` is for after actual delivery. It calls only the existing `delivery.py` offline preflight/check helpers through `runpy`; it does not load the API helper. Every delivery journal input must be explicitly allowlisted. It checks the exact packet, successful ready gates, selected kernel retry and production-gates receipts, actual publication jobs and exact Definition GET readbacks. It requires identical root graph objects before and after delivery and an unchecked `S2-04` in the supplied plan. It does not change the plan, main documents or obligation database.

Select the actual final successful kernel retry by filename. The existing failed `kernel-audit-result.json` remains an attempt record. The production success currently recorded by the main agent is `production-gates-result.json` (job `ci-013620-b1070538`); the script validates this file at execution instead of trusting this note. The main agent must supply an explicit extension list for later retry inputs and receipts.

Example after delivery (replace the kernel retry filename and plan path with actual files):

```sh
python3 /tmp/p2m-packet-field-evidence-finalize-v3-20261115/finalize.py \
  --packet /home/admin-wsl/Coq/abc/prove2me_workspace/.local/adaptation/reference-packet-field-carriers-20261115/delivery/packet.json \
  --ready /home/admin-wsl/Coq/abc/prove2me_workspace/.local/adaptation/reference-packet-field-carriers-20261115/delivery/ready.json \
  --journal /home/admin-wsl/Coq/abc/prove2me_workspace/.local/adaptation/reference-packet-field-carriers-20261115/delivery-journal \
  --evidence-list /tmp/p2m-packet-field-evidence-finalize-v3-20261115/unit-evidence-allowlist.json \
  --evidence-list /tmp/p2m-packet-field-evidence-finalize-v3-20261115/post-delivery-evidence-allowlist.json \
  --evidence-list /tmp/REVIEWED-RETRY-EXTENSION.json \
  --kernel-receipt ACTUAL-SUCCESSFUL-KERNEL-RETRY-result.json \
  --production-receipt production-gates-result.json \
  --plan /home/admin-wsl/Coq/abc/docs/ACTUAL-PLAN.md \
  --out /tmp/p2m-packet-field-finalization-review
```

By default this writes a registry candidate and two evidence summaries in the fresh external output directory. `--write-registry` explicitly installs only that candidate after validation; use another fresh output directory when rerunning. The candidate changes only `reference_source_preparation.definitions` (five appended records) and adds `reference_source_preparation.packet_field_unit`. All IDs come from actual delivery results. Root graph records/counts, existing proofs, open frontiers and obligations remain byte-value equivalent. The candidate records `canonicalC22Connected: false`, detached graph membership and `S2-04_completed: false`.

`finalization-summary.json` records every allowlisted terminal MCP-CI result, including failures, timeouts and retries. Each record retains receipt/input hashes, job ID, compiler arguments, exit state, diagnostics/stdout/stderr, wall time, CPU total/user/system and their sum, physical RSS/PSS bytes and resource source/degraded fields. Missing values remain `null`. Selected final receipts are independently bound to ready gates. Platform publication receipts are retained as originals and are not presented as MCP-CI resource records.

After the registry candidate is reviewed and installed, package the complete result in a fresh directory:

```sh
python3 /tmp/p2m-packet-field-evidence-finalize-v3-20261115/package_evidence.py \
  --extra-list /tmp/p2m-packet-field-evidence-finalize-v3-20261115/post-delivery-evidence-allowlist.json \
  --extra-list /tmp/REVIEWED-RETRY-EXTENSION.json \
  --finalization-dir /tmp/p2m-packet-field-finalization-review \
  --out /tmp/p2m-packet-field-evidence-review-final
```

The registry enters the final allowlist only when its installed bytes equal the validated candidate. Packaging copies the extension lists as numbered reproducibility inputs. It excludes credentials, caches, pycache, lock/tmp files and all unlisted files. Do not copy an entire unit directory, use a broad `git add`, or remove original evidence to make the package small.
