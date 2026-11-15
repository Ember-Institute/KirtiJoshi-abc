Tooling draft prepared only in `/tmp/p2m-tate-theta-tools-v5-20261115`. No main workspace writes, compiler, scheduler, API, network, or Git commands were executed. `static-validation.json` passed 82 checks, including actual prior evidence binding for 339 named constants, 15 prior modules, and all 42 required pairs. These checks are not acceptance of this unit's Lean source.

Install the core scripts listed in `draft-manifest.json` beside the inventory agent's finalized artifacts at `W/.local/adaptation/reference-tate-theta-carriers-20261115` (`B`). Inventory draft: `/tmp/p2m-tate-theta-inventory-v5-20261115`; inventory modules/order/counts are unchanged: JInvariant, Parametrization, AdmissiblePrime, TateStructure; 117 original / 78 selected / 20 source command roots. Inventory files already bind intended absolute B paths; copy their frozen-sources and supporting evidence before binding the unit. Do not copy the inventory's old generic carrier_contract/wrapper/exporter from another unit.

`reuse-provenance.json` pins the accepted volume/Tate inputs. `diffs/` gives exact changes to copied tools. `exporter-provenance.json` identifies the original Expr exporter. Its four module imports differ; the cached axiom collector, expression serialization, and indexed Lean4.35 owner lookup remain exact. It scans actual source-owned constants once, resolves each unique exact display key to the real compiler Name, checks a non-null supplied Name if present, and exports true str/num components. This supports six unselected private Parametrization Names containing numeric0. The `matchingNames` local avoids Lean's `matches` keyword.

`prepare_unit.py` binds the three accepted units from real compiler comparisons only. It takes:

```sh
python3 "$B/prepare_unit.py" \
  --inventory-unit "$B/unit-config.json" \
  --dependency-closure "$B/dependency-closure.json" \
  --volume-bound-unit "$PREVIOUS/bound-unit-config.json" \
  --volume-correspondence "$PREVIOUS/accepted-compiler-correspondence.json" \
  --volume-ci-result "$PREVIOUS/kernel-audit-v5-result.json" \
  --provenance-audit "$B/source-provenance-audit.json" \
  --out "$B/bound-unit-config.json"
python3 "$B/prepare_precise_imports.py" \
  --imports "$B/imports.json" --unit-config "$B/bound-unit-config.json" --out "$B"
```

`PREVIOUS=W/.local/adaptation/reference-volume-tate-carriers-20261115`. The volume dependency explicitly requires successful final-v5 job `ci-013964-cce30c9e`; 98 named comparisons and two genuine source proof-value resolutions stay separate. The packet/field's accepted exceptional evidence remains checked only for that prior unit. No prior proof-value resolver is loaded into this unit.

The precise import preparation preserves the exact compiler term-owner candidates, replacing project source imports only with installed Definitions on the platform. It adds only `Mathlib.Topology.MetricSpace.Ultra.Basic` for JInvariant and Parametrization's retained `IsUltrametricDist` variables. All contexts remain; broad `Mathlib`, `TateCurvesTheta`, and upstream production project dependencies are rejected. The new imports JSON and precise-import-review JSON are mutually hash-bound. The preparation may replace imports.json in B only after the inventory is integrated; it does not change source bytes or parser/Expr inventories.

Only root runs MCP-CI. `ci.py` defaults first attempts to60s/16GiB, keeps the existing pinned search paths, uses exclusive workspace jobs, records actual Git/worktree manifest state, hashes the complete structured request for idempotency, saves submissions before waiting, and checks terminal arguments/physicalRSS/CPU totals. Resource estimates for later attempts must be supplied from actual receipt evidence. Runtime jobs are sequential one-source process jobs. Do not run the root orchestrators from this temporary directory: their runtime B is the installed script directory.

Root sequence:

1. Run parser and original Expr queries through MCP-CI using `FOUNDATION_PARSER_CONFIG=$B/parser-config.json` and `NEXT_CARRIER_EXPORT_CONFIG=$B/export-config.json`. Standard request source files are B/QueryNextCarrierParserRanges.lean and B/QueryNextCarrierOriginalExprs.lean. Receipts use parser-ranges and original-exprs tags.
2. Use `run_queries.accept_parser()` and `accept_original()` (or run_queries.py after both terminal receipts exist) to produce hash-bound acceptance artifacts. The latter requires parser/exporter actual Names to agree exactly for all117.
3. Run select_small.py with the accepted parser files, graph path from inventory, prepared imports/review, and bound unit config:

```sh
python3 "$B/select_small.py" \
  --parser-acceptance "$B/parser-acceptance.json" \
  --parser-ci-result "$B/parser-ranges-result.json" \
  --parser-config "$B/parser-config.json" --parser-query "$B/QueryNextCarrierParserRanges.lean" \
  --graph "$GRAPH" --imports "$B/imports.json" \
  --reviewed-imports "$B/precise-import-review.json" \
  --unit-config "$B/bound-unit-config.json" --out "$B/generated"
python3 "$B/bind_small_oracles.py" \
  --small-source-report "$B/generated/foundation-small-source-report.json" --out "$B"
```

4. Root uses run_small_oracles.py (MCP-CI only) for four exact original4.35 sources. It deliberately reuses the accepted runtime driver at PREVIOUS/ExtractSmallRuntimeOracle.lean; each source is one frontend/process. The same-byte driver copy in this draft is provenance only; no fresh driver gate is needed. New source attempts start60s/16GiB.
5. `run_wrapper_generation.py` requires all four accepted small-original indexes/CI receipts, parser acceptance, original Expr export/receipt/acceptance, bound dependencies and precise imports. It uses the prior driver's actual acceptance+receipt directly. No wrapper is generated before those checks succeed.

The generator copies whole selected declaration commands, full inline proofs, all source contexts, all15 AdmissiblePrimeData fields and all6 TateStructure fields. It records source-to-small-to-wrapper bytes/body ranges. JInvariant and Parametrization are each allowed exactly one anonymous `noncomputable section` at EOF, checked from original parser AST and retained unchanged contexts; their wrappers add an explicitly recorded framing end. AdmissiblePrime and TateStructure must have an empty AST scope stack. This is a new exact two-module policy, not the prior Weierstrass special case.

Wrapper status remains `four-wrapper-drafts-generated-main-platform-CI-and-kernel-audit-pending`. Bundle count derives from actual output; selected count includes current-unit records only (78), with prior339 recorded separately. Candidate target Names are not accepted identities. Root must perform current4.33 platform leaves/artifacts and the kernel agent's strict audit after generation. Delivery/API/finalizer tooling is intentionally outside this draft; no parent mathematical completion is claimed.
