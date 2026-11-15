This is an offline draft for five detached private volume/Tate Definitions. No
accepted packet, ready record, CI receipt or publication ID is supplied here.
The main agent must review and integrate the scripts into
`prove2me_workspace/.local/adaptation/reference-volume-tate-carriers-20261115`.

The five original modules are `Iut.Cor312.ContainerHull`, `Iut.Cor312.LogVolume`,
`TateCurvesTheta.QParameter.PrimeToOrder`,
`TateCurvesTheta.TateCurve.Weierstrass`, and
`TateCurvesTheta.QParameter.NormalizedOrder`. Their canonical Definition names
use `AbcAdaptation_Reference_` followed by the module name with underscores.

`delivery.py` retains the prior packet-field workflow. `prepare` and `check`
remain offline. Only `deliver` and `reconcile` load the established API helper.
The only POST endpoint is `/submit-definition`, with five private Definitions
in environment `0df444a360eaa60ab8c11dca51a86af692955474`. The existing private
mission is `eeb5193f-68c0-41d0-9263-4a5ff7c801ee`, with root
`e33ff731-60a7-43ef-87ae-c12aeba23cb5`. There are no theorem verification jobs,
public launches, mission creation, graph changes, or messages in this workflow.

Each publication saves its exact intent before POST and its original job ID
before polling. Keep one journal directory for the packet. A lost POST response
requires GET-only reconciliation against the original exact matching job; it
does not permit a second POST. The exact published Definition GET must match
name, title, code, natural-language statement, source, private visibility and
environment. The root graph must remain equal before and after delivery.

Use `delivery-blind-readbacks.template.json` only as a schema. Its false flags
and placeholder text are not accepted evidence. The main agent supplies actual
readbacks from two fresh GPT-6.1 agents, code-only inputs, untouched original
artifacts, actual author/model identities and reviewed translations. Retain
both originals and the independent-review metadata in the reviewed evidence
list. The per-bundle provenance identifies the original that produced that
formal readback; it must not relabel the separate English paper-context author.
Preserve an explicit placeholder for the unresolved Chinese uniformizer term
if it occurs in the Chinese text. This terminology question does not block
formal code work.

`prepare_ready.py` takes the actual final successful kernel receipt and audit
JSON as explicit arguments. It derives selected coverage from the current
inventory (147 records, 100 selected) and checks the emitted audit configuration.
It accepts this unit's list of paper-validation checks, rather than the older
dictionary schema. No packet-field 133/131/2 counts are inherited.

Copy `ready-inputs.template.json` to a reviewed input file and fill its exact
unit-relative paths after the jobs and reviews finish. Include all five exact
Definition leaf receipts and their artifact receipts. The non-CI evidence must
cover both actual independent readbacks and metadata validation; the reviewed
SOURCE_LEDGER producer/consumer paths and source provenance; and the existing
mission, root and root-graph readbacks with their scope review. Freeze this
evidence in the final prepublication review. The six CI gates must cover the
new leaves, Checks/Axioms, wrapped kernel identity, ImportAudit, Act1Scene1 and
AxiomAudit. The main agent must inspect the actual allowed-axiom output.

```bash
python3 -B prepare_ready.py --inputs ready-inputs.json \
  --kernel-receipt ACTUAL_SUCCESSFUL_KERNEL_RESULT.json \
  --kernel-audit ACTUAL_KERNEL_OUTPUT/next-carrier-kernel-audit.json
python3 -B delivery.py check --packet delivery/packet.json --ready delivery/ready.json
```

The helper runs the required whitespace checks when the main agent invokes it.
It writes accepted `ready.json` only after the receipt preflight passes. The
template files supplied in this draft cannot pass those checks.

LogVolume's effective source is the graph-accepted override with SHA256
`002f44da071e858c1fe48f3608da4e75f1179d3cd6c3007444bc5453440b7ef0`.
Its upstream source has SHA256
`79f0f12f1c82d6a0b6b83a42197527542fa946e9a5bb8dd4fd3572fd88edaf15`.
Preserve both sources, the patch, the source-build plan and acceptance evidence.
Do not label the effective source as the upstream Git blob. The IUT III p.94
weight formula versus code-header correspondence remains an open obligation.
Paper context remains separate from formal readbacks and does not establish
arithmetic object identity, live root membership, S2-04 or parent completion.

`finalize.py` takes explicit final kernel and production receipt paths plus exact
reviewed evidence lists. It records all CI attempts, including failures and
retries. Unknown resource values remain null. CPU total, user/system detail,
wall time, process-tree physical RSS/PSS and resource-source/degraded flags are
retained. Only `reference_source_preparation.definitions` (five appended rows)
and the new `reference_source_preparation.volume_tate_unit` can change. The
prior `packet_field_unit`, all other registry fields and all graph states are
preserved by an equality check. `--write-registry` installs only the reviewed
candidate; without it, finalization writes a candidate outside the repository.

```bash
python3 -B finalize.py --packet delivery/packet.json --ready delivery/ready.json \
  --journal delivery-journal --evidence-list unit-evidence-allowlist.json \
  --evidence-list post-delivery-evidence-allowlist.json \
  --kernel-receipt ACTUAL_SUCCESSFUL_KERNEL_RESULT.json \
  --production-receipt ACTUAL_PRODUCTION_RESULT.json \
  --plan /absolute/current-plan.md --out /tmp/NEW-volume-tate-finalization
```

Both evidence allowlist templates are deliberately empty. The main agent must
supply the exact reviewed filenames after jobs complete. No glob or discovered
unknown file becomes an included input. The packager enumerates receipt names
only to reject omissions; it never reads an unlisted discovered receipt. Include
sources, all attempts, parser/exporter/runtime/audit outputs, scripts, frozen
paper evidence, source overrides, untouched blind originals and delivery
journal readbacks. Credentials, `.git`, `.lake`, caches and lock/temp files are
excluded. There is no Git staging or commit command in these scripts.

```bash
python3 -B package_evidence.py --input-list unit-evidence-allowlist.json \
  --extra-list post-delivery-evidence-allowlist.json \
  --extra-list REVIEWED_EXTENSION_FILENAME.json --out /tmp/NEW-volume-tate-review
```

The packager preserves each extension's filename and rejects conflicting
collisions. It deterministically gzips every `.diff`, historical Lean input,
large artifact, parser/runtime artifact and small artifact ending in a double
newline. It verifies expanded SHA256 and leaves every original unchanged.
`archive-manifest.json` maps original paths to packaged paths. Review the exact
`staging-allowlist.json` before any separate authorized Git operation.
