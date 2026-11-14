This directory supplies the strong Northcott preflight and finalizer.
It does not supply a new publisher or API adapter.
The main agent retains the established `delivery_draft.Delivery` submission protocol.
This subagent wrote only this task directory and made no compiler, CI, API, cache, Git-index or workspace change.

The evidence directory is:

`/home/admin-wsl/Coq/abc/prove2me_workspace/.local/adaptation/northcott-sourceproof-20261114`

Final names come from `delivery-plan.json`.
The preflight requires five unique ASCII platform names.
It derives the three estimates from the witness dependency list.
It keeps the existing `AbcAdaptation.Tripod.boundedDegreeFiniteness` name and ID.
It does not hardcode the superscript-one names from the initial source draft.
Current file hashes and final CI receipts must bind the renamed modules and real witness imports.
Historical first attempts remain in the resource summary.

To replace the draft publisher's weaker preflight, load this module in the root's API-adapter process:

```python
import importlib.util
spec = importlib.util.spec_from_file_location(
    'northcott_strong',
    '/tmp/p2m-northcott-final-delivery-20261114/delivery_common.py')
strong = importlib.util.module_from_spec(spec)
spec.loader.exec_module(strong)
Delivery.preflight = strong.preflight
# Keep the root's real API adapter and reviewed Delivery(...).run() invocation.
```

The replacement is read-only.
It also works as `strong.preflight()` before publication.
It returns `delivery-validation.json`, as the draft method requires.
It performs no submission or retry.

Required validation fields:

```json
{
  "passed": true,
  "exact_existing_target_type_equal": true,
  "readbacks_compiler_bound": true,
  "new_open_mathematical_obligations": 0,
  "source_hashes": {"eight-final-workspace-relative-paths": "SHA256"},
  "solution_hashes": {"six-final-workspace-relative-paths": "SHA256"},
  "compiler_checks": [
    {"tag": "real-receipt-prefix", "source": "actual-relative-source", "review": false, "artifact": false}
  ],
  "declaration_graph_sha256": "SHA256 of decl_graph.jsonl",
  "compiler_formals_sha256": "SHA256 of compiler-formals.json",
  "readbacks_sha256": "SHA256 of final-readbacks.json"
}
```

`graph_sha256`, `syntax_sha256`, and `readback_sha256` are accepted aliases for the last three fields.
If both names occur, both values must match the file.
The eight source paths and six Solution paths must match the final plan exactly.

The compiler check list must include:

- Each of eight source leaf checks and its artifact build.
- Each of six independent Solution leaves.
- The declaration-graph extraction leaf.
- A Lean Syntax/formal extraction leaf and a Validate…Types leaf.
- Own `Solutions/Checks_…` review, `AuditAllDefinitions.lean`, and `ProductionGates.lean`.

Every receipt must match its exact source hash, parameters, actual arguments and stable exclusive workspace.
A review receipt must report `review.passed: true`.
No output may include `sorryAx`.
Successful leaves need a physical RSS receipt at or below 16 GiB.
Final reviews bind all eight current sources.
Each independent Solution binds its own file through its leaf `source_sha256`; local Solution paths are not assumed to occur in every review manifest.
`existing-types-equal.json` must be JSON `true`.

`compiler-formals.json` is a six-name map:

```json
{
  "fully.qualified.name": {
    "preamble": "exact platform preamble",
    "formal_statement": "exact platform theorem statement/stub",
    "source": "workspace-relative-source.lean",
    "syntax": "nonempty Lean Syntax evidence, or an object with that evidence"
  }
}
```

The source may also be an absolute path inside the actual workspace.
The preflight compares each child payload's preamble and formal statement byte for byte with this compiler-derived record.
It does not recover declaration or proof boundaries with regular expressions.
The final type checks and independent Solution receipts remain mandatory.

`final-readbacks.json` must contain sixteen unique `declarations` and `input_file_sha256` for all eight current sources.
Each row needs `declaration`, relative `path`, `en`, `zh_Hans`, `ja`, `compiler_name`, `compiler_source_span`, and `elaboratedType`.
Rows must match compiler name/userName, source owner, span and type.
The preflight checks actual proof dependencies and declaration reachability.
Every owned output must have a consumer in the six source proofs.
The witness must consume exactly the three estimate theorem modules.
The parent must consume exactly its two immediate theorem children.
The final source theorem imports must match the same dependency lists as their Solutions.
Definitions must not import Theorems.
No source or Solution may import Iut, Genl, Heights, Solutions or Open as runtime dependencies.

Payloads must be refreshed from final compiler formals and the final readbacks.
The exact Mochizuki quotation plus those readbacks must supply Definition, child and parent metadata.
The existing publisher's intent/receipt replay protocol remains unchanged.
No finalizer action repeats a publication or proof submission.

`SOURCE_MANIFEST.json` binds the actual local archive bytes and required Mathlib source bytes.
`source-pin-draft.json` must identify that same archive path and SHA256.
The preflight verifies the included Iut and Mathlib license copies by SHA256.
It does not require or invent a tracked Git blob for the ignored archive.
The historical Iut `d9465c…` citation remains unverified.
All metadata source fields must carry the actual archive SHA256 and an explicit unverified-revision limit.
Candidate hashes in the source manifest describe the historical adaptation inventory.
The final validation and real CI receipts bind the mechanically renamed platform declarations.

After the main agent completes publication, graph readback and parent metadata synchronization, run:

```sh
python3 /tmp/p2m-northcott-final-delivery-20261114/finalize.py
```

The finalizer validates two private Definition publications and five private mathematical-node publications.
It validates all six real proof submissions.
The five new theorem proofs must be ACCEPTED.
The parent composer may have a SKETCH_ACCEPTED verification receipt, followed by an ACCEPTED graph reduction and actual Proved parent state.
The parent formal statement must remain byte-identical to its saved baseline.
Its exact patched metadata must match the saved server readback.

The graph audit requires precisely:

- Five added mathematical theorem nodes, all Proved.
- Witness→three estimates, tied to the actual accepted witness submission.
- Existing parent→two children, tied to the actual parent composer submission.
- Two added ACCEPTED reductions and five added dependency pairs.
- Existing mathematical nodes and reduction identities preserved.
- Only the existing parent removed from the fully paginated open frontier.
- The root still Open; no unrelated old theorem status changed.

Expected frontier 28→27 is checked through actual before/after data and the exact removed parent ID.
All graph counts come from those saved observations.
No count is inferred from a planned publication alone.

The registry gains five direct closed proof records and the parent's separate Proved composer record.
It records both actual dependency reductions and the source archive evidence.
Resource summaries retain every terminal attempt, including earlier names and failed attempts.
Missing resource source, degraded, CPU or memory fields remain null, meaning unknown.

The only document edit removes the exact remaining Northcott §1 bullet:

`- refer/iut/Iut/Tripod/Northcott.lean:183`

The actual Markdown line has backticks around the path.
The current document has no other Northcott pending item.
All other paragraphs, other docs, and plan checkboxes remain untouched.
Stage scope is the eight current sources, own Checks, this unit evidence, registry and that one document.
Unrelated staged and unstaged changes remain intact; their index entries are checked before and after staging owned paths.
The script does not commit or push.
