# Foundation carrier subtraction handoff

The five usable isolates are in `generated/FoundationSmall/`. They were generated
from authentic parser JSONL accepted by the main agent for MCP-CI job
`ci-013283-faafeb4e`. No Lean process, CI request, API request, Git command, or main
workspace mutation was performed by this subagent. All writes are below this
unique temporary directory.

| File | Selected complete commands | Retained original context commands, including EOI | Removed declarations | Bytes |
|---|---:|---:|---:|---:|
| `Places.lean` | 5 | 11 | 4 | 2440 |
| `PointMap.lean` | 1 | 11 | 5 | 1670 |
| `RationalPlace.lean` | 3 | 6 | 2 | 1778 |
| `Procession.lean` | 9 | 10 | 7 | 4497 |
| `PacketPresentation.lean` | 8 | 10 | 9 | 5907 |

`subtract_foundation.py` uses complete AST command ranges and compiler-range joins.
It does not scan source text to find declarations or references. It replaces only
the parser-bound import header and removes excluded whole declaration commands.
All other bytes remain in source order, including every namespace, section,
variable, scoped open, universe, instance attribute, module document, license
prefix, and whitespace. Declaration docs remain attached to their complete
selected command. Deleted declarations include their own docs and attributes.

`generated/foundation-small-source-report.json` records source and parser hashes,
each retained/removed command range and hash, output-coordinate ranges, and an
exact provenance partition for every output byte. Source offsets use normalized
UTF-8 coordinates, explicitly bound to `originalCoordinateSource` and its hash.
Generated precise import bytes are marked separately from copied source bytes.
`small-source-inputs.json` gives the five compiler-oracle input records; the main
agent can relocate byte-identical sources into its stable workspace and use one
input per MCP-CI process.

The original `RationalPlace.IsFinite` equations command remains before
`residueChar`. The full `RationalPlace` inductive command includes original
`deriving DecidableEq`. Procession retains the exact `procLabels_mono` proof and
both original Capsule instances. PacketPresentation retains both original field
instance attributes and its Total topology instance. The generated no-range
auxiliaries are reconstruction obligations, not handwritten declarations.

The source import list uses the precise 4.35 candidates from the frozen
`imports.json`, as authorized by the main agent for provisional small-source CI.
`precise-import-review.json` records that narrow review scope. No broad `import
Mathlib` fallback is used. The 4.33 migration candidates remain separate and need
compiler acceptance; they are not silently substituted into 4.35 isolates.

The copied main acceptance omitted a query hash. The supplemental acceptance
`parser-acceptance-with-query-binding.json` records its original path and hash,
adds the current query hash, and states that this binding was recorded after CI.
The query is byte-identical to the frozen pre-CI parser draft, and the CI request,
actual arguments, environment config path, receipt hash, JSONL hashes, normalized
source hashes, and graph hash are checked by the subtraction tool. This supplement
does not claim that the original acceptance already contained a query hash.

Python syntax validation passed. The coordinate, splice, license-prefix, and
retained-command mapping utilities were also checked against both authentic,
accepted numeric parser JSONL artifacts; see `python-validation.json`. The actual
five-module subtraction then passed all input-binding, complete-command, source
normalization, source-order, dependency-closure, selected-axiom, and provenance
checks. Compilation has not been run by this subagent.

## Main-agent next steps

1. Copy the five isolates and report into the stable main task directory without
   changing bytes. Record the integrated paths/hashes.
2. Through MCP-CI, run each small source under the locked original Lean 4.35
   environment using the established small-source InfoTree oracle. Do not import
   the cached originals into that fresh elaboration environment.
3. Confirm generated declarations and auxiliaries, especially shared
   `IsFinite.match_1`, deriving instances, PointMap proofs, the Fintype proof, and
   `Procession.standard._proof_1`. The original `*_proof_N` names are not assumed
   stable merely because complete source commands survived. Compare accepted
   original and small-source type/value expressions, dependencies, and axioms.
4. Generate the platform carriers from those accepted small-source reference
   facts, inside `AbcAdaptation.Reference`. Preserve all original contexts inside
   the wrapper. Rewrite qualified project references only from compiler reference
   ranges; account for constructors, projections, instances, proofs, and matchers
   in the original-to-wrapped name map. No regex reference rewriting.
5. For Lean 4.33, use the reviewed path migrations in `imports.json`, then perform
   the normal type/value kernel and allowed-axiom checks and required project
   acceptance. Source helpers stay in their carrier bundles. There are at most
   five carrier Def bundles, with actual downstream consumers, and no separate
   helper/matcher/projection nodes.

The subtraction script intentionally stops at the original-environment isolates.
Wrapper reference rewriting needs the pending accepted small-source InfoTree
facts. Successful parser subtraction does not establish compiler compatibility,
generated auxiliary identity, wrapped kernel equality, or a mathematical parent
obligation.
