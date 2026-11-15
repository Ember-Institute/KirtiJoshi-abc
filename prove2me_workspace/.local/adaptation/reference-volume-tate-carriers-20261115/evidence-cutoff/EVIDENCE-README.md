`unit-evidence-allowlist.current.json` lists only existing regular files in the
actual volume/Tate unit at the inventory cutoff. It contains 361 paths and
170,149,448 bytes. `present-evidence-inventory.json` records their exact hashes,
sizes, observation time and the five excluded Python-cache files. This is a
filename and hash review aid; it does not accept a compilation or publication.

The list retains all observed attempt inputs and reports, source/target
Decidable queries and facts, parser/runtime outputs, source overrides, frozen
effective and upstream source files, paper originals and page evidence,
untouched blind originals, and the tool drafts already integrated into B.
`exporter-cache-v2-provenance.json` is retained as provenance evidence; it is
not a build-cache directory.

`ci-receipt-resource-inventory.current.json` records all 29 existing CI result
receipts: 22 succeeded and seven failed. It retains the job ID, source/input
version, exit status, physical RSS/PSS, wall time, CPU total and user/system
details, resource source and degraded flag. Missing values remain null. The
original full receipts, including stdout, stderr and diagnostics, are in the
allowlist and remain the authoritative evidence.

`future-delivery-paths.plan.json` is an object for planning, not a path-list
input to the packager. It marks absent ledger, actual readbacks, frozen review,
kernel output, packet/ready, finalization and publication-journal paths as
unreviewed. The final successful kernel attempt suffix and extra diagnostic
paths must come from actual results. It contains no invented successful receipt
or ready record. Add those files through a new explicit reviewed extension
only after they exist.

Current B includes the five frozen effective sources, the upstream LogVolume
source and its patch. Some supporting source-build-plan, repair and accepted
source-graph receipts are outside B and appear only as path/hash references.
Those originals already belong to accepted earlier units and need not be
duplicated. `external-evidence-references.current.json` records their exact
paths and hashes. These references do not claim that B contains archive copies
of the referenced originals.

The draft `package_evidence.py` now accepts full lists that already contain its
tool paths. It deduplicates only equal hashes and rejects differing bytes. It
preserves extensions with their original filenames. It rejects omitted
request/submit/result files and omitted historical Lean files under `attempts`;
discovered files are never read as implicit new inputs. Integrate the reviewed
updated tools before packaging, so the installed and supplied tool bytes agree.

The draft `finalize.py` scans every allowlisted `*-result.json` at any depth.
It identifies MCP-CI receipts by `job_id`, `request` and `status`; missing
`resources` no longer causes a failure receipt to disappear. The existing
resource reader retains nulls and rejects nonterminal jobs. Platform publication
results retain their original files but do not become CI resource records.
Conflicting terminal receipts for one job stop finalization for review.

The current baseline changes as the main agent continues work. Later files
need explicit extensions; changed bytes need a new reviewed hash record.
The two tool changes here are equal-byte path deduplication and retention of CI
failure records whose resource fields are absent. No script invocation in this
task stages files or runs Git, CI, compilation or an API.
