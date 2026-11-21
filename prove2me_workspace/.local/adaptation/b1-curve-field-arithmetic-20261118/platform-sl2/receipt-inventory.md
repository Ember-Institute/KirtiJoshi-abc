# Private SL₂ and Tate receipt inventory

The recorded environment uses Lean 4.33.1 and Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`.
The terminal MCP-CI receipts identify worktree `/home/admin-wsl/Coq/abc` at HEAD `5ff88aae1695a547317558439249cec1ed91ccb3`.
The workspace is `/home/admin-wsl/Coq/abc/prove2me_workspace`.
The receipts record `exclusive_worktree` and `snapshot_id: null`.

## Private publications

| Theorem | Theorem ID | Publication job | Recorded article status | Receipts |
| --- | --- | --- | --- | --- |
| `EllipticCurveData.prime_dvd_ramificationIdx` | `695ba887-813b-4044-ab37-33e9d776f8e9` | `68a2c3c8-4691-47d9-bf2a-aa144bc35a71` | private, `Open` at publication | [Queue](theorem-batch-submission.json) · [Publication](AbcAdaptation.Reference.Iut.EllipticCurveData.prime_dvd_ramificationIdx-receipt.json) |
| `nonempty_tateStructure_of_torsion` | `9c4a74f6-1b13-43f2-8e44-3887b5abc445` | `719958a3-79c7-4380-9cd3-3db981852755` | private, `Open` at publication | [Queue](AbcAdaptation.Reference.Iut.nonempty_tateStructure_of_torsion-publish-submission.json) · [Publication](AbcAdaptation.Reference.Iut.nonempty_tateStructure_of_torsion-receipt.json) |
| `exists_tateUniformization` | `6ee6a3cd-649a-4604-a2d8-1400087da2d8` | `03514736-eaf0-414a-b358-480bfed0d6a2` | private, `Open` at publication | [Queue](AbcAdaptation.Reference.Iut.exists_tateUniformization-publish-submission.json) · [Publication](AbcAdaptation.Reference.Iut.exists_tateUniformization-receipt.json) |

The three publication receipts match the corresponding requests on name, title, formal statement, preamble, source, and natural language statement.

## Accepted reductions

| Parent | Submission ID | Terminal status and time (UTC) | Sole theorem child | Receipts |
| --- | --- | --- | --- | --- |
| `EllipticCurveData.prime_dvd_ramificationIdx` | `bc58c148-3dac-4911-abae-94ffc28859e5` | `SKETCH_ACCEPTED` at 2026-11-20 09:23:47.025214 | `nonempty_tateStructure_of_torsion` (`9c4a74f6-1b13-43f2-8e44-3887b5abc445`) | [Upload](AbcAdaptation.Reference.Iut.EllipticCurveData.prime_dvd_ramificationIdx-verify-submission.json) · [Terminal result](AbcAdaptation.Reference.Iut.EllipticCurveData.prime_dvd_ramificationIdx-verify-result.json) · [Decomposition](AbcAdaptation.Reference.Iut.EllipticCurveData.prime_dvd_ramificationIdx-decompositions.json) |
| `nonempty_tateStructure_of_torsion` | `e1a46253-fc83-4751-a40d-e0357cb93425` | `SKETCH_ACCEPTED` at 2026-11-20 09:55:29.140187 | `exists_tateUniformization` (`6ee6a3cd-649a-4604-a2d8-1400087da2d8`) | [Upload](AbcAdaptation.Reference.Iut.nonempty_tateStructure_of_torsion-verify-submission.json) · [Terminal result](AbcAdaptation.Reference.Iut.nonempty_tateStructure_of_torsion-verify-result.json) · [Decomposition](AbcAdaptation.Reference.Iut.nonempty_tateStructure_of_torsion-decompositions.json) |

The first decomposition records the Tate structure statement as `Open`.
Its later verification accepts the reduction to the uniformization statement.
The uniformization statement is `Open` in both receipts that record its status.

| Parent | Direct definition dependencies in decomposition order |
| --- | --- |
| `EllipticCurveData.prime_dvd_ramificationIdx` | `AbcAdaptation_Reference_Iut_Concrete_ModEllRepTorsionField` (`c9853da7-3eff-403c-9ae3-8e628ac912c8`)<br>`AbcAdaptation_Reference_Iut_Cor312_ThetaData_TateStructure` (`6447e7bb-4f13-4110-9084-612dfd9eecb9`)<br>`AbcAdaptation_Reference_Iut_Cor312_ThetaData_TateFamily` (`9bce2e6e-05b1-4abb-a962-c842ac8d7040`)<br>`AbcAdaptation_Reference_Iut_Concrete_TripodalInvariants` (`24a88985-5b74-4274-8554-c0929481a1b4`)<br>`AbcAdaptation_Reference_Iut_Concrete_TateInputsSupply` (`e8e269bd-328a-4d9d-b9a4-880db0c2d141`)<br>`AbcAdaptation_Tripod_RelativeValuation` (`f2f7627a-9442-4303-a499-e06daf876398`) |
| `nonempty_tateStructure_of_torsion` | `AbcAdaptation_Reference_Iut_Concrete_TateInputsSupply` (`e8e269bd-328a-4d9d-b9a4-880db0c2d141`)<br>`AbcAdaptation_Reference_Iut_Cor312_ThetaData_TateFamily` (`9bce2e6e-05b1-4abb-a962-c842ac8d7040`)<br>`AbcAdaptation_Tripod_PlaceUnder` (`59dfa846-1d49-4d6b-9205-27f46fc7d73f`)<br>`AbcAdaptation_Tripod_RelativeValuation` (`f2f7627a-9442-4303-a499-e06daf876398`) |

## Lean files

| Local file | Archived copy | SHA-256 | MCP-CI job |
| --- | --- | --- | --- |
| [Sketch_EllipticCurveData_prime_dvd_ramificationIdx.lean](../platform-sl2/Sketch_EllipticCurveData_prime_dvd_ramificationIdx.lean) | Byte-for-byte copy verified | `eb967aa4286c904be3eebfe1f775e66423fe91a6c77591616b8523a225149af7` | [ci-025577-6dea798d](../receipts/round-ci-025577-6dea798d-result.json) |
| [Thm_AbcAdaptation_Reference_Iut_nonempty_tateStructure_of_torsion.lean](../../../../Theorems/Thm_AbcAdaptation_Reference_Iut_nonempty_tateStructure_of_torsion.lean) | Byte-for-byte copy verified | `646d7f6d195c2d609961f6308ab88be637709c8a4008b3b47d64a255996e3583` | [ci-025550-49c92e31](../receipts/round-ci-025550-49c92e31-result.json) |
| [Sketch_nonempty_tateStructure_of_torsion.lean](../platform-sl2/Sketch_nonempty_tateStructure_of_torsion.lean) | Byte-for-byte copy verified | `615a8361f009f20b2f3364e7404e9723fcc930988d65f8ef67d707fe17a1764d` | [ci-025662-2f6c72c4](../receipts/round-ci-025662-2f6c72c4-result.json) |
| [Thm_AbcAdaptation_Reference_Iut_exists_tateUniformization.lean](../../../../Theorems/Thm_AbcAdaptation_Reference_Iut_exists_tateUniformization.lean) | Byte-for-byte copy verified | `54a8517d7f7921567deff9cfe8b3f3529c1438e21a6b4fbd300f944cb0c6d4cc` | [ci-025597-0e1ef2ac](../receipts/round-ci-025597-0e1ef2ac-result.json) |

Each accepted sketch has the same SHA-256 in the local mirror, archived copy, upload receipt, and MCP-CI manifest.
The ramification packet manifest records the earlier failed sketch hash `213faa04cb88cc0324f7c9866eac4fdc2c8dfd00f1717c0bae32ef48ab6d7214`.
The success and upload receipts give the accepted hash `eb967aa4286c904be3eebfe1f775e66423fe91a6c77591616b8523a225149af7`.

The two statement artifacts contain `sorry` placeholders. Each accepted sketch imports its declared theorem child.
The receipts cover leaf checks for the two statements and sketches. The proof status shown above is the status at publication.

## MCP-CI attempts

Wall and CPU times use seconds. Peak RSS is physical memory for the process tree in GiB. The receipts leave peak PSS and the resource degradation marker unspecified.

| Job | Source SHA-256 prefix | Status / exit | Wall s | CPU s (user + system) | Peak RSS GiB | Diagnostic or result |
| --- | --- | --- | ---: | ---: | ---: | --- |
| [ci-025550-49c92e31](../receipts/round-ci-025550-49c92e31-result.json) | `646d7f6d195c` | succeeded / 0 | 57.77 | 56.88 (2.59 + 54.29) | 3.89 | Tate structure statement artifact. One expected placeholder warning. |
| [ci-025559-7c4790c7](../receipts/round-ci-025559-7c4790c7-result.json) | `bccac2d20b3a` | succeeded / 0 | 130.80 | 128.38 (2.70 + 125.68) | 3.82 | Relative valuation definition artifact. Two warnings. |
| [ci-025564-5d359246](../receipts/round-ci-025564-5d359246-result.json) | `213faa04cb88` | failed / 1 | 102.57 | 105.60 (8.96 + 96.64) | 4.14 | Ramification sketch. Torsion-cardinality application type mismatch at line 651. |
| [ci-025577-6dea798d](../receipts/round-ci-025577-6dea798d-result.json) | `eb967aa4286c` | succeeded / 0 | 78.01 | 78.49 (8.40 + 70.09) | 4.14 | Transported cardinality across decidable equality instances. Accepted sketch input with 15 warnings. |
| [ci-025597-0e1ef2ac](../receipts/round-ci-025597-0e1ef2ac-result.json) | `54a8517d7f79` | succeeded / 0 | 97.70 | 91.31 (2.64 + 88.67) | 3.03 | Uniformization statement artifact. One expected placeholder warning. |
| [ci-025613-151f1794](../receipts/round-ci-025613-151f1794-result.json) | `90d04c12d8ad` | succeeded / 0 | 86.34 | 85.46 (3.26 + 82.20) | 3.91 | Definition artifact for the finite place below a place of the extension. |
| [ci-025617-3991790b](../receipts/round-ci-025617-3991790b-result.json) | `4f01110f6c5c` | failed / 1 | 96.72 | 125.58 (59.37 + 66.21) | 4.34 | Tate structure sketch. Coordinate and torsion instance mismatches and two curve map rewrite failures. |
| [ci-025630-7087e27a](../receipts/round-ci-025630-7087e27a-result.json) | `01b47c2a505b` | failed / 1 | 85.81 | 114.57 (57.28 + 57.29) | 4.34 | Qualified the curve map rewrites and transported the torsion instance. Coordinate projections still differed at lines 1305 and 1308. |
| [ci-025640-f3eb52df](../receipts/round-ci-025640-f3eb52df-result.json) | `4fbd129ee31f` | failed / 1 | 87.11 | 115.11 (55.96 + 59.15) | 4.36 | Split the coordinate projections by constructor. The point map injectivity proof still needed decidable equality. |
| [ci-025662-2f6c72c4](../receipts/round-ci-025662-2f6c72c4-result.json) | `615a8361f009` | succeeded / 0 | 81.29 | 110.54 (56.54 + 54.00) | 4.35 | Supplied decidable equality locally. Accepted sketch input with 55 warnings. |

## Requests and archive paths

These paths are relative to the existing project source ledger. The platform files above fit under `platform-sl2/` with their archive names. The ramification publication and its batch queue record already have local mirrors there. The MCP-CI results fit under `receipts/round-<job-id>-result.json`.

| Request | Archived file | Proposed path for the ledger |
| --- | --- | --- |
| Tate structure publication | [submit-problem.json](ramification-reduction-submit-problem.json) | `platform-sl2/ramification-reduction-submit-problem.json` |
| Ramification verification | [verify-request.json](ramification-reduction-verify-request.json) | `platform-sl2/ramification-reduction-verify-request.json` |
| Uniformization publication | [submit-problem.json](tate-structure-reduction-submit-problem.json) | `platform-sl2/tate-structure-reduction-submit-problem.json` |
| Tate structure verification | [verify-request.json](tate-structure-reduction-verify-request.json) | `platform-sl2/tate-structure-reduction-verify-request.json` |

[Trilingual readback](../SOURCE_LEDGER.md#the-private-sl₂-ramification-and-tate-structure-reductions)

The project and proof-dependency audit [`ci-025742-eeb452a1`](../receipts/round-ci-025742-eeb452a1-result.json) compiled in 114.02 s and took 119.03 CPU s (16.60 user + 102.43 system) at 8.25 GiB peak physical RSS. Lean exited with code 0 and attributed `sorryAx` solely to the declared platform child. The generic MCP-CI review reported a failure because it detects the child’s `sorryAx`.

The project and proof-dependency audit [`ci-025751-99f05c51`](../receipts/round-ci-025751-99f05c51-result.json) compiled in 118.22 s and took 159.37 CPU s (82.81 user + 76.56 system) at 8.62 GiB peak physical RSS. Lean exited with code 0 and attributed `sorryAx` solely to the declared platform child. The generic MCP-CI review reported a failure because it detects the child’s `sorryAx`.
