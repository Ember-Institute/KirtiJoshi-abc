# Main-bound paper context draft

This packet covers exactly five source bundles and 27 complete parser-selected commands (5/3/2/13/4).

- `paper-context.json`: source context, exact command bytes and bindings, provenance, actual consumers, and nine normalization distinctions.
- `PAPER-CONTEXT.en.md`: readable English background and selected command coverage.
- `quotations-and-evidence.json` and `quotations.en.md`: 18 original Mochizuki excerpts with exact locators.
- `evidence/`: original page renders, raw extracts, and full-paper search extracts.
- `validate_context.py`: offline byte, coverage, provenance, and evidence checks.
- `paper-context-validation.json`: passed offline validation.
- `build_context.py`: reproducible draft assembly. Rerun validation after assembly.

Run `python3 /tmp/p2m-main-bound-paper-context-v6-20261115/validate_context.py` to recheck the packet.

The validation script does not compile Lean or establish mathematical fidelity. The writer visually checked the cited original PDF pages. The packet is author/source context, not independent blind readback.

Keep the normalization distinctions with the delivered context. In particular, arbitrary positive QPilotData weights do not supply the paper fiber weights whose sum is one. The source residue-characteristic grouping logQAt has no proved identification with the paper normalized fiber quantity log(q_vQ). The q-side minus sign, the 2ℓ root normalization, the half-order procession, and global degree normalization remain separate.

PrimeCountingBound uses 3/2; Proposition 1.6 uses 4/3. Theorem110Certificate and LocalEstimate remain explicit supplied certificates. No proof of the paper identity, Corollary 3.12, Theorem 1.10, or ABC is asserted.

All new files were written under this /tmp directory. The task made no compiler, MCP-CI, API, network, or Git call and did not modify the main workspace.
