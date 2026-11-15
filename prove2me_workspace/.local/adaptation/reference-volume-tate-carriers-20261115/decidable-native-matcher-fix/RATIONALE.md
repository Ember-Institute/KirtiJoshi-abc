# One observed incompatible native helper

The typed local constructor annotation passed the original strict BinderInfo guard in `ci-013954-948862e7` (`kernel-audit-v4-result.json`). That audit then failed because the decoded genuine source `Nat.decEq.match_1` occurrence carries zero universe arguments, while the existing Lean 4.33.1 constant requires one.

The bound genuine Lean 4.35 source closure exports this helper as a safe, axiom-free definition in `Init.Prelude`, without universe parameters. Its motive is `Bool → Prop`. Its value uses only `Bool.casesOn.{0}`, `Eq.refl.{1}`, `Bool`, its constructors, and `Eq`. This value can be checked independently under the platform's stable primitive API. The source record is copied here for review; the integrated auditor continues to use the externally bound closure and receipt, not this temporary copy.

The patch introduces exactly one native-name exception: `Nat.decEq.match_1`, reached through the genuine source `Nat.decEq._proof_1` dependency stack. It checks the source's name-bound record, kind, owner, safety, zero universes, empty axioms, and Bool-to-Prop motive. At runtime it requires the native counterpart to be a safe definition in `Init.Prelude` with exactly one universe parameter. It records that actual native type and the actual native level parameters. It does not assert source/native type equality, change the native declaration, or create a new declaration.

The exact source body then goes through the existing dependency traversal, original BinderInfo inventory check, `Kernel.check`, exact source type equality, allowed Init owner check, and axiom check. Its source occurrences are expanded with that checked genuine body. The report calls this an exact same-name incompatible matcher, with `standaloneTargetIdentity: null`; absent support retains its existing report method. All other native constants retain the immediate return path.

This patch does not add a general arity-repair rule, a name relocation, a body replacement for arbitrary native APIs, or an alternative decision algorithm. It leaves the constructor annotation, original strict BinderInfo guard, decision-bit equation, whole parent-value comparisons, and all production carrier files unchanged.

No compiler, MCP-CI, API, or Git operation was used. All writes are in this task directory. Root must validate the candidate with the next exclusive kernel audit.
