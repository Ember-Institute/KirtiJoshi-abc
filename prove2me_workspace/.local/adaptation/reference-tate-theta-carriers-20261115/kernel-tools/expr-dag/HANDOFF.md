Minimal Lean4.33.1 Expr DAG codec draft. All files were written only here. No compiler, MCP-CI, API, network, Git, or main-workspace writes were executed by this agent. Root owns compilation and physical-memory acceptance.

Files:

- `ExprDagCodec.lean.inc`: insert inside FoundationAudit after existing checked and Name/Level/Binder codecs.
- `ExprDagCodec.lean`: self-contained import-Lean source containing exact reused primitive codecs and the DAG implementation.
- `ExprDagCodecCheck.lean`: same standalone implementation with a small run_meta check of 14 roots. This is a single leaf source; it needs no new olean to import. It checks exact duplicate reuse, separates lambda binder Names and BinderInfo, preserves numeric0 Name and level components, and separates otherwise-identical let nondependent flags. Every root must pass Expr.equal after a single table decode.
- `USAGE.lean.inc`: exporter and consumer integration examples. They show the specific A/B typed-entry boundary, not a new framework.

Interface in FoundationAudit:

```lean
structure ExprDagEncoder where
  nodes : Array Json := #[]
  index : Lean.ExprStructMap Nat := {}
abbrev ExprDagM := StateT ExprDagEncoder MetaM
partial def addExpr (e : Expr) : ExprDagM Nat
def decodeExprDag (dag : Json) : Except String (Array Expr)
def finishExprDag (encoder : ExprDagEncoder)
  (rootRefs : Array Nat) (originalRoots : Array Expr) : MetaM Json
```

`addExpr` interns actual Exprs with explicit ExprStructEq keys. Lean4.33.1's ExprStructEq.beq delegates to Expr.equal; ordinary BEq Expr is alpha equivalence and is not used as the map key. Binder Names, BinderInfo, nondependent let flags, constants, universe parameters including numeric Name components, projections and literals are stored in full. Bound variables are preserved. Free/metavariables and universe metavariables are rejected. Input roots must already be metadata-erased, as the existing replay contract requires; residual mdata is rejected without discarding data.

The JSON format is `{schema:"foundation-expr-dag-v1",nodes:[...],roots:[Nat...]}`. Each node uses the existing kind tags and field names; expression children are Nat references instead of recursive JSON. The encoder emits children first. The decoder builds one Expr table and validates each child against the completed prefix, so self, forward and out-of-range references fail. It validates every declared root reference. `finishExprDag` compares every original root with its decoded root using Expr.equal and refuses any mismatch before returning the artifact.

Use one encoder across all type/value roots in one A or B artifact. Preserve the existing complete per-entry originalName, params, replay method, axioms, full Binder provenance and kernel check fields; replace only expanded expression trees with typeRoot/valueRoot. Consumers decode each artifact once before their entry loop, then index the table with those references. A/B source hashes and actual CI receipts must bind the produced DAG; this codec does not weaken any kernel checks or establish a theorem by serialization alone.

The decoder's lam/forall/let/proj branches bind their fields with explicit lets and end in single-line constructor returns. This avoids the partial-return Lean layout error seen in earlier replay drafts. Codec size and resource improvements remain to be measured by root's MCP-CI jobs.
