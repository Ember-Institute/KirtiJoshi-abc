-- Insert inside namespace FoundationAudit, after checked and the existing
-- Name/Level/Binder codecs. Roots must already be metadata-erased.

structure ExprDagEncoder where
  nodes : Array Json := #[]
  index : Lean.ExprStructMap Nat := {}
  deriving Inhabited

abbrev ExprDagM := StateT ExprDagEncoder MetaM

/-- Intern by Expr.equal, which preserves binder Names and BinderInfo. -/
partial def addExpr (e : Expr) : ExprDagM Nat := do
  let initial ← get
  if let some ref := initial.index[(⟨e⟩ : ExprStructEq)]? then
    return ref
  let payload : Json ← match e with
    | .bvar i => pure (node "bvar" [("index", toJson i)])
    | .sort u => do
        let encoded ← liftM (checked (encodeLevel u))
        pure (node "sort" [("level", encoded)])
    | .const n us => do
        let levels ← liftM (checked (us.toArray.mapM encodeLevel))
        pure (node "const" [("name", encodeName n), ("levels", Json.arr levels)])
    | .app f a => do
        let fnRef ← addExpr f
        let argRef ← addExpr a
        pure (node "app" [("fn", toJson fnRef), ("arg", toJson argRef)])
    | .lam n t b bi => do
        let typeRef ← addExpr t
        let bodyRef ← addExpr b
        pure (node "lam" [("name", encodeName n), ("type", toJson typeRef),
          ("body", toJson bodyRef), ("binder", toJson (encodeBinder bi))])
    | .forallE n t b bi => do
        let typeRef ← addExpr t
        let bodyRef ← addExpr b
        pure (node "forall" [("name", encodeName n), ("type", toJson typeRef),
          ("body", toJson bodyRef), ("binder", toJson (encodeBinder bi))])
    | .letE n t v b nd => do
        let typeRef ← addExpr t
        let valueRef ← addExpr v
        let bodyRef ← addExpr b
        pure (node "let" [("name", encodeName n), ("type", toJson typeRef),
          ("value", toJson valueRef), ("body", toJson bodyRef), ("nondependent", toJson nd)])
    | .lit (.natVal n) => pure (node "nat" [("value", toJson n)])
    | .lit (.strVal s) => pure (node "string" [("value", toJson s)])
    | .proj n i b => do
        let bodyRef ← addExpr b
        pure (node "proj" [("name", encodeName n), ("index", toJson i), ("body", toJson bodyRef)])
    | .mdata _ _ => throwError "Expr DAG requires metadata-erased roots; metadata was not discarded"
    | .fvar _ => throwError "Free variable in Expr DAG input"
    | .mvar _ => throwError "Expression metavariable in Expr DAG input"
  let current ← get
  let ref := current.nodes.size
  set { current with nodes := current.nodes.push payload,
                     index := current.index.insert (⟨e⟩ : ExprStructEq) ref }
  return ref

/-- A child must refer to an already decoded node, never itself or a future node. -/
def exprDagChild (earlier : Array Expr) (entry : Json) (key : String) : Except String Expr := do
  let ref ← (← field entry key).getNat?
  match earlier[ref]? with
  | some e => pure e
  | none => throw s!"Expr DAG {key} reference {ref} is not earlier than node {earlier.size}"

/-- Decode one node using only the completed topological prefix. -/
def decodeExprDagNode (earlier : Array Expr) (entry : Json) : Except String Expr := do
  match ← stringField entry "kind" with
  | "bvar" => return .bvar (← (← field entry "index").getNat?)
  | "sort" => return .sort (← decodeLevel (← field entry "level"))
  | "const" =>
      let levels ← (← arrayField entry "levels").mapM decodeLevel
      return .const (← decodeName (← field entry "name")) levels.toList
  | "app" => return .app (← exprDagChild earlier entry "fn") (← exprDagChild earlier entry "arg")
  | "lam" =>
      let binderName ← decodeName (← field entry "name")
      let ty ← exprDagChild earlier entry "type"
      let body ← exprDagChild earlier entry "body"
      let binder ← decodeBinder (← stringField entry "binder")
      return .lam binderName ty body binder
  | "forall" =>
      let binderName ← decodeName (← field entry "name")
      let ty ← exprDagChild earlier entry "type"
      let body ← exprDagChild earlier entry "body"
      let binder ← decodeBinder (← stringField entry "binder")
      return .forallE binderName ty body binder
  | "let" =>
      let binderName ← decodeName (← field entry "name")
      let ty ← exprDagChild earlier entry "type"
      let value ← exprDagChild earlier entry "value"
      let body ← exprDagChild earlier entry "body"
      let nondependent ← (← field entry "nondependent").getBool?
      return .letE binderName ty value body nondependent
  | "nat" => return .lit (.natVal (← (← field entry "value").getNat?))
  | "string" => return .lit (.strVal (← (← field entry "value").getStr?))
  | "proj" =>
      let projectionName ← decodeName (← field entry "name")
      let index ← (← field entry "index").getNat?
      let body ← exprDagChild earlier entry "body"
      return .proj projectionName index body
  | other => throw s!"Unsupported Expr DAG node kind: {other}"

/-- Build the shared Expr table once and validate every declared root reference. -/
def decodeExprDag (dag : Json) : Except String (Array Expr) := do
  unless (← stringField dag "schema") == "foundation-expr-dag-v1" do
    throw "Unexpected Expr DAG schema"
  let entries ← arrayField dag "nodes"
  let mut decoded : Array Expr := #[]
  for entry in entries do
    decoded := decoded.push (← decodeExprDagNode decoded entry)
  for root in ← arrayField dag "roots" do
    let ref ← root.getNat?
    unless ref < decoded.size do
      throw s!"Expr DAG root reference {ref} is outside {decoded.size} nodes"
  return decoded

/-- Finalize only after one strict round trip for every original root. -/
def finishExprDag (encoder : ExprDagEncoder) (rootRefs : Array Nat)
    (originalRoots : Array Expr) : MetaM Json := do
  unless rootRefs.size == originalRoots.size do
    throwError "Expr DAG root references and original roots differ in count"
  let dag := Json.mkObj [("schema", toJson "foundation-expr-dag-v1"),
    ("nodes", Json.arr encoder.nodes), ("roots", toJson rootRefs)]
  let decoded ← checked (decodeExprDag dag)
  for i in [:rootRefs.size] do
    let ref := rootRefs[i]!
    let some actual := decoded[ref]? | throwError "Expr DAG root {i} is absent"
    unless Expr.equal originalRoots[i]! actual do
      throwError "Expr DAG strict Expr.equal round trip failed at root {i} (node {ref})"
  return dag
