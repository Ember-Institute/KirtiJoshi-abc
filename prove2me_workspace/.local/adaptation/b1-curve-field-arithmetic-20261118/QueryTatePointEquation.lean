import Lean
import TateCurvesTheta.TateCurve.TatePointOnCurve
import Solutions.Source_ReferenceIutTatePointEquation

namespace TatePointEquationAudit

open Lean Elab Term Meta

/- The Expr and Name encoders come from QueryTateAnalyticNativeFacts.lean. -/
partial def encodeName : Name → Json
  | .anonymous => Json.arr #[]
  | .str p s => Json.arr #[(encodeName p), Json.str "str", Json.str s]
  | .num p n => Json.arr #[(encodeName p), Json.str "num", toJson n]

def node (kind : String) (values : List (String × Json)) : Json :=
  Json.mkObj (("kind", Json.str kind) :: values)

partial def encodeLevel : Level → Except String Json
  | .zero => return node "zero" []
  | .succ u => return node "succ" [("arg", ← encodeLevel u)]
  | .max u v => return node "max" [("left", ← encodeLevel u), ("right", ← encodeLevel v)]
  | .imax u v => return node "imax" [("left", ← encodeLevel u), ("right", ← encodeLevel v)]
  | .param n => return node "param" [("name", encodeName n)]
  | .mvar _ => throw "Universe metavariable in compiler type"

def encodeBinder : BinderInfo → String
  | .default => "default"
  | .implicit => "implicit"
  | .strictImplicit => "strictImplicit"
  | .instImplicit => "instImplicit"

partial def encodeExpr : Expr → Except String Json
  | .bvar i => return node "bvar" [("index", toJson i)]
  | .sort u => return node "sort" [("level", ← encodeLevel u)]
  | .const n us => return node "const" [("name", encodeName n),
      ("levels", Json.arr (← us.toArray.mapM encodeLevel))]
  | .app f a => return node "app" [("fn", ← encodeExpr f), ("arg", ← encodeExpr a)]
  | .lam n t b bi => return node "lam" [("name", encodeName n),
      ("type", ← encodeExpr t), ("body", ← encodeExpr b), ("binder", toJson (encodeBinder bi))]
  | .forallE n t b bi => return node "forall" [("name", encodeName n),
      ("type", ← encodeExpr t), ("body", ← encodeExpr b), ("binder", toJson (encodeBinder bi))]
  | .letE n t v b nd => return node "let" [("name", encodeName n),
      ("type", ← encodeExpr t), ("value", ← encodeExpr v), ("body", ← encodeExpr b),
      ("nondependent", toJson nd)]
  | .lit (.natVal n) => return node "nat" [("value", toJson n)]
  | .lit (.strVal s) => return node "string" [("value", toJson s)]
  | .mdata _ b => encodeExpr b
  | .proj n i b => return node "proj" [("name", encodeName n), ("index", toJson i),
      ("body", ← encodeExpr b)]
  | .fvar _ => throw "Free variable in compiler declaration type"
  | .mvar _ => throw "Expression metavariable in compiler declaration type"

def checked {α : Type} (x : Except String α) : MetaM α :=
  match x with
  | .ok a => pure a
  | .error e => throwError "{e}"

def absoluteEnv (key : String) : MetaM String := do
  let some p ← IO.getEnv key | throwError "Missing environment variable {key}"
  unless p.startsWith "/" do throwError "Expected absolute path: {key}"
  return p

def moduleOf (env : Environment) (name : Name) : Option Name := do
  let index ← env.getModuleIdxFor? name
  env.header.moduleNames[index.toNat]?

def standardAxioms : Array Name := #[`propext, `Classical.choice, `Quot.sound]

def ensureStandard (label : String) (axs : Array Name) : MetaM Unit := do
  for ax in axs do
    unless standardAxioms.contains ax do throwError "Unexpected axiom in {label}: {ax}"

def kind (ci : ConstantInfo) : String := match ci with
  | .axiomInfo _ => "axiom" | .defnInfo _ => "definition" | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque" | .quotInfo _ => "quotient"
  | .inductInfo _ => "inductive" | .ctorInfo _ => "constructor" | .recInfo _ => "recursor"

def telescopeJson (type : Expr) : MetaM Json :=
  forallTelescope type fun xs result => do
    let binders ← xs.mapM fun x => do
      let d ← x.fvarId!.getDecl
      return Json.mkObj [("name", toJson d.userName.toString),
        ("binderInfo", toJson (encodeBinder d.binderInfo)),
        ("typeDisplay", toJson (← ppExpr d.type).pretty)]
    return Json.mkObj [("binders", Json.arr binders),
      ("resultDisplay", toJson (← ppExpr result).pretty)]

def requireClosed (label : String) (e : Expr) : MetaM Unit := do
  if e.hasMVar || e.hasFVar || e.hasLooseBVars then throwError "Open actual Expr {label}"

def checkedValueType (label : String) (value type : Expr) : MetaM Expr := do
  requireClosed label value
  requireClosed s!"TYPE of {label}" type
  let inferred ← match Kernel.check (← getEnv) {} value with
    | .ok t => pure t
    | .error ex => throwKernelException ex
  match Kernel.isDefEq (← getEnv) {} inferred type with
  | .ok true => pure ()
  | .ok false => throwError "Kernel actual value/TYPE mismatch {label}"
  | .error ex => throwKernelException ex
  return inferred

def sourceName : Name := `TateCurvesTheta.TateParameter.tatePoint_mem'
def targetName : Name :=
  `AbcAdaptation.Reference.TateCurvesTheta.TateParameter.tatePoint_equation
def targetProposition : Name :=
  `AbcAdaptation.Reference.TateCurvesTheta.TateParameter.TatePointEquation

def namesJson (names : Array Name) : Json :=
  Json.arr ((names.qsort Name.lt).map encodeName)

def valueOf (ci : ConstantInfo) : MetaM Expr := do
  let some value := ci.value? (allowOpaque := true) |
    throwError "Missing value for {ci.name}"
  return value

def rootFact (ci : ConstantInfo) (owner : Name) (expectedKind : String) : MetaM Json := do
  unless moduleOf (← getEnv) ci.name == some owner && kind ci == expectedKind do
    throwError "Unexpected owner or kind for {ci.name}"
  let value ← valueOf ci
  let _ ← checkedValueType ci.name.toString value ci.type
  let axioms ← collectAxioms ci.name
  ensureStandard ci.name.toString axioms
  return Json.mkObj [
    ("name", encodeName ci.name), ("owner", encodeName owner), ("kind", toJson expectedKind),
    ("levelParams", Json.arr (ci.levelParams.toArray.map encodeName)),
    ("actualTypeExpr", ← checked (encodeExpr ci.type)),
    ("actualValueExpr", ← checked (encodeExpr value)),
    ("telescope", ← telescopeJson ci.type),
    ("directTypeConstants", namesJson ci.type.getUsedConstants),
    ("directValueConstants", namesJson value.getUsedConstants),
    ("axioms", toJson ((axioms.qsort Name.lt).map Name.toString)),
    ("kernelValueTypeMatchesActualTYPE", toJson true)]

def relocateTateName (n : Name) : Name :=
  n.replacePrefix `TateCurvesTheta `AbcAdaptation.Reference.TateCurvesTheta

partial def relocateTateType (type : Expr) : Expr :=
  type.replace fun
    | .const name levels =>
      if Name.isPrefixOf `TateCurvesTheta name then some (.const (relocateTateName name) levels)
      else none
    | .proj name index body =>
      if Name.isPrefixOf `TateCurvesTheta name then
        some (.proj (relocateTateName name) index (relocateTateType body))
      else none
    | _ => none

/-- Unfold the local equation proposition and match the upstream unit and characteristic binders. -/
def compareType (source target : ConstantInfo) : MetaM Json := do
  unless source.levelParams.length == target.levelParams.length do
    throwError "Different universe parameter counts for the point equation"
  let sourceType := relocateTateType
    (source.type.instantiateLevelParams source.levelParams (target.levelParams.map Level.param))
  let order ← forallTelescope sourceType fun xs _ => do
    unless xs.size == 8 do throwError "Expected eight upstream point equation binders"
    let u ← xs[5]!.fvarId!.getDecl
    if u.userName == `u then return #[0, 1, 2, 3, 4, 6, 5, 7]
    unless u.userName == `h12 do throwError "Unexpected upstream point equation binder order"
    return #[0, 1, 2, 3, 4, 5, 6, 7]
  withTransparency .all <| forallTelescopeReducing target.type fun xs targetBody => do
    unless xs.size == 8 do throwError "Expected eight expanded local point equation binders"
    let mut sourceBody := sourceType
    for index in order do
      let .forallE _ domain next info := sourceBody |
        throwError "Source type ended before local point equation binders"
      let targetBinder ← xs[index]!.fvarId!.getDecl
      let expectedBinder := if index == 6 then BinderInfo.implicit else targetBinder.binderInfo
      unless info == expectedBinder do throwError "Binder kind differs at index {index}"
      unless ← isDefEq domain targetBinder.type do
        throwError "Binder type differs at index {index}"
      sourceBody := next.instantiate1 xs[index]!
    unless ← isDefEq sourceBody targetBody do
      throwError "Point equation result types differ after relocation"
    return Json.mkObj [
      ("upstreamBinderOrderAsTargetIndices", toJson order),
      ("localPropositionUnfolded", toJson true),
      ("mappedBindersAndResultDefinitionallyEqual", toJson true)]

/-- Follow actual type and value dependencies owned by the Tate library. -/
def sourceGraph (root : Name) : MetaM (Array Json) := do
  let env ← getEnv
  let isTate := fun name => (moduleOf env name).any (Name.isPrefixOf `TateCurvesTheta ·)
  let mut work := [root]
  let mut seen : Std.HashSet Name := {}
  let mut records := #[]
  while let name :: rest := work do
    work := rest
    if seen.contains name then continue
    seen := seen.insert name
    let ci ← getConstInfo name
    let some owner := moduleOf env name | throwError "Missing module for {name}"
    let typeDeps := ci.type.getUsedConstants
    let valueDeps := match ci with
      | .recInfo r => r.rules.toArray.flatMap (fun rule => rule.rhs.getUsedConstants)
      | _ => (ci.value? (allowOpaque := true)).map Expr.getUsedConstants |>.getD #[]
    let constructors := match ci with
      | .inductInfo i => i.ctors.toArray
      | _ => #[]
    let pending := ((typeDeps ++ valueDeps ++ constructors).filter isTate).qsort Name.lt
    work := pending.toList ++ work
    records := records.push (Json.mkObj [
      ("name", encodeName name), ("owner", encodeName owner), ("kind", toJson (kind ci)),
      ("typeConstants", namesJson typeDeps), ("valueConstants", namesJson valueDeps),
      ("constructors", namesJson constructors)])
  return records

run_meta do
  unless Lean.versionString == "4.33.1" do throwError "Expected Lean 4.33.1"
  let source ← getConstInfo sourceName
  let target ← getConstInfo targetName
  let proposition ← getConstInfo targetProposition
  let facts ← #[
      (source, `TateCurvesTheta.TateCurve.TatePointOnCurve, "theorem"),
      (target, `Solutions.Source_ReferenceIutTatePointEquation, "theorem"),
      (proposition, `Solutions.Source_ReferenceIutTateUniformization, "definition")
    ].mapM (fun (ci, owner, expectedKind) => rootFact ci owner expectedKind)
  let comparison ← compareType source target
  let graph ← sourceGraph sourceName
  let output ← absoluteEnv "P2M_TATE_POINT_EQUATION_FACTS"
  IO.FS.writeFile output ((Json.mkObj [
    ("schema", toJson "tate-point-equation-native-facts/v1"),
    ("compilerVersion", toJson Lean.versionString),
    ("facts", Json.arr facts), ("comparison", comparison),
    ("sourceGraph", Json.arr graph)]).compress ++ "\n")
  logInfo m!"Point equation type and standard axioms verified. Recorded {graph.size} Tate declarations."

end TatePointEquationAudit
