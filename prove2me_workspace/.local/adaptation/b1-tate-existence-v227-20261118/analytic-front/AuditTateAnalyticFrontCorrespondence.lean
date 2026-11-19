import Lean
import Definitions.Def_AbcAdaptation_Reference_TateCurvesTheta_TateCurve_EisensteinSummability
import Definitions.Def_AbcAdaptation_Reference_TateCurvesTheta_TateCurve_A6Coefficients

namespace FoundationAudit
open Lean

def field (j : Json) (key : String) : Except String Json := j.getObjVal? key
def stringField (j : Json) (key : String) : Except String String := do
  (← field j key).getStr?
def arrayField (j : Json) (key : String) : Except String (Array Json) := do
  (← field j key).getArr?

-- Preserve actual Name components, including numeric components; do not use String.toName.
partial def encodeName : Name → Json
  | .anonymous => Json.arr #[]
  | .str p s => Json.arr #[(encodeName p), Json.str "str", Json.str s]
  | .num p n => Json.arr #[(encodeName p), Json.str "num", toJson n]

partial def decodeName (j : Json) : Except String Name := do
  let a ← j.getArr?
  if a.isEmpty then return .anonymous
  unless a.size == 3 do throw "Invalid Name JSON"
  let p ← decodeName a[0]!
  match ← a[1]!.getStr? with
  | "str" => return .str p (← a[2]!.getStr?)
  | "num" => return .num p (← a[2]!.getNat?)
  | _ => throw "Invalid Name component"

def node (kind : String) (values : List (String × Json)) : Json :=
  Json.mkObj (("kind", Json.str kind) :: values)

partial def encodeLevel : Level → Except String Json
  | .zero => return node "zero" []
  | .succ u => return node "succ" [("arg", ← encodeLevel u)]
  | .max u v => return node "max" [("left", ← encodeLevel u), ("right", ← encodeLevel v)]
  | .imax u v => return node "imax" [("left", ← encodeLevel u), ("right", ← encodeLevel v)]
  | .param n => return node "param" [("name", encodeName n)]
  | .mvar _ => throw "Universe metavariable in compiler type"

partial def decodeLevel (j : Json) : Except String Level := do
  match ← stringField j "kind" with
  | "zero" => return .zero
  | "succ" => return .succ (← decodeLevel (← field j "arg"))
  | "max" => return .max (← decodeLevel (← field j "left")) (← decodeLevel (← field j "right"))
  | "imax" => return .imax (← decodeLevel (← field j "left")) (← decodeLevel (← field j "right"))
  | "param" => return .param (← decodeName (← field j "name"))
  | k => throw s!"Unknown universe kind: {k}"

def encodeBinder : BinderInfo → String
  | .default => "default"
  | .implicit => "implicit"
  | .strictImplicit => "strictImplicit"
  | .instImplicit => "instImplicit"

def decodeBinder : String → Except String BinderInfo
  | "default" => return .default
  | "implicit" => return .implicit
  | "strictImplicit" => return .strictImplicit
  | "instImplicit" => return .instImplicit
  | k => throw s!"Unknown binder info: {k}"

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

open Lean Elab Term Meta

def checked {α : Type} (x : Except String α) : MetaM α :=
  match x with
  | .ok a => pure a
  | .error e => throwError "{e}"

def namesFromJson (j : Json) : MetaM (List Name) := do
  return (← checked ((← checked j.getArr?).mapM decodeName)).toList

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

abbrev AxiomCache := IO.Ref (Std.HashMap Name (Array Name))

-- The imported source environment is stable throughout this one export run.
-- Cache only successful collectAxioms results; errors still propagate normally.
def cachedAxioms (cache : AxiomCache) (name : Name) : MetaM (Array Name) := do
  if let some axs := (← cache.get)[name]? then return axs
  let axs ← collectAxioms name
  cache.modify fun entries => entries.insert name axs
  return axs

def expressionAxioms (cache : AxiomCache) (e : Expr) : MetaM (Array Name) := do
  let mut axs : Array Name := #[]
  for name in e.getUsedConstants do
    for ax in ← cachedAxioms cache name do
      unless axs.contains ax do axs := axs.push ax
  return axs.qsort Name.lt

def kind (ci : ConstantInfo) : String := match ci with
  | .axiomInfo _ => "axiom" | .defnInfo _ => "definition" | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque" | .quotInfo _ => "quotient"
  | .inductInfo _ => "inductive" | .ctorInfo _ => "constructor" | .recInfo _ => "recursor"

end FoundationAudit

namespace TateAnalyticSupplementReview
open Lean Elab Term Meta FoundationAudit

def relocateName (n : Name) : Except String Name := do
  if Name.isPrefixOf `TateCurvesTheta n then
    return n.replacePrefix `TateCurvesTheta `AbcAdaptation.Reference.TateCurvesTheta
  if #[`Iut, `Genl, `AbcAdaptation, `_private].any (·.isPrefixOf n) then
    throw s!"Unmapped project constant {n}"
  return n

-- Decode the source Expr while preserving its binders and universe arguments.
-- Mathlib names retain their source spellings for target-kernel conversion.
partial def relocateExpr (j : Json) : Except String Expr := do
  let recur := relocateExpr
  let relocate := relocateName
  match ← stringField j "kind" with
  | "bvar" => return .bvar (← (← field j "index").getNat?)
  | "sort" => return .sort (← decodeLevel (← field j "level"))
  | "const" =>
    let n ← decodeName (← field j "name")
    let us ← (← arrayField j "levels").mapM decodeLevel
    return .const (← relocate n) us.toList
  | "app" => return .app (← recur (← field j "fn")) (← recur (← field j "arg"))
  | "lam" => return .lam (← decodeName (← field j "name")) (← recur (← field j "type")) (← recur (← field j "body")) (← decodeBinder (← stringField j "binder"))
  | "forall" => return .forallE (← decodeName (← field j "name")) (← recur (← field j "type")) (← recur (← field j "body")) (← decodeBinder (← stringField j "binder"))
  | "let" => return .letE (← decodeName (← field j "name")) (← recur (← field j "type")) (← recur (← field j "value")) (← recur (← field j "body")) (← (← field j "nondependent").getBool?)
  | "nat" => return .lit (.natVal (← (← field j "value").getNat?))
  | "string" => return .lit (.strVal (← stringField j "value"))
  | "proj" => return .proj (← relocate (← decodeName (← field j "name"))) (← (← field j "index").getNat?) (← recur (← field j "body"))
  | k => throw s!"Unsupported actual Expr kind {k}"

def requireClosed (label : String) (e : Expr) : MetaM Unit := do
  if e.hasMVar || e.hasFVar || e.hasLooseBVars then throwError "Open expression {label}"

def kernelCheck (label : String) (e : Expr) : MetaM Expr := do
  requireClosed label e
  match Kernel.check (← getEnv) {} e with
  | .ok t => return t
  | .error ex => throwKernelException ex

def kernelEq (label : String) (e f : Expr) : MetaM Unit := do
  let et ← kernelCheck label e
  let ft ← kernelCheck label f
  for (a,b) in #[(et,ft),(e,f)] do
    match Kernel.isDefEq (← getEnv) {} a b with
    | .ok true => pure ()
    | .ok false => throwError "Kernel inequality {label}"
    | .error ex => throwKernelException ex

partial def binderPlacement (e : Expr) (path := "root") : Array String :=
  match e with
  | .forallE _ t b bi => #[path ++ ":forall:" ++ encodeBinder bi] ++ binderPlacement t (path ++ ".type") ++ binderPlacement b (path ++ ".body")
  | .lam _ t b bi => #[path ++ ":lambda:" ++ encodeBinder bi] ++ binderPlacement t (path ++ ".type") ++ binderPlacement b (path ++ ".body")
  | .app f a => binderPlacement f (path ++ ".function") ++ binderPlacement a (path ++ ".argument")
  | .letE _ t v b _ => binderPlacement t (path ++ ".type") ++ binderPlacement v (path ++ ".value") ++ binderPlacement b (path ++ ".body")
  | .mdata _ e => binderPlacement e path
  | .proj _ _ e => binderPlacement e (path ++ ".projected")
  | _ => #[]

def constantDifferences (source target : Expr) : Json :=
  let sourceNames := source.getUsedConstants.qsort Name.lt
  let targetNames := target.getUsedConstants.qsort Name.lt
  Json.mkObj [
    ("mappedSourceOnly", toJson ((sourceNames.filter (fun n => !targetNames.contains n)).map Name.toString)),
    ("targetOnly", toJson ((targetNames.filter (fun n => !sourceNames.contains n)).map Name.toString))]

def sourceAxioms (row : Json) (key : String) : MetaM (Array String) := do
  let recorded ← checked (row.getObjValAs? (Array String) key)
  let allowed := standardAxioms.map Name.toString
  unless recorded.all (allowed.contains ·) do
    throwError "Unexpected source axioms in {key}: {recorded}"
  return recorded

end TateAnalyticSupplementReview

namespace TateAnalyticFrontReview
open Lean Elab Term Meta FoundationAudit TateAnalyticSupplementReview

structure Expected where
  source : Name
  sourceOwner : Name
  targetOwner : Name
  kind : String
  deriving Inhabited

def groups : Array (String × Array Expected) := #[
  ("B1_TATE_ANALYTIC_SUMMABILITY_FACTS", #[
    ⟨`TateCurvesTheta.TateParameter.eisenstein_summand_summable,
      `TateCurvesTheta.TateCurve.Weierstrass,
      `Definitions.Def_AbcAdaptation_Reference_TateCurvesTheta_TateCurve_EisensteinSummability, "theorem"⟩,
    ⟨`TateCurvesTheta.TateParameter.norm_one_sub_qpow,
      `TateCurvesTheta.TateCurve.Weierstrass,
      `Definitions.Def_AbcAdaptation_Reference_TateCurvesTheta_TateCurve_EisensteinSummability, "theorem"⟩,
    ⟨`TateCurvesTheta.TateParameter.one_sub_qpow_ne_zero,
      `TateCurvesTheta.TateCurve.Weierstrass,
      `Definitions.Def_AbcAdaptation_Reference_TateCurvesTheta_TateCurve_EisensteinSummability, "theorem"⟩
  ]),
  ("B1_TATE_ANALYTIC_A6COEFFICIENTS_FACTS", #[
    ⟨`TateCurvesTheta.a₆Coeff,
      `TateCurvesTheta.TateCurve.A6Series,
      `Definitions.Def_AbcAdaptation_Reference_TateCurvesTheta_TateCurve_A6Coefficients, "definition"⟩,
    ⟨`TateCurvesTheta.TateParameter.qFactor,
      `TateCurvesTheta.TateCurve.A6Series,
      `Definitions.Def_AbcAdaptation_Reference_TateCurvesTheta_TateCurve_A6Coefficients, "definition"⟩,
    ⟨`TateCurvesTheta.a₆Coeff_zero,
      `TateCurvesTheta.TateCurve.A6Series,
      `Definitions.Def_AbcAdaptation_Reference_TateCurvesTheta_TateCurve_A6Coefficients, "theorem"⟩,
    ⟨`TateCurvesTheta.TateParameter.eisenstein_eq_tsum_qFactor,
      `TateCurvesTheta.TateCurve.A6Series,
      `Definitions.Def_AbcAdaptation_Reference_TateCurvesTheta_TateCurve_A6Coefficients, "theorem"⟩,
    ⟨`TateCurvesTheta.TateParameter.term_combo,
      `TateCurvesTheta.TateCurve.A6Series,
      `Definitions.Def_AbcAdaptation_Reference_TateCurvesTheta_TateCurve_A6Coefficients, "theorem"⟩,
    ⟨`TateCurvesTheta.twelve_mul_a₆Coeff,
      `TateCurvesTheta.TateCurve.A6Series,
      `Definitions.Def_AbcAdaptation_Reference_TateCurvesTheta_TateCurve_A6Coefficients, "theorem"⟩,
    ⟨`TateCurvesTheta.twelve_dvd_five_mul_cube_add_seven_mul_pow,
      `TateCurvesTheta.TateCurve.A6Series,
      `Definitions.Def_AbcAdaptation_Reference_TateCurvesTheta_TateCurve_A6Coefficients, "theorem"⟩
  ]),
  ("B1_TATE_ANALYTIC_GENERATED_FACTS", #[
    ⟨`TateCurvesTheta.TateParameter.eisenstein.eq_1,
      `TateCurvesTheta.TateCurve.A6Series,
      `Definitions.Def_AbcAdaptation_Reference_TateCurvesTheta_TateCurve_A6Coefficients, "theorem"⟩,
    ⟨`TateCurvesTheta.TateParameter.qFactor.eq_1,
      `TateCurvesTheta.TateCurve.A6Series,
      `Definitions.Def_AbcAdaptation_Reference_TateCurvesTheta_TateCurve_A6Coefficients, "theorem"⟩
  ])
]

def checkType (cache : AxiomCache) (row : Json) (ci : ConstantInfo) : MetaM Json := do
  let universes ← namesFromJson (← checked (field row "levelParams"))
  unless universes == ci.levelParams do
    throwError "Named universe parameter order differs for {ci.name}"
  let sourceType ← checked (relocateExpr (← checked (field row "actualTypeExpr")))
  unless binderPlacement sourceType == binderPlacement ci.type do
    throwError "Type binder placement differs for {ci.name}"
  kernelEq s!"full type {ci.name}" sourceType ci.type
  let mappedSourceAxioms ← expressionAxioms cache sourceType
  let targetAxioms ← expressionAxioms cache ci.type
  ensureStandard ci.name.toString mappedSourceAxioms
  ensureStandard ci.name.toString targetAxioms
  return Json.mkObj [
    ("kernelDefinitionalEquality", toJson true),
    ("levelParams", toJson (universes.map Name.toString)),
    ("binderPlacement", toJson (binderPlacement ci.type)),
    ("mappedSourceExpr", ← checked (encodeExpr sourceType)),
    ("targetExpr", ← checked (encodeExpr ci.type)),
    ("directConstantDifferences", constantDifferences sourceType ci.type),
    ("mappedSourceAxioms", toJson (mappedSourceAxioms.map Name.toString)),
    ("targetAxioms", toJson (targetAxioms.map Name.toString))]

def checkValue (cache : AxiomCache) (row : Json) (ci : ConstantInfo) : MetaM Json := do
  let some targetValue := ci.value? (allowOpaque := true) | throwError "Missing value for {ci.name}"
  let sourceValue ← checked (relocateExpr (← checked (field row "actualValueExpr")))
  let sourceValueType ← kernelCheck s!"mapped source value {ci.name}" sourceValue
  let targetValueType ← kernelCheck s!"actual target value {ci.name}" targetValue
  kernelEq s!"mapped source value at the full target type {ci.name}" sourceValueType ci.type
  kernelEq s!"native value at the full target type {ci.name}" targetValueType ci.type
  match Kernel.isDefEq (← getEnv) {} sourceValue targetValue with
  | .ok true => pure ()
  | .ok false => throwError "Complete value differs for {ci.name}"
  | .error ex => throwKernelException ex
  let mappedSourceAxioms ← expressionAxioms cache sourceValue
  let targetAxioms ← expressionAxioms cache targetValue
  ensureStandard ci.name.toString mappedSourceAxioms
  ensureStandard ci.name.toString targetAxioms
  return Json.mkObj [
    ("bothValuesCheckAtTargetType", toJson true),
    ("kernelDefinitionalEquality", toJson true),
    ("directConstantDifferences", constantDifferences sourceValue targetValue),
    ("mappedSourceAxioms", toJson (mappedSourceAxioms.map Name.toString)),
    ("targetAxioms", toJson (targetAxioms.map Name.toString))]

def attempt (action : MetaM Json) : MetaM (Bool × Json) := do
  try
    return (true, ← action)
  catch e =>
    return (false, Json.mkObj [("diagnostic", toJson (← e.toMessageData.toString))])

def compare (cache : AxiomCache) (row : Json) (expected : Expected) : MetaM (Bool × Json) := do
  let actualName ← checked (decodeName (← checked (field row "nameExpr")))
  let actualOwner ← checked (decodeName (← checked (field row "ownerNameExpr")))
  unless actualName == expected.source && actualOwner == expected.sourceOwner do
    throwError "Unexpected source record {actualName} in {actualOwner}"
  unless (← checked (stringField row "record")) == "fullActualFact" &&
      (← checked (stringField row "kind")) == expected.kind &&
      (← checked (row.getObjValAs? Bool "valueRead")) &&
      (← checked (row.getObjValAs? Bool "kernelValueTypeMatchesActualTYPE")) &&
      !(← checked (row.getObjValAs? Bool "hasSorryAx")) do
    throwError "Incomplete source evidence for {actualName}"
  let declarationAxioms ← sourceAxioms row "axioms"
  let typeAxioms ← sourceAxioms row "typeAxioms"
  let valueAxioms ← sourceAxioms row "valueAxioms"
  let targetName ← checked (relocateName actualName)
  let ci ← getConstInfo targetName
  unless moduleOf (← getEnv) targetName == some expected.targetOwner && kind ci == expected.kind do
    throwError "Unexpected target declaration or owner for {targetName}"
  let nativeAxioms ← cachedAxioms cache targetName
  ensureStandard targetName.toString nativeAxioms
  let (typePassed, typeResult) ← attempt (checkType cache row ci)
  let (valuePassed, valueResult) ←
    if typePassed then attempt (checkValue cache row ci) else pure (false, Json.null)
  logInfo m!"{targetName} has standard axioms {(nativeAxioms.qsort Name.lt).map Name.toString}"
  return (typePassed && valuePassed, Json.mkObj [
    ("source", toJson actualName.toString),
    ("sourceOwner", toJson actualOwner.toString),
    ("target", toJson targetName.toString),
    ("targetOwner", toJson expected.targetOwner.toString),
    ("kind", toJson expected.kind),
    ("typePassed", toJson typePassed), ("type", typeResult),
    ("valuePassed", toJson valuePassed), ("value", valueResult),
    ("sourceAxioms", toJson declarationAxioms),
    ("sourceTypeAxioms", toJson typeAxioms),
    ("sourceValueAxioms", toJson valueAxioms),
    ("targetAxioms", toJson ((nativeAxioms.qsort Name.lt).map Name.toString))])

run_meta do
  unless Lean.versionString == "4.33.1" do throwError "Expected Lean 4.33.1"
  let output ← absoluteEnv "B1_TATE_ANALYTIC_FRONT_COMPARISON"
  let cache ← IO.mkRef ({} : Std.HashMap Name (Array Name))
  let mut records : Array Json := #[]
  let mut failures : Array Name := #[]
  for (envKey, expected) in groups do
    let lines ← IO.FS.lines (← absoluteEnv envKey)
    unless lines.size == expected.size do
      throwError "Unexpected number of archived records at {envKey}"
    for k in [:lines.size] do
      let row ← checked (Json.parse lines[k]!)
      let (passed, evidence) ← compare cache row expected[k]!
      unless passed do failures := failures.push expected[k]!.source
      records := records.push evidence
  let report := Json.mkObj [
    ("schema", toJson "b1-tate-analytic-front-comparison/v1"),
    ("compilerVersion", toJson Lean.versionString),
    ("sourceCompilerVersion", toJson "4.35.0-rc3"),
    ("projectNamespaceMap", toJson "TateCurvesTheta → AbcAdaptation.Reference.TateCurvesTheta"),
    ("mathlibNameMap", toJson "identity"),
    ("records", Json.arr records),
    ("failedSources", toJson (failures.map Name.toString))]
  IO.FS.writeFile output (report.compress ++ "\n")
  unless failures.isEmpty do
    throwError "Tate analytic correspondence failed for {failures} in {output}"
  logInfo m!"Full types, values, and standard axioms passed for {records.size} declarations"

end TateAnalyticFrontReview
