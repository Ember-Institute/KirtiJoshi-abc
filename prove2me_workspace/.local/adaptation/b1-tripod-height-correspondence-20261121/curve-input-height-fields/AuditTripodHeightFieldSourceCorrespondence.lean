import Lean
import Solutions.Source_TripodCurveInputs
import Solutions.Source_TripodCurveInputsHeightFields

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

end FoundationAudit

namespace TripodHeightFieldExpressionComparison
open Lean Elab Term Meta FoundationAudit

def relocateName (maps : Array (Name × Name)) (n : Name) : Except String Name := do
  if let some pair := maps.find? (fun pair => pair.1 == n) then
    return pair.2
  if #[`Iut, `Genl, `TateCurvesTheta, `AbcAdaptation, `_private].any (·.isPrefixOf n) then
    throw s!"Unmapped project constant {n}"
  return n

-- Decode the source Expr while preserving its binders and universe arguments.
-- Mathlib names retain their source spellings for target-kernel conversion.
partial def relocateExpr (maps : Array (Name × Name)) (j : Json) : Except String Expr := do
  let recur := relocateExpr maps
  let relocate := relocateName maps
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

partial def outerBinderPlacement (e : Expr) : Array String :=
  match e with
  | .forallE _ _ body binder => #[encodeBinder binder] ++ outerBinderPlacement body
  | .mdata _ body => outerBinderPlacement body
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

end TripodHeightFieldExpressionComparison


namespace TripodHeightFieldSourceCorrespondence
open Lean Elab Term Meta FoundationAudit TripodHeightFieldExpressionComparison

structure Expected where
  source : Name
  sourceOwner : Name
  target : Name
  targetOwner : Name
  kind : String
  provenance : String
  referenceLine : Nat

def expectedPairs (config : Json) : MetaM (Array Expected) := do
  (← checked (arrayField config "pairs")).mapM fun item => do
    let source ← checked (decodeName (← checked (field item "source")))
    let sourceOwner ← checked (decodeName (← checked (field item "sourceOwner")))
    let target ← checked (decodeName (← checked (field item "target")))
    let targetOwner ← checked (decodeName (← checked (field item "targetOwner")))
    let kind ← checked (stringField item "kind")
    let provenance ← checked (stringField item "provenance")
    let referenceLine ← checked (item.getObjValAs? Nat "referenceLine")
    return { source, sourceOwner, target, targetOwner, kind, provenance, referenceLine }

def auditConstants (label : String) (expression : Expr) : MetaM Unit := do
  let env ← getEnv
  let missing := expression.getUsedConstants.filter fun name => (env.find? name).isNone
  unless missing.isEmpty do
    throwError "{label}: missing target constants {missing.qsort Name.lt}"

structure NativeField where
  name : Name
  type : Expr
  value : Expr
  rhs : Expr
  closedValue : Expr
  closedTheorem : Name

def checkType (cache : AxiomCache) (maps : Array (Name × Name)) (row : Json)
    (native : NativeField) : MetaM Json := do
  let universes ← namesFromJson (← checked (field row "levelParams"))
  unless universes.isEmpty do
    throwError "Named universe parameter order differs for {native.name}"
  let originalSourceType ← checked (field row "actualTypeExpr")
  let sourceType ← checked (relocateExpr maps originalSourceType)
  auditConstants "Mapped source type" sourceType
  let sourceBinders := binderPlacement sourceType
  let targetBinders := binderPlacement native.type
  unless outerBinderPlacement sourceType == outerBinderPlacement native.type do
    throwError "Outer type binder modes differ for {native.name}"
  kernelEq s!"full type {native.name}" sourceType native.type
  let mappedSourceAxioms ← expressionAxioms cache sourceType
  let targetAxioms ← expressionAxioms cache native.type
  ensureStandard native.name.toString mappedSourceAxioms
  ensureStandard native.name.toString targetAxioms
  return Json.mkObj [
    ("kernelDefinitionalEquality", toJson true),
    ("levelParams", toJson (universes.map Name.toString)),
    ("outerBinderPlacement", toJson (outerBinderPlacement native.type)),
    ("rawBinderPlacementMatches", toJson (sourceBinders == targetBinders)),
    ("sourceBinderPlacement", toJson sourceBinders),
    ("targetBinderPlacement", toJson targetBinders),
    ("originalSourceExpr", originalSourceType),
    ("mappedSourceExpr", ← checked (encodeExpr sourceType)),
    ("targetExpr", ← checked (encodeExpr native.type)),
    ("directConstantDifferences", constantDifferences sourceType native.type),
    ("mappedSourceAxioms", toJson (mappedSourceAxioms.map Name.toString)),
    ("targetAxioms", toJson (targetAxioms.map Name.toString))]

def checkValue (cache : AxiomCache) (maps : Array (Name × Name)) (row : Json)
    (native : NativeField) : MetaM Json := do
  let targetValue := native.value
  let originalSourceValue ← checked (field row "actualValueExpr")
  let sourceValue ← checked (relocateExpr maps originalSourceValue)
  auditConstants "Mapped source proof" sourceValue
  let sourceValueType ← kernelCheck s!"mapped source value {native.name}" sourceValue
  let targetValueType ← kernelCheck s!"actual target value {native.name}" targetValue
  kernelEq s!"mapped source value at the full target type {native.name}" sourceValueType native.type
  kernelEq s!"native value at the full target type {native.name}" targetValueType native.type
  match Kernel.isDefEq (← getEnv) {} sourceValue targetValue with
  | .ok true => pure ()
  | .ok false => throwError "Complete value differs for {native.name}"
  | .error ex => throwKernelException ex
  let mappedSourceAxioms ← expressionAxioms cache sourceValue
  let targetAxioms ← expressionAxioms cache targetValue
  ensureStandard native.name.toString mappedSourceAxioms
  ensureStandard native.name.toString targetAxioms
  return Json.mkObj [
    ("bothValuesCheckAtTargetType", toJson true),
    ("kernelDefinitionalEquality", toJson true),
    ("sourceValueMatchesTargetExpr", toJson (sourceValue == targetValue)),
    ("originalSourceExpr", originalSourceValue),
    ("mappedSourceExpr", ← checked (encodeExpr sourceValue)),
    ("targetExpr", ← checked (encodeExpr targetValue)),
    ("targetRhsExpr", ← checked (encodeExpr native.rhs)),
    ("directConstantDifferences", constantDifferences sourceValue targetValue),
    ("mappedSourceAxioms", toJson (mappedSourceAxioms.map Name.toString)),
    ("targetAxioms", toJson (targetAxioms.map Name.toString))]

def attempt (action : MetaM Json) : MetaM (Bool × Json) := do
  try
    return (true, ← action)
  catch e =>
    return (false, Json.mkObj [("diagnostic", toJson (← e.toMessageData.toString))])

def compare (cache : AxiomCache) (maps : Array (Name × Name)) (row : Json)
    (expected : Expected) (native : NativeField) : MetaM (Bool × Json) := do
  let actualName ← checked (decodeName (← checked (field row "nameExpr")))
  let actualOwner ← checked (decodeName (← checked (field row "ownerNameExpr")))
  unless actualName == expected.source && actualOwner == expected.sourceOwner do
    throwError "Unexpected source record {actualName} in {actualOwner}"
  unless (← checked (stringField row "record")) == "fullActualFact" &&
      (← checked (stringField row "kind")) == expected.kind &&
      (← checked (stringField row "provenance")) == expected.provenance &&
      (← checked (stringField row "referenceFile")) == "Iut/Tripod/CurveFacts.lean" &&
      (← checked (row.getObjValAs? Nat "referenceLine")) == expected.referenceLine &&
      (← checked (row.getObjValAs? Bool "isProposition")) &&
      (← checked (row.getObjValAs? Bool "valueRead")) &&
      (← checked (row.getObjValAs? Bool "kernelValueTypeMatchesActualTYPE")) &&
      !(← checked (row.getObjValAs? Bool "hasSorryAx")) do
    throwError "Incomplete source evidence for {actualName}"
  let declarationAxioms ← sourceAxioms row "axioms"
  let typeAxioms ← sourceAxioms row "typeAxioms"
  let valueAxioms ← sourceAxioms row "valueAxioms"
  let targetName ← checked (relocateName maps actualName)
  unless targetName == expected.target do
    throwError "Candidate pair disagrees with relocation for {actualName}"
  unless native.name == targetName do
    throwError "Unexpected constructor field {native.name}"
  let nativeAxioms ← expressionAxioms cache native.value
  ensureStandard targetName.toString nativeAxioms
  let (typePassed, typeResult) ← attempt (checkType cache maps row native)
  let (valuePassed, valueResult) ←
    if typePassed then attempt (checkValue cache maps row native) else pure (false, Json.null)
  return (typePassed && valuePassed, Json.mkObj [
    ("record", toJson "sourceTargetKernelComparison"),
    ("source", toJson actualName.toString),
    ("sourceOwner", toJson actualOwner.toString),
    ("target", toJson targetName.toString),
    ("targetConstructorOwner", toJson expected.targetOwner.toString),
    ("kind", toJson expected.kind),
    ("sourceProvenance", toJson expected.provenance),
    ("sourceReferenceLine", toJson expected.referenceLine),
    ("typePassed", toJson typePassed), ("type", typeResult),
    ("valuePassed", toJson valuePassed), ("value", valueResult),
    ("sourceAxioms", toJson declarationAxioms),
    ("sourceTypeAxioms", toJson typeAxioms),
    ("sourceValueAxioms", toJson valueAxioms),
    ("targetAxioms", toJson ((nativeAxioms.qsort Name.lt).map Name.toString))])

def filePath (config : Json) (key : String) : MetaM String := do
  let path ← checked (stringField config key)
  unless path.startsWith "/" do throwError "Expected absolute path for {key}"
  return path

private def constructorName := ``AbcAdaptation.Tripod.curveInputsOfSL2Image
private def curveInputsName := ``AbcAdaptation.Reference.Iut.CurveInputs

/-- Lean can abstract a proof inside a record literal into a generated theorem.
Read that theorem's value so the field's direct dependencies can be checked. -/
private def fieldRhs (argument : Expr) : MetaM Expr :=
  lambdaTelescope argument fun xs body => do
    let body := body.consumeMData
    let .const aux levels := body.getAppFn' | return argument
    unless constructorName.isPrefixOf (privateToUserName aux) do return argument
    let .thmInfo proof ← getConstInfo aux | throwError "Expected a constructor proof at {aux}"
    let value := proof.value.instantiateLevelParams proof.levelParams levels
    let applied := (mkAppN value body.getAppArgs).headBeta
    mkLambdaFVars xs applied

private def constructorHypothesis (xs : Array Expr) (head : Name) : MetaM Expr := do
  let some x ← xs.findM? (fun x => do
    let type ← inferType x
    return type.getAppFn'.isConstOf head) |
    throwError "The constructor is missing a parameter of type {head}"
  return x

private def readConstructorField (expected : Expected) : MetaM NativeField := do
  let env ← getEnv
  unless moduleOf env constructorName == some expected.targetOwner do
    throwError "Unexpected owner of the target constructor"
  let .defnInfo declaration ← getConstInfo constructorName |
    throwError "Expected the native curve input constructor definition"
  unless declaration.levelParams.isEmpty do throwError "Unexpected constructor universe parameter"
  let some info := getStructureInfo? env curveInputsName |
    throwError "Missing CurveInputs structure metadata"
  let some index := info.fieldNames.findIdx? (fun n => info.structName ++ n == expected.target) |
    throwError "Missing CurveInputs projection {expected.target}"
  lambdaTelescope declaration.value fun xs body => do
    let body := body.consumeMData
    let .const ctorName levels := body.getAppFn |
      throwError "The definition body does not build a CurveInputs record"
    let ctor ← getConstInfoCtor ctorName
    unless ctor.induct == curveInputsName do
      throwError "Unexpected constructor {ctorName}"
    let args := body.getAppArgs
    let offset := ctor.numParams + index
    let some argument := args[offset]? | throwError "Missing {expected.target} field argument"
    let fieldBinder ← instantiateForall (ctor.type.instantiateLevelParams ctor.levelParams levels)
      (args.extract 0 offset)
    let .forallE _ fieldType _ _ := fieldBinder |
      throwError "Expected the declared type of {expected.target}"
    let #[provider, bound, degree] := xs.extract 0 3 |
      throwError "The constructor is missing its provider, compact bound or degree"
    let rhs ← fieldRhs argument
    let bind (params closedParams : Array Expr) (specialized : Expr) (theoremName : Name) :
        MetaM NativeField := do
      return { name := expected.target
               type := ← mkForallFVars params fieldType
               value := ← mkLambdaFVars params argument
               rhs := ← mkLambdaFVars params rhs
               closedValue := ← mkLambdaFVars closedParams specialized
               closedTheorem := theoremName }
    match info.fieldNames[index]! with
    | `height_eq =>
      lambdaTelescope rhs fun _ expr => do
        let head := expr.consumeMData.getAppFn'
        unless head.isConstOf ``rfl || head.isConstOf ``Eq.refl do
          throwError "Expected a reflexivity proof for the height_eq argument"
      let params := #[provider, bound, degree]
      bind params params argument ``AbcAdaptation.Tripod.curveInputs_height_eq
    | `htCan_equiv =>
      let hh ← constructorHypothesis xs ``AbcAdaptation.Tripod.LegendreHeightHyp
      unless rhs.consumeMData == hh do
        throwError "The htCan_equiv argument differs from the constructor's hh"
      let comparison := mkApp2 (Lean.mkConst ``AbcAdaptation.Tripod.legendreHeight) provider bound
      bind #[provider, bound, hh] #[provider, bound] (argument.replaceFVars #[hh] #[comparison])
        ``AbcAdaptation.Tripod.curveInputs_htCan_equiv
    | `northcott =>
      let hN ← constructorHypothesis xs ``AbcAdaptation.Tripod.NorthcottHyp
      let hh ← constructorHypothesis xs ``AbcAdaptation.Tripod.LegendreHeightHyp
      lambdaTelescope rhs fun threshold expr => do
        let expr := expr.consumeMData
        let thm := ``AbcAdaptation.Tripod.northcott_of_equiv
        let args := expr.getAppArgs
        unless expr.getAppFn'.isConstOf thm && threshold.size ≤ 1 &&
            args.size == 5 + threshold.size && args.extract 0 3 == #[hN, bound, degree] &&
            args[4]! == hh && args.extract 5 args.size == threshold do
          throwError "Expected the field value northcott_of_equiv hN K d hh"
        let height := mkApp (Lean.mkConst ``AbcAdaptation.Tripod.CurveProviders.h) provider
        unless ← isDefEq args[3]! height do
          throwError "The northcott argument uses a different height function"
      let comparison := mkApp2 (Lean.mkConst ``AbcAdaptation.Tripod.legendreHeight) provider bound
      let northcott := Lean.mkConst ``AbcAdaptation.Tripod.northcottHyp
      bind #[provider, bound, degree, hN, hh] #[provider, bound, degree]
        (argument.replaceFVars #[hN, hh] #[northcott, comparison])
        ``AbcAdaptation.Tripod.curveInputs_northcott
    | n => throwError "Unexpected projection {n}"

private def checkClosedField (cache : AxiomCache) (native : NativeField) : MetaM Json := do
  unless moduleOf (← getEnv) native.closedTheorem == some `Solutions.Source_TripodCurveInputsHeightFields do
    throwError "Unexpected owner of the field theorem {native.closedTheorem}"
  let .thmInfo theoremInfo ← getConstInfo native.closedTheorem |
    throwError "Expected a field theorem {native.closedTheorem}"
  let inferred ← kernelCheck s!"specialized {native.name} constructor argument" native.closedValue
  kernelEq s!"specialized {native.name} constructor argument at its field theorem type"
    inferred theoremInfo.type
  let theoremValueType ← kernelCheck s!"field theorem {theoremInfo.name}" theoremInfo.value
  kernelEq s!"complete type of {theoremInfo.name}" theoremValueType theoremInfo.type
  kernelEq s!"specialized {native.name} constructor proof" native.closedValue theoremInfo.value
  let axioms ← expressionAxioms cache native.closedValue
  let theoremAxioms ← cachedAxioms cache theoremInfo.name
  ensureStandard native.name.toString axioms
  ensureStandard theoremInfo.name.toString theoremAxioms
  return Json.mkObj [
    ("record", toJson "targetConstructorField"),
    ("constructorDefinition", toJson constructorName.toString),
    ("projection", toJson native.name.toString),
    ("fieldTheorem", toJson theoremInfo.name.toString),
    ("actualConstructorRhsChecked", toJson true),
    ("kernelCheckedAtFieldTheoremType", toJson true),
    ("closedFieldExpr", ← checked (encodeExpr native.closedValue)),
    ("fieldTheoremExpr", ← checked (encodeExpr theoremInfo.value)),
    ("axioms", toJson (axioms.map Name.toString)),
    ("fieldTheoremAxioms", toJson (theoremAxioms.map Name.toString))]

run_meta do
  unless Lean.versionString == "4.33.1" do throwError "Expected Lean 4.33.1"
  let configPath ← absoluteEnv "TRIPOD_HEIGHT_FIELD_REVIEW_CONFIG"
  let config ← checked (Json.parse (← IO.FS.readFile configPath))
  unless (← checked (stringField config "schema")) == "tripod-height-field-source-correspondence/v1" do
    throwError "Unexpected height field review configuration schema"
  let pairs ← expectedPairs config
  unless pairs.size == 3 do throwError "Expected the three source height fields"
  let maps ← (← checked (arrayField config "maps")).mapM fun item => do
    let source ← checked (decodeName (← checked (field item "source")))
    let target ← checked (decodeName (← checked (field item "target")))
    pure (source, target)
  let sourceRecords ← IO.FS.Handle.mk (← filePath config "sourceFactsFile") .read
  let evidence ← IO.FS.Handle.mk (← filePath config "evidenceFile") .write
  let output ← filePath config "resultFile"
  let cache ← IO.mkRef ({} : Std.HashMap Name (Array Name))
  let mut sourceFailures : Array Name := #[]
  let mut closedFailures : Array Name := #[]
  for pair in pairs do
    let row ← checked (Json.parse (← sourceRecords.getLine))
    let native ← readConstructorField pair
    let (passed, report) ← compare cache maps row pair native
    unless passed do sourceFailures := sourceFailures.push pair.source
    evidence.putStrLn report.compress
    let (closedPassed, closedReport) ← attempt (checkClosedField cache native)
    unless closedPassed do closedFailures := closedFailures.push native.name
    evidence.putStrLn closedReport.compress
    evidence.flush
  unless (← sourceRecords.getLine).isEmpty do throwError "Unexpected extra source facts"
  let result := Json.mkObj [
    ("schema", toJson "tripod-height-field-source-correspondence/v1"),
    ("sourceReplayCompilerVersion", toJson "4.35.0-rc3"),
    ("targetCompilerVersion", toJson Lean.versionString),
    ("comparedSourceCount", toJson pairs.size),
    ("failedSourceNames", toJson (sourceFailures.map Name.toString)),
    ("failedClosedFields", toJson (closedFailures.map Name.toString)),
    ("kernelCorrespondencePassed", toJson sourceFailures.isEmpty),
    ("targetConstructorFieldsPassed", toJson closedFailures.isEmpty)]
  IO.FS.writeFile output (result.compress ++ "\n")
  unless sourceFailures.isEmpty do
    throwError "Source correspondence failed for {sourceFailures}. See {output}"
  unless closedFailures.isEmpty do
    throwError "Closed field comparison failed for {closedFailures}. See {output}"
  logInfo m!"{pairs.size} source height field proofs matched the actual constructor and the specialized field theorems"

end TripodHeightFieldSourceCorrespondence
