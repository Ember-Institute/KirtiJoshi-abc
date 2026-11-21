import Lean
import Solutions.Source_TripodCurveInputsFromSource
import Solutions.Source_TripodCurveInputsTwoAdicField

set_option autoImplicit false

namespace TwoAdicConstructorFieldAudit

open AbcAdaptation.Tripod AbcAdaptation.Reference.Iut

/-- The source field with the constructor's hypothesis still explicit. -/
theorem heightEq_two_le_from_hB (P : CurveProviders) (K : CompactlyBounded) (d : ℕ)
    (hB : TwoAdicBoundHyp P K (max (4 * K.c) 0))
    (x : tripodTheory.Pt tripodTheory.tripod)
    (hx : x ∈ tripodTheory.cbsSet K ∩ tripodTheory.ptLE tripodTheory.tripod d) :
    ((P.curve x).localHeightData (P.arith x) (P.tate x)).heightEq 2 ≤ max (4 * K.c) 0 :=
  hB x hx.1

/-- The supplied arithmetic and Tate data give these fields in the Corollary 2.2 input. -/
theorem corollary22Fields (P : CurveProviders) (K : CompactlyBounded) (d : ℕ)
    {AG : AnabelianGeometry.{0}} {TK : ℝ}
    (CF : CurveFactsProp P K d TK) (hcore : CoreFinitenessHyp P K d AG)
    (hN : NorthcottHyp) (hh : LegendreHeightHyp P K)
    (x : tripodTheory.Pt tripodTheory.tripod)
    (hx : x ∈ tripodTheory.cbsSet K ∩ tripodTheory.ptLE tripodTheory.tripod d) :
    let CI := curveInputs_from_source P K d CF hcore hN hh (twoAdicBound P K)
    let I := CI.toCorollary22Inputs
    I.B = max (4 * K.c) 0 ∧
      I.B_nonneg = curveInputs_B_nonneg K ∧
      I.heightEq_two_le x hx = curveInputs_heightEq_two_le P K d x hx :=
  ⟨rfl, rfl, rfl⟩

open Lean Elab Term Meta

/- Read the compiled assignments as expressions so proof irrelevance cannot hide a change
in the constructor's use of the explicit hypothesis. -/
def auditConstructorExpressions : MetaM Unit := do
  let constructor := ``curveInputsOfSL2Image
  let structureName := ``CurveInputs
  let env ← getEnv
  let some structureInfo := getStructureInfo? env structureName |
    throwError "Could not read the CurveInputs field names"
  let .defnInfo declaration ← getConstInfo constructor |
    throwError "Could not read curveInputsOfSL2Image"
  lambdaTelescope declaration.value fun args body => do
    let body := body.consumeMData
    let .const ctorName _ := body.getAppFn |
      throwError "Expected a CurveInputs constructor application"
    let ctor ← getConstInfoCtor ctorName
    unless ctor.induct == structureName do
      throwError "Expected the CurveInputs constructor"
    let fields := body.getAppArgs
    let fieldValue (name : Name) : MetaM Expr := do
      let some index := structureInfo.fieldNames.findIdx? (· == name) |
        throwError "Could not find field {name}"
      let some value := fields[ctor.numParams + index]? |
        throwError "Could not read field {name}"
      -- Lean moves nontrivial proof fields into auxiliary theorems of this definition.
      let proof ← deltaExpand value (fun n => constructor.isPrefixOf (privateToUserName n))
        (allowOpaque := true)
      return proof.consumeMData
    let nonneg ← fieldValue `B_nonneg
    unless nonneg.getAppFn.isConstOf ``le_max_right do
      throwError "Expected le_max_right in B_nonneg, found {nonneg.getAppFn}"
    let binderNames ← args.mapM fun arg => return (← arg.fvarId!.getDecl).userName
    let some index := binderNames.findIdx? (· == `hB) |
      throwError "Could not find the two-adic hypothesis binder"
    let hB := args[index]!
    lambdaTelescope (← fieldValue `heightEq_two_le) fun binders proof => do
      let proof := proof.consumeMData
      let actual := proof.getAppArgs
      unless binders.size == 2 && proof.getAppFn == hB && actual.size == 2 &&
          actual[0]! == binders[0]! do
        throwError "Expected heightEq_two_le to apply hB to the field's point and membership"
      let membership := actual[1]!.consumeMData
      let compactMembership := match membership with
        | .proj name index premise =>
          name == ``And && index == 0 && premise == binders[1]!
        | _ =>
          membership.getAppFn.isConstOf ``And.left &&
            membership.getAppArgs[membership.getAppNumArgs - 1]? == some binders[1]!
      unless compactMembership do
        throwError "Expected the compact membership obtained from hx.1"

end TwoAdicConstructorFieldAudit

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

namespace TripodTwoAdicExpressionComparison
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

end TripodTwoAdicExpressionComparison


namespace TripodTwoAdicSourceCorrespondence
open Lean Elab Term Meta FoundationAudit TripodTwoAdicExpressionComparison

structure Expected where
  source : Name
  sourceOwner : Name
  target : Name
  targetOwner : Name
  kind : String
  provenance : String
  referenceFile : String
  referenceLine : Nat

def expectedPairs (config : Json) : MetaM (Array Expected) := do
  (← checked (arrayField config "pairs")).mapM fun item => do
    let source ← checked (decodeName (← checked (field item "source")))
    let sourceOwner ← checked (decodeName (← checked (field item "sourceOwner")))
    let target ← checked (decodeName (← checked (field item "target")))
    let targetOwner ← checked (decodeName (← checked (field item "targetOwner")))
    let kind ← checked (stringField item "kind")
    let provenance ← checked (stringField item "provenance")
    let referenceFile ← checked (stringField item "referenceFile")
    let referenceLine ← checked (item.getObjValAs? Nat "referenceLine")
    return { source, sourceOwner, target, targetOwner, kind, provenance, referenceFile, referenceLine }

def auditConstants (label : String) (expression : Expr) : MetaM Unit := do
  let env ← getEnv
  let missing := expression.getUsedConstants.filter fun name => (env.find? name).isNone
  unless missing.isEmpty do
    throwError "{label}: missing target constants {missing.qsort Name.lt}"

def checkType (cache : AxiomCache) (maps : Array (Name × Name)) (row : Json)
    (ci : ConstantInfo) : MetaM Json := do
  let universes ← namesFromJson (← checked (field row "levelParams"))
  unless universes == ci.levelParams do
    throwError "Named universe parameter order differs for {ci.name}"
  let originalSourceType ← checked (field row "actualTypeExpr")
  let sourceType ← checked (relocateExpr maps originalSourceType)
  auditConstants "Mapped source type" sourceType
  let sourceBinders := binderPlacement sourceType
  let targetBinders := binderPlacement ci.type
  unless outerBinderPlacement sourceType == outerBinderPlacement ci.type do
    throwError "Outer type binder modes differ for {ci.name}"
  kernelEq s!"full type {ci.name}" sourceType ci.type
  let mappedSourceAxioms ← expressionAxioms cache sourceType
  let targetAxioms ← expressionAxioms cache ci.type
  ensureStandard ci.name.toString mappedSourceAxioms
  ensureStandard ci.name.toString targetAxioms
  return Json.mkObj [
    ("kernelDefinitionalEquality", toJson true),
    ("levelParams", toJson (universes.map Name.toString)),
    ("outerBinderPlacement", toJson (outerBinderPlacement ci.type)),
    ("rawBinderPlacementMatches", toJson (sourceBinders == targetBinders)),
    ("sourceBinderPlacement", toJson sourceBinders),
    ("targetBinderPlacement", toJson targetBinders),
    ("originalSourceExpr", originalSourceType),
    ("mappedSourceExpr", ← checked (encodeExpr sourceType)),
    ("targetExpr", ← checked (encodeExpr ci.type)),
    ("directConstantDifferences", constantDifferences sourceType ci.type),
    ("mappedSourceAxioms", toJson (mappedSourceAxioms.map Name.toString)),
    ("targetAxioms", toJson (targetAxioms.map Name.toString))]

def checkValue (cache : AxiomCache) (maps : Array (Name × Name)) (row : Json)
    (ci : ConstantInfo) : MetaM Json := do
  let some targetValue := ci.value? (allowOpaque := true) | throwError "Missing value for {ci.name}"
  let originalSourceValue ← checked (field row "actualValueExpr")
  let sourceValue ← checked (relocateExpr maps originalSourceValue)
  auditConstants "Mapped source proof" sourceValue
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
    ("sourceValueMatchesTargetExpr", toJson (sourceValue == targetValue)),
    ("originalSourceExpr", originalSourceValue),
    ("mappedSourceExpr", ← checked (encodeExpr sourceValue)),
    ("targetExpr", ← checked (encodeExpr targetValue)),
    ("directConstantDifferences", constantDifferences sourceValue targetValue),
    ("mappedSourceAxioms", toJson (mappedSourceAxioms.map Name.toString)),
    ("targetAxioms", toJson (targetAxioms.map Name.toString))]

def attempt (action : MetaM Json) : MetaM (Bool × Json) := do
  try
    return (true, ← action)
  catch e =>
    return (false, Json.mkObj [("diagnostic", toJson (← e.toMessageData.toString))])

def compare (cache : AxiomCache) (maps : Array (Name × Name)) (row : Json)
    (expected : Expected) : MetaM (Bool × Json) := do
  let actualName ← checked (decodeName (← checked (field row "nameExpr")))
  let actualOwner ← checked (decodeName (← checked (field row "ownerNameExpr")))
  unless actualName == expected.source && actualOwner == expected.sourceOwner do
    throwError "Unexpected source record {actualName} in {actualOwner}"
  unless (← checked (stringField row "record")) == "fullActualFact" &&
      (← checked (stringField row "kind")) == expected.kind &&
      (← checked (stringField row "provenance")) == expected.provenance &&
      (← checked (stringField row "referenceFile")) == expected.referenceFile &&
      (← checked (row.getObjValAs? Nat "referenceLine")) == expected.referenceLine &&
      (← checked (row.getObjValAs? Bool "isProposition")) == (expected.kind == "theorem") &&
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
  let ci ← getConstInfo targetName
  let env ← getEnv
  let owner := (moduleOf env targetName).getD env.mainModule
  unless owner == expected.targetOwner && kind ci == expected.kind do
    throwError "Unexpected target declaration or owner for {targetName}"
  let nativeAxioms ← cachedAxioms cache targetName
  ensureStandard targetName.toString nativeAxioms
  let (typePassed, typeResult) ← attempt (checkType cache maps row ci)
  let (valuePassed, valueResult) ←
    if typePassed then attempt (checkValue cache maps row ci) else pure (false, Json.null)
  return (typePassed && valuePassed, Json.mkObj [
    ("record", toJson "sourceTargetKernelComparison"),
    ("source", toJson actualName.toString),
    ("sourceOwner", toJson actualOwner.toString),
    ("target", toJson targetName.toString),
    ("targetOwner", toJson expected.targetOwner.toString),
    ("kind", toJson expected.kind),
    ("sourceProvenance", toJson expected.provenance),
    ("sourceReferenceFile", toJson expected.referenceFile),
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

def checkConstructorFields (cache : AxiomCache) : MetaM Json := do
  TwoAdicConstructorFieldAudit.auditConstructorExpressions
  let name := ``TwoAdicConstructorFieldAudit.corollary22Fields
  let ci ← getConstInfo name
  let some value := ci.value? (allowOpaque := true) | throwError "Missing compiled projection witness"
  let valueType ← kernelCheck "Corollary 2.2 projection witness" value
  kernelEq "Corollary 2.2 projection witness type" valueType ci.type
  let axs ← cachedAxioms cache name
  ensureStandard name.toString axs
  return Json.mkObj [
    ("record", toJson "targetConstructorFields"),
    ("constructorDefinition", toJson "AbcAdaptation.Tripod.curveInputsOfSL2Image"),
    ("checkedAssignments", toJson #["B_nonneg", "heightEq_two_le"]),
    ("corollary22Witness", toJson name.toString),
    ("projectionWitnessType", ← checked (encodeExpr ci.type)),
    ("projectionWitnessValue", ← checked (encodeExpr value)),
    ("axioms", toJson ((axs.qsort Name.lt).map Name.toString))]

run_meta do
  unless Lean.versionString == "4.33.1" do throwError "Expected Lean 4.33.1"
  let configPath ← absoluteEnv "TRIPOD_TWOADIC_REVIEW_CONFIG"
  let config ← checked (Json.parse (← IO.FS.readFile configPath))
  unless (← checked (stringField config "schema")) == "tripod-twoadic-source-correspondence/v1" do
    throwError "Unexpected two-adic review configuration schema"
  let pairs ← expectedPairs config
  unless pairs.size == 6 do throwError "Expected six source records"
  let maps ← (← checked (arrayField config "maps")).mapM fun item => do
    let source ← checked (decodeName (← checked (field item "source")))
    let target ← checked (decodeName (← checked (field item "target")))
    pure (source, target)
  let sourceRecords ← IO.FS.Handle.mk (← filePath config "sourceFactsFile") .read
  let evidence ← IO.FS.Handle.mk (← filePath config "evidenceFile") .write
  let output ← filePath config "resultFile"
  let cache ← IO.mkRef ({} : Std.HashMap Name (Array Name))
  let mut failures : Array Name := #[]
  for pair in pairs do
    let row ← checked (Json.parse (← sourceRecords.getLine))
    let (passed, report) ← compare cache maps row pair
    unless passed do failures := failures.push pair.source
    evidence.putStrLn report.compress
    evidence.flush
  unless (← sourceRecords.getLine).isEmpty do throwError "Unexpected extra source facts"
  let (fieldPassed, fieldResult) ← attempt (checkConstructorFields cache)
  evidence.putStrLn fieldResult.compress
  evidence.flush
  let result := Json.mkObj [
    ("schema", toJson "tripod-twoadic-source-correspondence/v1"),
    ("sourceReplayCompilerVersion", toJson "4.35.0-rc3"),
    ("targetCompilerVersion", toJson Lean.versionString),
    ("comparedSourceCount", toJson pairs.size),
    ("failedSourceNames", toJson (failures.map Name.toString)),
    ("kernelCorrespondencePassed", toJson failures.isEmpty),
    ("targetConstructorFieldPassed", toJson fieldPassed)]
  IO.FS.writeFile output (result.compress ++ "\n")
  unless failures.isEmpty do
    throwError "Cross-version comparison failed for {failures}. See {output}"
  unless fieldPassed do
    throwError "Native constructor field check failed. See {output}"
  logInfo m!"{pairs.size} two-adic declarations matched their target types and values. The compiled constructor fields passed."

end TripodTwoAdicSourceCorrespondence
