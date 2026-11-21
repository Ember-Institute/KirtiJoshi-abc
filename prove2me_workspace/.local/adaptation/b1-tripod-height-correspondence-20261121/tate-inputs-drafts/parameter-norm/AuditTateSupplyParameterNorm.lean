import Lean
import Definitions.Def_AbcAdaptation_Reference_Iut_Concrete_TateInputsSupply

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

namespace TateSupplyExpressionComparison
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

def sourceAxioms (row : Json) (key : String) : MetaM (Array String) := do
  let recorded ← checked (row.getObjValAs? (Array String) key)
  let allowed := standardAxioms.map Name.toString
  unless recorded.all (allowed.contains ·) do
    throwError "Unexpected source axioms in {key}: {recorded}"
  return recorded

end TateSupplyExpressionComparison

namespace TateSupplyParameterNormReview
open Lean Elab Term Meta FoundationAudit TateSupplyExpressionComparison

def certify (raw normalized : Expr) : MetaM Json := do
  kernelEq "native original and normalized expression" raw normalized
  let equality ← mkEq raw normalized
  let equalityProof ← mkEqRefl raw
  let inferredType ← kernelCheck "native normalization equality proof" equalityProof
  kernelEq "native normalization equality proposition" inferredType equality
  return Json.mkObj [
    ("originalExpr", ← checked (encodeExpr raw)),
    ("normalizedExpr", ← checked (encodeExpr normalized)),
    ("equalityExpr", ← checked (encodeExpr equality)),
    ("equalityProofExpr", ← checked (encodeExpr equalityProof))]

def contextVars : MetaM (Array Expr) := do
  return (← getLCtx).foldl (fun xs d => xs.push (mkFVar d.fvarId)) (#[] : Array Expr)

def localEqEvidence (label : String) (raw normalized : Expr) : MetaM Json := do
  let locals ← contextVars
  let rawClosed ← mkLambdaFVars locals raw
  let normalizedClosed ← mkLambdaFVars locals normalized
  let certificate ← certify rawClosed normalizedClosed
  return certificate.setObjVal! "label" (toJson label)

-- Expand saturated finite-place instances using their ten native arguments.
-- Check the resulting expression in the native kernel.
def normalizeCore (raw : Expr) : MetaM (Expr × Json) := do
  let events ← IO.mkRef (#[] : Array Json)
  let normalized ← Meta.transform raw (pre := fun e => do
    if e.getAppFn.isConstOf ``NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal then
      unless e.getAppNumArgs == 6 do throwError "Unexpected partial one_lt_absNorm_nnreal application"
      return .done e
    if e.getAppFn.isConstOf ``NumberField.HeightOneSpectrum.instNormedFieldValuedAdicCompletion ||
        e.getAppFn.isConstOf ``NumberField.HeightOneSpectrum.instRankOneAdicCompletion then
      unless e.getAppNumArgs == 10 do throwError "Unexpected partial FinitePlace data instance application"
      let some expanded ← unfoldDefinition? e (ignoreTransparency := true) |
        throwError "Actual FinitePlace data instance failed exact delta reduction"
      let candidate := expanded.headBeta
      let expected := if e.getAppFn.isConstOf ``NumberField.HeightOneSpectrum.instNormedFieldValuedAdicCompletion
        then ``Valued.toNormedField else ``Valuation.IsRankOneDiscrete.rankOne
      unless candidate.getAppFn.isConstOf expected do throwError "Unexpected delta core head"
      let event ← localEqEvidence "exact-ten-argument-instance-delta" e candidate
      events.modify (·.push event)
      return .visit candidate
    let args := e.getAppArgs
    if e.getAppFn.isConstOf ``DFunLike.coe && args.size == 6 then
      let hom := args[4]!
      if hom.getAppFn.isConstOf ``Ideal.absNorm && hom.getAppNumArgs == 4 then
        let some expanded ← unfoldDefinition? hom (ignoreTransparency := true) |
          throwError "Cannot delta-expand actual bundled absNorm"
        let projected := mkAppN e.getAppFn (args.set! 4 expanded)
        let candidate ← withReducibleAndInstances <| whnf projected
        unless candidate.getAppFn.isConstOf ``Submodule.cardQuot do throwError "Actual absNorm did not reduce to cardQuot"
        let event ← localEqEvidence "saturated-actual-Nat-absNorm-to-cardQuot" e candidate
        events.modify (·.push event)
        return .done candidate
    if e.getAppFn.isConstOf ``Ideal.absNorm then
      throwError "Unsupported unsaturated or bundled absNorm outside the retained Prop proof"
    return .continue)
  let evidence ← events.get
  return (normalized, Json.mkObj [
    ("events",Json.arr evidence),("exactDataDeltaCount",toJson evidence.size),
    ("nonPropositionalDataReplacedWithoutKernelCertificate",toJson false)])

structure ProofSite where
  functionType : Expr
  actualProofFunction : Expr
  localBinders : Array String
  localContextIndices : Array Nat
  deriving Inhabited

def collectProofSites (cache : AxiomCache) (core : Expr) : MetaM (Array ProofSite) := do
  let sites ← IO.mkRef (#[] : Array ProofSite)
  discard <| Meta.transform core (pre := fun e => do
    unless e.getAppFn.isConstOf ``NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal do
      return .continue
    unless e.getAppNumArgs == 6 do throwError "Expected a saturated native one_lt_absNorm_nnreal proof application"
    let expectedType ← inferType e
    unless ← isProp expectedType do throwError "Certificate abstraction would abstract computational data"
    let (normalizedProp,_) ← normalizeCore expectedType
    let allLocals ← contextVars
    let used ← (Lean.collectFVars (Lean.collectFVars {} normalizedProp) e).addDependencies
    let localContextIndices := (Array.range allLocals.size).filter fun i =>
      used.fvarSet.contains allLocals[i]!.fvarId!
    let locals := localContextIndices.map (allLocals[·]!)
    let functionType ← mkForallFVars locals normalizedProp
    let actualProofFunction ← mkLambdaFVars locals e
    requireClosed "certificate-only proof-function TYPE" functionType
    requireClosed "original actual proof function" actualProofFunction
    let proofType ← kernelCheck "actual original one_lt proof function" actualProofFunction
    kernelEq "actual one_lt proof function TYPE" proofType functionType
    ensureStandard "actual original proof function" (← expressionAxioms cache actualProofFunction)
    let localBinders ← locals.mapM fun x => return encodeBinder (← x.fvarId!.getDecl).binderInfo
    sites.modify (·.push {functionType,actualProofFunction,localBinders,localContextIndices})
    return .done e)
  return ← sites.get

partial def outerBinderInfo : Expr → List BinderInfo
  | .forallE _ _ body info => info :: outerBinderInfo body
  | .mdata _ body => outerBinderInfo body
  | _ => []

def boolField (j : Json) (key : String) : MetaM Bool :=
  checked (j.getObjValAs? Bool key)

def nameField (j : Json) (key : String) : MetaM Name := do
  checked (decodeName (← checked (field j key)))

def reviewQOrderSupport (cache : AxiomCache) (maps : Array (Name × Name))
    (records : Array Json) : MetaM Unit := do
  let expected := #[
    `Iut.EllipticCurveData.TateInputs.qOrder._proof_1,
    `Iut.EllipticCurveData.TateInputs.qOrder._proof_2]
  unless records.size == expected.size do
    throwError "Expected two accepted qOrder proof correspondences"
  for i in [:expected.size] do
    let record := records[i]!
    let source ← nameField record "source"
    let target ← nameField record "target"
    unless source == expected[i]! && (← checked (relocateName maps source)) == target do
      throwError "Unexpected qOrder proof correspondence {source} → {target}"
    let ci ← getConstInfo target
    unless moduleOf (← getEnv) target ==
        some `Definitions.Def_AbcAdaptation_Reference_Iut_Concrete_CurveData && kind ci == "theorem" do
      throwError "Unexpected owner or declaration kind for {target}"
    let some value := ci.value? (allowOpaque := true) |
      throwError "Missing complete value for {target}"
    unless (← checked (encodeExpr ci.type)) == (← checked (field record "targetType")) &&
        (← checked (encodeExpr value)) == (← checked (field record "targetValue")) do
      throwError "Live qOrder proof differs from the accepted complete native record {target}"
    let valueType ← kernelCheck s!"qOrder proof {target}" value
    unless ← isProp ci.type do throwError "Expected a qOrder proposition {target}"
    kernelEq s!"qOrder proof type {target}" valueType ci.type
    ensureStandard target.toString (← cachedAxioms cache target)

def compareCertificate (cache : AxiomCache) (maps : Array (Name × Name))
    (sourceRecord certificate : Json) (nativeRaw : Expr) (nativeUniverses : List Name)
    (label rawField : String) (expectedProofSites : Nat) : MetaM (Expr × Json) := do
  unless (← nameField sourceRecord "nameExpr") == (← nameField certificate "nameExpr") &&
      (← checked (stringField certificate "label")) == label &&
      (← checked (field sourceRecord rawField)) == (← checked (field certificate "rawExpression")) &&
      (← boolField certificate "sourceCompleteKernelNormalizationChecked") do
    throwError "Source certificate does not match the frozen expression {label}"
  let templateInfo ← checked (field certificate "samePropCompatibilityTemplateCertificate")
  unless (← boolField templateInfo "universalCompleteEqualityKernelChecked") &&
      !(← boolField templateInfo "productionDefinitionParametersAdded") &&
      (← boolField templateInfo "nativeProofFunctionsMustMatchCompleteTYPE") do
    throwError "Incomplete source compatibility certificate {label}"
  let sourceUniverses ← (← checked (arrayField sourceRecord "levelParams")).mapM fun value =>
    checked (decodeName value)
  unless sourceUniverses.size == nativeUniverses.length do throwError "Universe arity differs"
  let comparisonLevels := nativeUniverses.map Level.param
  let decode (value : Json) := do
    let expression ← checked (relocateExpr maps value)
    pure (expression.instantiateLevelParams sourceUniverses.toList comparisonLevels)
  let sourceTemplate ← decode (← checked (field templateInfo "completeProofFunctionTemplate"))
  let (nativeCore, nativeDelta) ← normalizeCore nativeRaw
  let nativeCoreCertificate ← certify nativeRaw nativeCore
  let nativeSites ← collectProofSites cache nativeCore
  let sourceSites ← checked (arrayField templateInfo "actualSourceProofArguments")
  let certifiedCount ← checked (templateInfo.getObjValAs? Nat "certificateOnlyProofFunctionCount")
  unless certifiedCount == expectedProofSites && sourceSites.size == certifiedCount &&
      nativeSites.size == certifiedCount do
    throwError "Source and native certificate proof occurrence counts differ at {label}"
  let mut nativeArguments : Array Expr := #[]
  let mut proofReports : Array Json := #[]
  for i in [:certifiedCount] do
    let sourceSite := sourceSites[i]!
    let nativeSite := nativeSites[i]!
    unless (← checked (sourceSite.getObjValAs? Nat "occurrenceIndex")) == i &&
        (← boolField sourceSite "proofOnlyCertificateBinder") &&
        (← checked (field sourceSite "originalContextBinderInfo")) == toJson nativeSite.localBinders &&
        (← checked (field sourceSite "originalContextDependencyIndices")) ==
          toJson nativeSite.localContextIndices do
      throwError "Proof-function binder context differs at {label} occurrence {i}"
    let sourceFunctionType ← decode (← checked (field sourceSite "proofFunctionType"))
    kernelEq s!"actual source and native proof-function type {label} occurrence {i}"
      sourceFunctionType nativeSite.functionType
    let nativeFunctionType ← kernelCheck "actual native proof function" nativeSite.actualProofFunction
    kernelEq "actual native proof at the mapped source proposition" nativeFunctionType sourceFunctionType
    nativeArguments := nativeArguments.push nativeSite.actualProofFunction
    proofReports := proofReports.push (Json.mkObj [
      ("mappedSourceFunctionType", ← checked (encodeExpr sourceFunctionType)),
      ("nativeFunctionType", ← checked (encodeExpr nativeFunctionType)),
      ("actualNativeProofFunction", ← checked (encodeExpr nativeSite.actualProofFunction))])
  let instantiatedSource := (mkAppN sourceTemplate nativeArguments).headBeta
  let instantiatedType ← kernelCheck "instantiated source expression" instantiatedSource
  let nativeType ← kernelCheck "actual native expression" nativeRaw
  kernelEq s!"full source and native expression {label}" instantiatedSource nativeRaw
  kernelEq s!"kernel-inferred source and native types at {label}" instantiatedType nativeType
  let sourceBeta ← Core.betaReduce instantiatedSource
  let nativeBeta ← Core.betaReduce nativeCore
  kernelEq s!"full source and native expressions after deep beta reduction {label}" sourceBeta nativeBeta
  unless outerBinderInfo instantiatedSource == outerBinderInfo nativeRaw do
    throwError "Outer binder information differs at {label}"
  for expression in #[instantiatedSource, instantiatedType, nativeRaw, nativeType] do
    ensureStandard label (← expressionAxioms cache expression)
  return (instantiatedType, Json.mkObj [
    ("label", toJson label),
    ("completeExprKernelDefEq", toJson true),
    ("mappedSourceExpr", ← checked (encodeExpr instantiatedSource)),
    ("mappedSourceInferredType", ← checked (encodeExpr instantiatedType)),
    ("nativeExpr", ← checked (encodeExpr nativeRaw)),
    ("nativeInferredType", ← checked (encodeExpr nativeType)),
    ("nativeDelta", nativeDelta),
    ("nativeCoreCertificate", nativeCoreCertificate),
    ("nativeProofArguments", Json.arr proofReports),
    ("outerBinderInfoEqual", toJson true),
    ("normalizedBinderPlacementEqual", toJson (binderPlacement sourceBeta == binderPlacement nativeBeta)),
    ("normalizedSourceBinderPlacement", toJson (binderPlacement sourceBeta)),
    ("normalizedNativeBinderPlacement", toJson (binderPlacement nativeBeta))])

def reviewJExistenceSupport (cache : AxiomCache) (maps : Array (Name × Name))
    (record : Json) : MetaM Unit := do
  let source ← nameField record "source"
  let target ← nameField record "target"
  unless source == `TateCurvesTheta.TateParameter.exists_tateParameter_tateJ_eq &&
      target == ``AbcAdaptation.Reference.TateCurvesTheta.TateParameter.exists_tateParameter_tateJ_eq &&
      (← checked (relocateName maps source)) == target do
    throwError "Unexpected Tate j-existence correspondence"
  let ci ← getConstInfo target
  unless moduleOf (← getEnv) target ==
      some `Definitions.Def_AbcAdaptation_Reference_TateCurvesTheta_QParameter_JExistence &&
      kind ci == "theorem" do
    throwError "Unexpected owner or declaration kind for {target}"
  let some value := ci.value? (allowOpaque := true) |
    throwError "Missing full value for {target}"
  unless (← checked (encodeExpr ci.type)) == (← checked (field record "targetType")) &&
      (← checked (encodeExpr value)) == (← checked (field record "targetValue")) do
    throwError "Live j-existence theorem differs from the accepted native record {target}"
  ensureStandard target.toString (← cachedAxioms cache target)

def compareProof (cache : AxiomCache) (maps : Array (Name × Name)) (record : Json)
    (sourceName targetName : Name) : MetaM Json := do
  let source ← checked (field record "sourceRecord")
  unless (← nameField source "nameExpr") == sourceName &&
      (← nameField source "ownerNameExpr") == `B1SourceReplay &&
      (← checked (stringField source "record")) == "fullActualFact" &&
      (← checked (stringField source "kind")) == "theorem" &&
      (← boolField source "valueRead") &&
      (← boolField source "kernelValueTypeMatchesActualTYPE") &&
      !(← boolField source "hasSorryAx") do
    throwError "Unexpected source proof for {sourceName}"
  for key in #["axioms", "typeAxioms", "valueAxioms"] do
    discard <| sourceAxioms source key
  unless (← checked (relocateName maps sourceName)) == targetName do
    throwError "Relocation disagrees with the audited target {targetName}"
  let ci ← getConstInfo targetName
  let owner := `Definitions.Def_AbcAdaptation_Reference_Iut_Concrete_TateInputsSupply
  unless kind ci == "theorem" && moduleOf (← getEnv) targetName == some owner do
    throwError "Unexpected suite theorem or owner for {targetName}"
  let some nativeValue := ci.value? (allowOpaque := true) |
    throwError "Missing complete proof of {targetName}"
  unless ← isProp ci.type do
    throwError "Expected a proposition for {targetName}"
  let axs ← cachedAxioms cache targetName
  ensureStandard targetName.toString axs
  let (_, typeReport) ← compareCertificate cache maps source
    (← checked (field record "typeCertificate")) ci.type ci.levelParams "TYPE" "actualTypeExpr" 1
  let (sourceValueType, valueReport) ← compareCertificate cache maps source
    (← checked (field record "valueCertificate")) nativeValue ci.levelParams "value" "actualValueExpr" 1
  kernelEq s!"{sourceName}: complete relocated proof at the native theorem type" sourceValueType ci.type
  return Json.mkObj [
    ("source", toJson sourceName.toString), ("sourceOwner", toJson "B1SourceReplay"),
    ("target", toJson targetName.toString), ("targetOwner", toJson owner.toString),
    ("type", typeReport), ("value", valueReport),
    ("fullMappedProofTypeChecks", toJson true),
    ("axioms", toJson (axs.qsort Name.lt |>.map Name.toString))]

run_meta do
  unless Lean.versionString == "4.33.1" do throwError "Expected Lean 4.33.1"
  let configPath ← absoluteEnv "B1_TATE_PARAMETER_NORM_REVIEW_CONFIG"
  let config ← checked (Json.parse (← IO.FS.readFile configPath))
  let schema := "b1-tate-supply-parameter-norm-review/v1"
  unless (← checked (stringField config "schema")) == schema do
    throwError "Unexpected Tate parameter proof review configuration"
  let maps ← (← checked (arrayField config "maps")).mapM fun item =>
    return (← nameField item "source", ← nameField item "target")
  let rows ← checked (arrayField config "pairs")
  let pairs : Array (Name × Name) := #[
    (`Iut.EllipticCurveData.one_lt_norm_j, ``AbcAdaptation.Reference.Iut.EllipticCurveData.one_lt_norm_j),
    (`Iut.EllipticCurveData.tateParameter._proof_1,
      `AbcAdaptation.Reference.Iut.EllipticCurveData.tateParameter._proof_1)]
  unless rows.size == pairs.size do throwError "Expected the two Tate parameter proofs"
  let cache ← IO.mkRef ({} : Std.HashMap Name (Array Name))
  reviewQOrderSupport cache maps (← checked (arrayField config "qOrderSupport"))
  reviewJExistenceSupport cache maps (← checked (field config "jExistenceSupport"))
  let output ← checked (stringField config "outputFile")
  unless output.startsWith "/" do throwError "Expected absolute output file path"
  let mut reports : Array Json := #[]
  let mut failures : Array String := #[]
  for i in [:pairs.size] do
    let (sourceName, targetName) := pairs[i]!
    try
      reports := reports.push (← compareProof cache maps rows[i]! sourceName targetName)
    catch error =>
      failures := failures.push sourceName.toString
      reports := reports.push (Json.mkObj [
        ("source", toJson sourceName.toString), ("target", toJson targetName.toString),
        ("diagnostic", toJson (← error.toMessageData.toString))])
  let report := Json.mkObj [
    ("schema", toJson schema), ("compilerVersion", toJson Lean.versionString),
    ("sourceCompilerVersion", toJson "4.35.0-rc3"),
    ("acceptedQOrderProofsRebound", toJson true),
    ("acceptedJExistenceProofRebound", toJson true),
    ("uncheckedSourceNames", toJson failures),
    ("kernelCorrespondencePassed", toJson failures.isEmpty),
    ("comparisons", Json.arr reports)]
  IO.FS.writeFile output (report.compress ++ "\n")
  unless failures.isEmpty do
    throwError "Tate parameter correspondence failed for {failures}. See {output}"
  logInfo m!"Both Tate parameter proof comparisons passed with standard axioms"

end TateSupplyParameterNormReview
