import Lean
import B1SourceReplay

/-! Stable JSON for *actual compiler Exprs*. No pretty-printer text is decoded here.
    Metadata is erased; local/metavariables are rejected. -/
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

def jsonFile (p : String) : MetaM Json := do
  checked (Json.parse (← IO.FS.readFile p))

def absoluteEnv (key : String) : MetaM String := do
  let some p ← IO.getEnv key | throwError "Missing environment variable {key}"
  unless p.startsWith "/" do throwError "Expected absolute path: {key}"
  return p

def moduleOf (env : Environment) (name : Name) : Option Name := do
  let index ← env.getModuleIdxFor? name
  let m ← env.header.modules[index.toNat]?
  return m.module

def standardAxioms : Array Name := #[`propext, `Classical.choice, `Quot.sound]

def ensureStandard (label : String) (axs : Array Name) : MetaM Unit := do
  for ax in axs do
    unless standardAxioms.contains ax do throwError "Unexpected axiom in {label}: {ax}"

def expressionAxioms (e : Expr) : MetaM (Array Name) := do
  let mut axs : Array Name := #[]
  for name in e.getUsedConstants do
    for ax in ← collectAxioms name do
      unless axs.contains ax do axs := axs.push ax
  return axs.qsort Name.lt

partial def binderInventory : Expr → Array String
  | .forallE _ t b bi => #["forall:" ++ encodeBinder bi] ++ binderInventory t ++ binderInventory b
  | .lam _ t b bi => #["lambda:" ++ encodeBinder bi] ++ binderInventory t ++ binderInventory b
  | .app f a => binderInventory f ++ binderInventory a
  | .letE _ t v b _ => binderInventory t ++ binderInventory v ++ binderInventory b
  | .mdata _ e => binderInventory e
  | .proj _ _ e => binderInventory e
  | _ => #[]

def kind (ci : ConstantInfo) : String := match ci with
  | .axiomInfo _ => "axiom" | .defnInfo _ => "definition" | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque" | .quotInfo _ => "quotient"
  | .inductInfo _ => "inductive" | .ctorInfo _ => "constructor" | .recInfo _ => "recursor"

end FoundationAudit

namespace B1TateSupplySourceNormalization
open Lean Elab Term Meta FoundationAudit
def closed (label : String) (e : Expr) : MetaM Unit := do
  if e.hasFVar || e.hasMVar || e.hasLooseBVars then throwError "Open Expr {label}"

def kcheck (label : String) (e : Expr) : MetaM Expr := do
  closed label e
  match Kernel.check (← getEnv) {} e with
  | .ok t => return t
  | .error ex => throwKernelException ex

def keq (label : String) (e f : Expr) : MetaM Unit := do
  let et ← kcheck label e
  let ft ← kcheck label f
  for (a,b) in #[(et,ft),(e,f)] do
    match Kernel.isDefEq (← getEnv) {} a b with
    | .ok true => pure ()
    | .ok false => throwError "Kernel inequality {label}"
    | .error ex => throwKernelException ex

def certify (raw normalized : Expr) : MetaM Json := do
  keq "complete original/normalized Expr" raw normalized
  let equality ← mkEq raw normalized
  let proof ← mkEqRefl raw
  let pt ← kcheck "complete normalization equality proof" proof
  keq "complete normalization equality proposition" pt equality
  ensureStandard "complete normalization equality proof" (← expressionAxioms proof)
  return Json.mkObj [
    ("originalExpr",← checked (encodeExpr raw)),
    ("normalizedExpr",← checked (encodeExpr normalized)),
    ("equalityExpr",← checked (encodeExpr equality)),
    ("equalityProofExpr",← checked (encodeExpr proof)),
    ("completeExprKernelDefEq",toJson true),
    ("completeEqualityProofKernelChecked",toJson true),
    ("axioms",toJson ((← expressionAxioms proof).map Name.toString))]


def contextVars (exclude : Array Expr := #[]) : MetaM (Array Expr) := do
  return (← getLCtx).foldl (fun xs d =>
    let x := mkFVar d.fvarId
    if exclude.contains x then xs else xs.push x) (#[] : Array Expr)

def localEqEvidence (label : String) (raw normalized : Expr) : MetaM Json := do
  let locals ← contextVars
  let rawClosed ← mkLambdaFVars locals raw
  let normalizedClosed ← mkLambdaFVars locals normalized
  let certificate ← certify rawClosed normalizedClosed
  return certificate.setObjVal! "label" (toJson label)

-- These are the only computational declarations expanded. All ten source
-- arguments are supplied to real delta reduction; no class is renamed or mapped.
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

def collectProofSites (core : Expr) : MetaM (Array ProofSite) := do
  let sites ← IO.mkRef (#[] : Array ProofSite)
  discard <| Meta.transform core (pre := fun e => do
    unless e.getAppFn.isConstOf ``NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal do
      return .continue
    unless e.getAppNumArgs == 6 do throwError "Expected complete source one_lt_absNorm_nnreal proof application"
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
    closed "certificate-only proof-function TYPE" functionType
    closed "original actual proof function" actualProofFunction
    let proofType ← kcheck "actual original one_lt proof function" actualProofFunction
    keq "actual one_lt proof function TYPE" proofType functionType
    ensureStandard "actual original proof function" (← expressionAxioms actualProofFunction)
    let localBinders ← locals.mapM fun x => return encodeBinder (← x.fvarId!.getDecl).binderInfo
    sites.modify (·.push {functionType,actualProofFunction,localBinders,localContextIndices})
    return .done e)
  return ← sites.get

-- The proof functions below are bound only in the compatibility certificate.
-- Neither a source/target production definition nor its statement receives them.
def proofTemplateCertificate (raw core : Expr) (sites : Array ProofSite)
    (requireVersionIndependentTemplate : Bool := true) : MetaM Json := do
  let decls := sites.mapIdx fun i site => (Name.mkSimple s!"finitePlaceProofCertificate{i}", site.functionType)
  withLocalDeclsDND decls fun proofFunctions => do
    let index ← IO.mkRef (0 : Nat)
    let openedTemplate ← Meta.transform core (pre := fun e => do
      unless e.getAppFn.isConstOf ``NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal do
        return .continue
      let i ← index.get
      unless i < sites.size do throwError "More template proof sites than original source occurrences"
      let allLocals ← contextVars proofFunctions
      let locals := sites[i]!.localContextIndices.map (allLocals[·]!)
      let proofFunction := proofFunctions[i]!
      let candidate := mkAppN proofFunction locals
      unless ← isDefEq (← inferType candidate) (← inferType e) do
        throwError "Certificate proof-function application is not the same actual proposition"
      index.modify (·+1)
      return .done candidate)
    unless (← index.get) == sites.size do throwError "Template proof site count changed"
    let template ← mkLambdaFVars proofFunctions openedTemplate
    closed "complete certificate-only template" template
    for forbidden in #[``NumberField.HeightOneSpectrum.instNormedFieldValuedAdicCompletion,
        ``NumberField.HeightOneSpectrum.instRankOneAdicCompletion,
        ``NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal,
        ``Ring.HasFiniteQuotients, ``NumberField.RingOfIntegers.instHasFiniteQuotients,
        ``Ideal.absNorm,
        ``Iut.EllipticCurveData.TateInputs.qOrder._proof_3,
        ``Iut.EllipticCurveData.TateInputs.qOrder._proof_4] do
      if requireVersionIndependentTemplate && template.getUsedConstants.contains forbidden then
        throwError "Version-specific finite-place dependency remains in complete template: {forbidden}"
    -- Applying the original actual proof functions must reproduce the real data core.
    let originalInstantiation := mkAppN template (sites.map (·.actualProofFunction))
    let originalCertificate ← certify raw originalInstantiation
    -- Prove the complete equality for EVERY proof function of the fixed propositions.
    let openedEquality ← mkEq raw openedTemplate
    let generalizedEquality ← mkForallFVars proofFunctions openedEquality
    let openedProof ← mkEqRefl raw
    let generalizedProof ← mkLambdaFVars proofFunctions openedProof
    let inferred ← kcheck "universal complete-data compatibility equality proof" generalizedProof
    keq "universal complete-data compatibility equality TYPE" inferred generalizedEquality
    ensureStandard "universal compatibility certificate" (← expressionAxioms generalizedProof)
    let templateType ← kcheck "complete compatibility template" template
    let mut sourceProofArguments : Array Json := #[]
    for i in [:sites.size] do
      let site := sites[i]!
      sourceProofArguments := sourceProofArguments.push (Json.mkObj [
        ("occurrenceIndex",toJson i),("proofFunctionType",← checked (encodeExpr site.functionType)),
        ("actualSourceProofFunction",← checked (encodeExpr site.actualProofFunction)),
        ("originalContextBinderInfo",toJson site.localBinders),
        ("originalContextDependencyIndices",toJson site.localContextIndices),
        ("proofOnlyCertificateBinder",toJson true)])
    return Json.mkObj [
      ("completeProofFunctionTemplate",← checked (encodeExpr template)),
      ("completeProofFunctionTemplateType",← checked (encodeExpr templateType)),
      ("actualSourceProofArguments",Json.arr sourceProofArguments),
      ("universalEqualityExpr",← checked (encodeExpr generalizedEquality)),
      ("universalEqualityProofExpr",← checked (encodeExpr generalizedProof)),
      ("universalCompleteEqualityKernelChecked",toJson true),
      ("actualSourceProofInstantiationCertificate",originalCertificate),
      ("certificateOnlyProofFunctionCount",toJson sites.size),
      ("productionDefinitionParametersAdded",toJson false),
      ("nativeProofFunctionsMustMatchCompleteTYPE",toJson true)]


def normalizeOne (n : Name) (label : String) (raw : Expr) : MetaM Json := do
  let (core, delta) ← normalizeCore raw
  let certificate ← certify raw core
  let sites ← collectProofSites core
  let template ← proofTemplateCertificate raw core sites
  ensureStandard s!"source expression {n}:{label}" (← expressionAxioms raw)
  ensureStandard s!"normalized source expression {n}:{label}" (← expressionAxioms core)
  return Json.mkObj [
    ("name", toJson n.toString), ("nameExpr", encodeName n), ("label", toJson label),
    ("rawExpression", ← checked (encodeExpr raw)),
    ("deltaNormalizedExpression", ← checked (encodeExpr core)),
    ("wholeRawToDeltaCoreCertificate", certificate), ("exactDeltaSteps", delta),
    ("samePropCompatibilityTemplateCertificate", template),
    ("rawBinderInventory", toJson (binderInventory raw)),
    ("deltaNormalizedBinderInventory", toJson (binderInventory core)),
    ("sourceCompleteKernelNormalizationChecked", toJson true)]

run_meta do
  unless Lean.versionString == "4.35.0-rc3" do
    throwError "Expected Lean 4.35.0-rc3 for the source replay"
  let config ← jsonFile (← absoluteEnv "B1_TATE_SUPPLY_SOURCE_CONFIG")
  unless (← checked (stringField config "schema")) == "b1-tate-supply-source-config/v1" do
    throwError "Unexpected Tate supply source configuration"
  let factsPath ← checked (stringField config "sourceFactsFile")
  let outputPath ← checked (stringField config "outputFile")
  unless factsPath.startsWith "/" && outputPath.startsWith "/" do
    throwError "Expected absolute paths for the source facts and output"
  let inputs ← IO.FS.Handle.mk factsPath .read
  let expected : Array Name := #[
    `Iut.EllipticCurveData.one_lt_norm_j,
    `Iut.EllipticCurveData.tateParameter,
    `Iut.EllipticCurveData.tateParameter_tateJ,
    `Iut.EllipticCurveData.tateInputs,
    `Iut.EllipticCurveData.tateParameter._proof_1,
    `Iut.EllipticCurveData.tateInputs._proof_1,
    `Iut.EllipticCurveData.tateInputs._proof_2]
  let env ← getEnv
  let mut rows : Array Json := #[]
  let mut certificates : Array Json := #[]
  for n in expected do
    let row ← checked (Json.parse (← inputs.getLine))
    let name ← checked (decodeName (← checked (field row "nameExpr")))
    unless name == n && moduleOf env name == some `B1SourceReplay do
      throwError "Unexpected source declaration {name}"
    let ci ← getConstInfo name
    unless (← checked (field row "levelParams")) == Json.arr (ci.levelParams.toArray.map encodeName) do
      throwError "Source universe parameters differ for {name}"
    unless (← checked (stringField row "kind")) == kind ci do
      throwError "Source declaration kind differs for {name}"
    unless (← checked (field row "actualTypeExpr")) == (← checked (encodeExpr ci.type)) do
      throwError "Source type differs for {name}"
    let some value := ci.value? (allowOpaque := true) |
      throwError "Source declaration lacks a value for {name}"
    unless (← checked (field row "actualValueExpr")) == (← checked (encodeExpr value)) do
      throwError "Source value differs for {name}"
    let inferred ← kcheck s!"actual source value of {name}" value
    keq s!"actual source value type of {name}" inferred ci.type
    ensureStandard name.toString (← collectAxioms name)
    rows := rows.push row
    certificates := certificates.push (← normalizeOne name "TYPE" ci.type)
    certificates := certificates.push (← normalizeOne name "value" value)
  unless (← inputs.getLine).isEmpty do throwError "Unexpected extra Tate supply source facts"
  IO.FS.writeFile outputPath ((Json.mkObj [
    ("schema", toJson "b1-tate-supply-source-normalization/v1"),
    ("compilerVersion", toJson Lean.versionString),
    ("sourceRecords", Json.arr rows),
    ("normalizationCertificates", Json.arr certificates),
    ("sourceCompleteKernelNormalizationChecked", toJson true)]).pretty ++ "\n")
  logInfo m!"Checked complete source types and values for {rows.size} Tate supply declarations"

end B1TateSupplySourceNormalization
