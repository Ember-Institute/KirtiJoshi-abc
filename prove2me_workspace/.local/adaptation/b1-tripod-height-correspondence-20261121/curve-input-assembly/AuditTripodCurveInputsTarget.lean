/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository https://github.com/lana-agents/iut
Original revision 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
Original path Iut/Tripod/CurveFacts.lean (sl2Image and curveInputs)
-/
import Lean
import Definitions.Def_AbcAdaptation_Reference_Iut_Tripod_CurveFacts
import Definitions.Def_AbcAdaptation_Reference_Iut_Tripod_CurveDegreeBound
import Definitions.Def_AbcAdaptation_Reference_Iut_Tripod_DifferentDegree
import Definitions.Def_AbcAdaptation_Reference_Iut_Tripod_LegendreHeightHyp
import Definitions.Def_AbcAdaptation_Reference_Iut_Tripod_NorthcottComparison
import Definitions.Def_AbcAdaptation_Reference_Iut_Tripod_TwoAdicBoundHyp
import Solutions.Source_TripodCurveInputsFromSource

set_option autoImplicit false

namespace AbcAdaptation.Tripod

open AbcAdaptation.Reference AbcAdaptation.Reference.Iut

/-- The local Tate-ramification proof supplies the SL₂ image field of the provider. -/
private theorem sl2Image (P : CurveProviders) : SL2ImageHyp P := by
  classical
  intro x ℓ hℓ h5 hP2 hP4 hP5 A
  have hP2' : ∀ w (hw : w ∈ (P.curve x).badAll), ¬ ℓ ∣ (P.tate x).qOrder w hw := by
    intro w hw
    have := hP2 w ((P.arith x).badAll_finite.mem_toFinset.mpr hw)
    change ¬ ℓ ∣ (if h : w ∈ (P.curve x).badAll then (P.tate x).qOrder w h else 0) at this
    rwa [dif_pos hw] at this
  have hP5' : ∃ w ∈ (P.curve x).badAll,
      AbcAdaptation.Reference.Iut.residueChar w ≠ 2 ∧
      AbcAdaptation.Reference.Iut.residueChar w ≠ ℓ := by
    obtain ⟨w, hw, h⟩ := hP5
    exact ⟨w, (P.arith x).badAll_finite.mem_toFinset.mp hw, h⟩
  exact (P.curve x).sl_le_range_of_from_source (P.arith x) (P.tate x) hℓ (P.modRep x ℓ hℓ)
    h5 hP2' hP4 hP5' A

variable (P : CurveProviders) (K : CompactlyBounded) (d : ℕ)

/-- **The inputs of IUT IV, Corollary 2.2 for the tripod**, from the curves `E_λ/F_λ` of the
points, the facts proved in this file, the isolated hypotheses `CurveFactsProp`, the core
finiteness `CoreFinitenessHyp` (a theorem for the model geometry, `Iut.Tripod.coreFiniteness`),
the height comparison `LegendreHeightHyp` (proved in `Height.lean`), the `2`-adic and conductor
bounds (proved in `TwoAdic.lean`, `LogCond.lean`), and the Northcott property `NorthcottHyp`. -/
noncomputable def curveInputs {AG : AnabelianGeometry.{0}} {TK : ℝ}
    (CF : CurveFactsProp P K d TK) (hcore : CoreFinitenessHyp P K d AG) (hN : NorthcottHyp)
    (hdeg3 : ∀ x : Pt, TorsionDegreeBound x.1 3) (hdeg5 : ∀ x : Pt, TorsionDegreeBound x.1 5)
    (hh : LegendreHeightHyp P K) (hB : TwoAdicBoundHyp P K (max (4 * K.c) 0))
    (hge : LogCondGeHyp P) (hle : LogCondLeHyp P) :
    CurveInputs tripodTheory AG K d where
  h := P.h
  curve x _ := P.curve x
  arith x _ := P.arith x
  tate x _ := P.tate x
  modRep x _ ℓ hℓ := P.modRep x ℓ hℓ
  height_eq _ _ := rfl
  deg_le x hx := by
    refine (deg_le x _ _ (hdeg3 x) (hdeg5 x)).trans ?_
    exact Nat.mul_le_mul_left _ hx.2
  dmod_le x hx := (dmod_le x _ _).trans hx.2
  htCan_equiv := hh
  northcott := northcott_of_equiv hN K d hh
  B := max (4 * K.c) 0
  B_nonneg := le_max_right _ _
  heightEq_two_le x hx := hB x hx.1
  HasCyclicSubgroup x ℓ := (P.curve x).HasCyclicSubgroup ℓ
  TK := TK
  cyclic_bound := CF.cyclic
  sl2_of x _ ℓ hℓ := sl2Image P x ℓ hℓ
  logDiff_eq x _ := logDiff_eq x _ _
  excCore_finite := hcore
  logCond_ge x _ := hge x
  logCond_le x _ := hle x

/-- The independently packaged constructor gives exactly the record used by P7. -/
theorem curveInputs_eq_from_source {AG : AnabelianGeometry.{0}} {TK : ℝ}
    (CF : CurveFactsProp P K d TK) (hcore : CoreFinitenessHyp P K d AG) (hN : NorthcottHyp)
    (hh : LegendreHeightHyp P K) (hB : TwoAdicBoundHyp P K (max (4 * K.c) 0)) :
    curveInputs P K d CF hcore hN torsionDegreeBound_three' torsionDegreeBound_five'
        hh hB (logCondGe P) (logCondLe P) =
      curveInputs_from_source P K d CF hcore hN hh hB := rfl

end AbcAdaptation.Tripod

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

end FoundationAudit

namespace CurveInputsExpressionComparison
open Lean Elab Term Meta FoundationAudit

def relocateName (maps : Array (Name × Name)) (n : Name) : Except String Name := do
  if let some pair := maps.find? (fun pair => pair.1 == n) then
    return pair.2
  if (`Iut.Tripod).isPrefixOf n then
    return n.replacePrefix `Iut.Tripod `AbcAdaptation.Tripod
  if #[`Iut, `Genl, `TateCurvesTheta, `DiscrepancyEquiv, `DiscrepancyLE].any (·.isPrefixOf n) then
    return `AbcAdaptation.Reference ++ n
  if (`_private).isPrefixOf n then throw s!"Unmapped private reference constant {n}"
  return n

/- Decode a kernel expression from the reference environment. -/
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

partial def outerBinderPlacement (e : Expr) : Array String :=
  match e with
  | .forallE _ _ body binder => #[encodeBinder binder] ++ outerBinderPlacement body
  | .mdata _ body => outerBinderPlacement body
  | _ => #[]

def sourceAxioms (row : Json) (key : String) : MetaM (Array String) := do
  let recorded ← checked (row.getObjValAs? (Array String) key)
  let allowed := standardAxioms.map Name.toString
  unless recorded.all (allowed.contains ·) do
    throwError "Unexpected source axioms in {key}: {recorded}"
  return recorded

end CurveInputsExpressionComparison

namespace CurveInputsAudit

open Lean Elab Term Meta FoundationAudit CurveInputsExpressionComparison

private def fieldNames : Array Name :=
  #[`h, `curve, `arith, `tate, `modRep, `height_eq, `deg_le, `dmod_le, `htCan_equiv,
    `northcott, `B, `B_nonneg, `heightEq_two_le, `HasCyclicSubgroup, `TK, `cyclic_bound,
    `sl2_of, `excCore_finite, `logDiff_eq, `logCond_ge, `logCond_le]

structure Assignment where
  field : Name
  type : Expr
  value : Expr
  inputs : Array Name
  projectUses : Array Name

structure Constructor where
  type : Expr
  axioms : Array Name
  assignments : Array Assignment

private def ownsProjectConstant (name : Name) : Bool :=
  #[`Iut, `Genl, `TateCurvesTheta, `AbcAdaptation, `DiscrepancyEquiv, `DiscrepancyLE].any
    (·.isPrefixOf name)

private def requiredInputs (field : Name) : Array Name :=
  match field with
  | `deg_le => #[`hdeg3, `hdeg5]
  | `htCan_equiv => #[`hh]
  | `northcott => #[`hN, `hh]
  | `heightEq_two_le => #[`hB]
  | `cyclic_bound => #[`CF]
  | `excCore_finite => #[`hcore]
  | `logCond_ge => #[`hge]
  | `logCond_le => #[`hle]
  | _ => #[]

private def requiredProjectUse (field : Name) : Option Name :=
  match field with
  | `h => some `Iut.Tripod.CurveProviders.h
  | `curve => some `Iut.Tripod.CurveProviders.curve
  | `arith => some `Iut.Tripod.CurveProviders.arith
  | `tate => some `Iut.Tripod.CurveProviders.tate
  | `modRep => some `Iut.Tripod.CurveProviders.modRep
  | `deg_le => some `Iut.Tripod.deg_le
  | `dmod_le => some `Iut.Tripod.dmod_le
  | `northcott => some `Iut.Tripod.northcott_of_equiv
  | `HasCyclicSubgroup => some `Iut.EllipticCurveData.HasCyclicSubgroup
  | `cyclic_bound => some `Iut.Tripod.CurveFactsProp.cyclic
  | `sl2_of => some `Iut.Tripod.sl2Image
  | `logDiff_eq => some `Iut.Tripod.logDiff_eq
  | _ => none

def projectName (name : Name) : Name :=
  if (`Iut.Tripod).isPrefixOf name then
    name.replacePrefix `Iut.Tripod `AbcAdaptation.Tripod
  else if #[`Iut, `Genl, `TateCurvesTheta, `DiscrepancyEquiv, `DiscrepancyLE].any
      (·.isPrefixOf name) then
    `AbcAdaptation.Reference ++ name
  else name

def readConstructor (name recordName : Name) (translate : Name → Name)
    (suppliedImage := false) : MetaM Constructor := do
  let env ← getEnv
  let some record := getStructureInfo? env recordName |
    throwError "Missing structure metadata for {recordName}"
  unless record.fieldNames == fieldNames do
    throwError "Unexpected CurveInputs fields {record.fieldNames}"
  let .defnInfo decl ← getConstInfo name |
    throwError "Expected the CurveInputs constructor definition {name}"
  unless decl.levelParams.isEmpty do throwError "Unexpected constructor universe parameters"
  let axioms ← collectAxioms name
  ensureStandard name.toString axioms
  let inferred ← kernelCheck name.toString decl.value
  kernelEq "constructor declared type" inferred decl.type
  let assignments ← lambdaTelescope decl.value fun binders body => do
    let names ← binders.mapM fun binder => return (← binder.fvarId!.getDecl).userName
    let expectedArity := if suppliedImage then 15 else 14
    unless names.size == expectedArity && (!suppliedImage || names[0]! == `sl2Image) do
      throwError "Unexpected constructor binders {names}"
    let body := body.consumeMData
    let .const ctorName levels := body.getAppFn |
      throwError "Expected a CurveInputs constructor application"
    let ctor ← getConstInfoCtor ctorName
    let arguments := body.getAppArgs
    unless ctor.induct == recordName && arguments.size == ctor.numParams + fieldNames.size do
      throwError "Unexpected record constructor {ctorName} with {arguments.size} arguments"
    let mut assignments : Array Assignment := #[]
    for index in [:fieldNames.size] do
      let field := fieldNames[index]!
      let offset := ctor.numParams + index
      let remainingType ← instantiateForall
        (ctor.type.instantiateLevelParams ctor.levelParams levels) (arguments.extract 0 offset)
      let .forallE _ fieldType _ _ := remainingType |
        throwError "Could not instantiate the dependent type of {field}"
      let value ← deltaExpand arguments[offset]!
        (fun n => name.isPrefixOf (privateToUserName n)) (allowOpaque := true)
      let projectUses := (value.getUsedConstants.map privateToUserName).filter ownsProjectConstant
      let mut inputs : Array Name := #[]
      for binder in [:binders.size] do
        if value.containsFVar binders[binder]!.fvarId! then
          inputs := inputs.push names[binder]!
      for input in requiredInputs field do
        unless inputs.contains input do throwError "Field {field} did not use {input}"
      if suppliedImage then
        unless (inputs.contains `sl2Image) == (field == `sl2_of) do
          throwError "Unexpected use of the explicit SL2 supplier in {field}"
      if let some expected := requiredProjectUse field then
        unless suppliedImage && field == `sl2_of do
          let expected := translate expected
          let isProjection : Expr → Bool
            | .proj base index _ =>
              ((getStructureInfo? env base).bind fun info => info.fieldNames[index]?).any
                (fun fieldName => base ++ fieldName == expected)
            | _ => false
          unless projectUses.contains expected || (value.find? isProjection).isSome do
            throwError "Field {field} did not use {expected}"
      let type ← mkForallFVars binders fieldType
      let value ← mkLambdaFVars binders value
      requireClosed s!"type of {field}" type
      requireClosed s!"value of {field}" value
      assignments := assignments.push { field, type, value, inputs, projectUses }
    return assignments
  return { type := decl.type, axioms, assignments }

def exportConstructor (name owner : Name) (constructor : Constructor)
    (suppliedImage := false) : MetaM Json := do
  let rows ← constructor.assignments.mapM fun field => do
    return Json.mkObj [
      ("field", toJson field.field.toString),
      ("type", ← checked (encodeExpr field.type)),
      ("value", ← checked (encodeExpr field.value)),
      ("inputs", toJson (field.inputs.map Name.toString)),
      ("projectUses", Json.arr (field.projectUses.map encodeName))]
  return Json.mkObj [
    ("schema", toJson "tripod-curve-inputs/v1"),
    ("compiler", toJson Lean.versionString),
    ("constructor", toJson name.toString),
    ("owner", toJson owner.toString),
    ("explicitSL2Supplier", toJson suppliedImage),
    ("type", ← checked (encodeExpr constructor.type)),
    ("axioms", toJson (constructor.axioms.map Name.toString)),
    ("fields", Json.arr rows)]

end CurveInputsAudit

namespace CurveInputsComparison

open Lean Elab Term Meta FoundationAudit CurveInputsAudit CurveInputsExpressionComparison

def checkSource (sourceFile : String) (native : CurveInputsAudit.Constructor) : MetaM Unit := do
  let source ← checked (Json.parse (← IO.FS.readFile sourceFile))
  unless (← checked (stringField source "schema")) == "tripod-curve-inputs/v1" &&
      (← checked (stringField source "compiler")) == "4.35.0-rc3" &&
      (← checked (stringField source "constructor")) == "Iut.Tripod.curveInputs" do
    throwError "Unexpected reference constructor evidence"
  let suppliedImage ← checked (source.getObjValAs? Bool "explicitSL2Supplier")
  let sourceOwner ← checked (stringField source "owner")
  if suppliedImage then
    unless sourceOwner.endsWith "QueryTripodCurveInputsReplay" do
      throwError "Expected the B1 source replay module, found {sourceOwner}"
  else
    unless sourceOwner == "Iut.Tripod.CurveFacts" do
      throwError "Expected the original CurveFacts module, found {sourceOwner}"
  let _ ← sourceAxioms source "axioms"
  let refFields ← checked (arrayField source "fields")
  unless refFields.size == native.assignments.size do
    throwError "Reference and target field counts differ"
  let some imageField := native.assignments.find? (fun a => a.field == `sl2_of) |
    throwError "Missing sl2_of field"
  let some imageName := imageField.value.getUsedConstants.find?
    (fun n => privateToUserName n == `AbcAdaptation.Tripod.sl2Image) |
    throwError "Missing local SL2 supplier"
  let relocate (e : Json) (isType : Bool) : MetaM Expr := do
    let translated ← checked (relocateExpr #[(`Iut.Tripod.sl2Image, imageName)] e)
    if !suppliedImage then return translated
    match translated.consumeMData with
    | .forallE `sl2Image supplyType body .default =>
      unless isType do throwError "Expected an SL2 supplier lambda in the reference value"
      let proof := Lean.mkConst imageName
      kernelEq "SL2 supply type" supplyType (← kernelCheck "target SL2 image theorem" proof)
      return body.instantiate1 proof
    | .lam `sl2Image supplyType body .default =>
      if isType then throwError "Expected an SL2 supplier quantifier in the reference type"
      let proof := Lean.mkConst imageName
      kernelEq "SL2 supply type" supplyType (← kernelCheck "target SL2 image theorem" proof)
      return body.instantiate1 proof
    | _ => throwError "Missing the explicit SL2 supplier binder in the source replay"
  let sourceType ← relocate (← checked (field source "type")) true
  unless outerBinderPlacement sourceType == outerBinderPlacement native.type do
    throwError "Constructor binder modes differ"
  kernelEq "curveInputs type" sourceType native.type
  let mut failed : Array Name := #[]
  for assignment in native.assignments do
    let fieldName := assignment.field.toString
    try
      let fieldRows := refFields.filter fun row => stringField row "field" == .ok fieldName
      unless fieldRows.size == 1 do
        throwError "Expected one reference field named {fieldName}"
      let row := fieldRows[0]!
      let sourceInputs ← checked (row.getObjValAs? (Array String) "inputs")
      let matchedInputs := if suppliedImage then sourceInputs.filter (· != "sl2Image") else sourceInputs
      unless matchedInputs == assignment.inputs.map Name.toString do
        throwError "Field {fieldName} uses different constructor inputs: {sourceInputs} and {assignment.inputs}"
      let sourceUses ← namesFromJson (← checked (field row "projectUses"))
      let mappedUses := if suppliedImage && assignment.field == `sl2_of then
          `AbcAdaptation.Tripod.sl2Image :: sourceUses.map projectName
        else sourceUses.map projectName
      let nativeUses := assignment.projectUses.toList
      unless mappedUses.all nativeUses.contains && nativeUses.all mappedUses.contains do
        throwError "Field {fieldName} references different project constants: {mappedUses} and {nativeUses}"
      let sourceFieldType ← relocate (← checked (field row "type")) true
      let sourceValue ← relocate (← checked (field row "value")) false
      kernelEq s!"{fieldName} type" sourceFieldType assignment.type
      kernelEq s!"{fieldName} right-hand side" sourceValue assignment.value
      logInfo m!"Matched {fieldName}"
    catch err =>
      failed := failed.push assignment.field
      logWarning err.toMessageData
  unless failed.isEmpty do throwError "Cross-version correspondence failed for {failed}"
  logInfo m!"Reference and target matched for {refFields.size} constructor fields"

end CurveInputsComparison

open Lean Elab Term Meta FoundationAudit CurveInputsAudit CurveInputsComparison in
run_meta do
  unless Lean.versionString == "4.33.1" do throwError "Expected Lean 4.33.1"
  let name := ``AbcAdaptation.Tripod.curveInputs
  let constructor ← readConstructor name ``AbcAdaptation.Reference.Iut.CurveInputs projectName
  let facts ← exportConstructor name (← getEnv).mainModule constructor
  let path ← absoluteEnv "TRIPOD_CURVE_INPUTS_FACTS"
  IO.FS.writeFile path (facts.compress ++ "\n")
  logInfo m!"Checked the {constructor.assignments.size} native target constructor fields"
  if let some sourceFile ← IO.getEnv "TRIPOD_CURVE_INPUTS_SOURCE_FACTS" then
    unless sourceFile.startsWith "/" do throwError "Expected an absolute reference evidence path"
    checkSource sourceFile constructor

#print axioms AbcAdaptation.Tripod.curveInputs

#print axioms AbcAdaptation.Tripod.curveInputs_eq_from_source
