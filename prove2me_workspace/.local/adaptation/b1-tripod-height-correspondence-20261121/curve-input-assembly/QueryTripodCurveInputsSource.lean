/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors

Original repository https://github.com/lana-agents/iut
Original revision 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8
Original path Iut/Tripod/CurveFacts.lean (sl2Image and curveInputs)
-/
import Lean
import Iut.Tripod.CurveFacts

set_option autoImplicit false

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

def readConstructor (name recordName : Name) (translate : Name → Name) : MetaM Constructor := do
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
    unless names.size == 14 do throwError "Unexpected constructor binders {names}"
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
      if let some expected := requiredProjectUse field then
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

def exportConstructor (name owner : Name) (constructor : Constructor) : MetaM Json := do
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
    ("explicitSL2Supplier", toJson false),
    ("type", ← checked (encodeExpr constructor.type)),
    ("axioms", toJson (constructor.axioms.map Name.toString)),
    ("fields", Json.arr rows)]

end CurveInputsAudit

open Lean Elab Term Meta FoundationAudit CurveInputsAudit in
run_meta do
  unless Lean.versionString == "4.35.0-rc3" do throwError "Expected Lean 4.35.0-rc3"
  let name := ``Iut.Tripod.curveInputs
  let owner := `Iut.Tripod.CurveFacts
  unless moduleOf (← getEnv) name == some owner do
    throwError "Expected the constructor defined in Iut.Tripod.CurveFacts"
  let constructor ← readConstructor name ``Iut.CurveInputs id
  let facts ← exportConstructor name owner constructor
  let path ← absoluteEnv "TRIPOD_CURVE_INPUTS_FACTS"
  IO.FS.writeFile path (facts.compress ++ "\n")
  logInfo m!"Exported {constructor.assignments.size} reference constructor fields"

#print axioms Iut.Tripod.curveInputs
#print axioms Iut.ThetaLocalData.logDK_eq_zero
#print axioms Iut.LocalTheory.packetVol_scaledIntegral
#print axioms Iut.TowerArithmetic.vol_finite
#print axioms Iut.TowerArithmetic.vol_infinite
#print axioms Iut.TowerArithmetic.localEstimate
