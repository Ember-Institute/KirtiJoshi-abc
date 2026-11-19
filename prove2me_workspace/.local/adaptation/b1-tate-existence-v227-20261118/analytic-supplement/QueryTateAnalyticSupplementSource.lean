import Lean
import TateCurvesTheta.TateCurve.A6Series

/-! Stable JSON for *actual compiler Exprs*. No pretty-printer text is decoded here.
    Metadata is erased; local/metavariables are rejected. -/
namespace FoundationAudit
open Lean

-- Preserve actual Name components, including numeric components; do not use String.toName.
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
  -- moduleNames maps the entire module array; use the indexed record directly.
  let imported ← env.header.modules[index.toNat]?
  return imported.module

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

-- Preserve inductive/constructor/recursor computation metadata as well as types.
def computationShape (ci : ConstantInfo) (rename : Name → Except String Name) : Except String Json := do
  let ns := fun xs : List Name => do
    return Json.arr (← xs.toArray.mapM fun n => return encodeName (← rename n))
  match ci with
  | .inductInfo i => return Json.mkObj [
      ("all", ← ns i.all), ("constructors", ← ns i.ctors),
      ("numParams", toJson i.numParams), ("numIndices", toJson i.numIndices),
      ("numNested", toJson i.numNested), ("isRec", toJson i.isRec),
      ("isUnsafe", toJson i.isUnsafe), ("isReflexive", toJson i.isReflexive)]
  | .ctorInfo i => return Json.mkObj [
      ("inductive", encodeName (← rename i.induct)), ("index", toJson i.cidx),
      ("numParams", toJson i.numParams), ("numFields", toJson i.numFields),
      ("isUnsafe", toJson i.isUnsafe)]
  | .recInfo i => return Json.mkObj [
      ("all", ← ns i.all), ("numParams", toJson i.numParams),
      ("numIndices", toJson i.numIndices), ("numMotives", toJson i.numMotives),
      ("numMinors", toJson i.numMinors), ("k", toJson i.k), ("isUnsafe", toJson i.isUnsafe),
      ("rules", Json.arr (← i.rules.toArray.mapM fun r => return Json.mkObj [
        ("constructor", encodeName (← rename r.ctor)), ("numFields", toJson r.nfields)]))]
  | .defnInfo i => return Json.mkObj [("safety", toJson (reprStr i.safety))]
  | _ => return Json.null

-- Include elaborator-visible field and parent metadata, not only kernel arities.
def structureShape (info : StructureInfo) (rename : Name → Except String Name) : Except String Json := do
  let fields ← info.fieldInfo.mapM fun p => do
    let subobject ← match p.subobject? with
      | none => pure Json.null
      | some n => pure (encodeName (← rename n))
    return Json.mkObj [
      ("fieldName", encodeName p.fieldName), ("projection", encodeName (← rename p.projFn)),
      ("subobject", subobject), ("binderInfo", toJson (encodeBinder p.binderInfo)),
      ("hasAutoParam", toJson p.autoParam?.isSome)]
  let parents ← info.parentInfo.mapM fun p => do
    return Json.mkObj [
      ("structure", encodeName (← rename p.structName)), ("subobject", toJson p.subobject),
      ("projection", encodeName (← rename p.projFn))]
  return Json.mkObj [
    ("structure", encodeName (← rename info.structName)),
    ("fieldNamesInConstructorOrder", Json.arr (info.fieldNames.map encodeName)),
    ("fieldsSortedByName", Json.arr fields), ("parentsInExtendsOrder", Json.arr parents)]

def telescopeJson (type : Expr) : MetaM Json :=
  forallTelescope type fun xs result => do
    let binders ← xs.mapM fun x => do
      let d ← x.fvarId!.getDecl
      return Json.mkObj [("name", toJson d.userName.toString),
        ("binderInfo", toJson (encodeBinder d.binderInfo)),
        ("typeDisplay", toJson (← ppExpr d.type).pretty)]
    return Json.mkObj [("binders", Json.arr binders),
      ("resultDisplay", toJson (← ppExpr result).pretty)]

end FoundationAudit
namespace B1SourceRootActualFacts
open Lean Elab Term Meta FoundationAudit

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

end B1SourceRootActualFacts
namespace B1SourceActualClosure
open Lean Elab Term Meta FoundationAudit B1SourceRootActualFacts

def namesJson (ns : Array Name) : Json := Json.arr (ns.map encodeName)

abbrev RecursorIndex := Std.HashMap Name (Array Name)

def actualMetadata (recursorsByInduct : RecursorIndex) (ci : ConstantInfo) : MetaM (Json × Array Name × Array Expr) := do
  let env ← getEnv
  let mut dependencies : Array Name := #[]
  let mut expressions : Array Expr := #[]
  let structureFacts ← match getStructureInfo? env ci.name with
    | none => pure Json.null
    | some info => do
      let mut fieldAutoParams : Array Json := #[]
      for f in info.fieldInfo do
        match f.autoParam? with
        | none => fieldAutoParams := fieldAutoParams.push Json.null
        | some e =>
          expressions := expressions.push e
          fieldAutoParams := fieldAutoParams.push (← checked (encodeExpr e))
      for f in info.fieldInfo do
        dependencies := dependencies.push f.projFn
        if let some p := f.subobject? then dependencies := dependencies.push p
      for p in info.parentInfo do
        dependencies := dependencies.push p.structName |>.push p.projFn
      pure (Json.mkObj [
        ("completeMetadata",← checked (structureShape info pure)),
        ("fieldAutoParamExprs",Json.arr fieldAutoParams)])
  let mut recursorRules : Array Json := #[]
  match ci with
  | .inductInfo i =>
    dependencies := dependencies ++ i.all.toArray ++ i.ctors.toArray
    -- Find compiler-owned recursor names from actual recursor metadata. Never synthesize .rec names.
    dependencies := dependencies ++ (recursorsByInduct[ci.name]?).getD #[]
  | .ctorInfo c => dependencies := dependencies.push c.induct
  | .recInfo r =>
    dependencies := dependencies ++ r.all.toArray
    for rule in r.rules do
      dependencies := dependencies.push rule.ctor
      expressions := expressions.push rule.rhs
      recursorRules := recursorRules.push (Json.mkObj [
        ("constructor",encodeName rule.ctor),("numFields",toJson rule.nfields),
        ("rhs",← checked (encodeExpr rule.rhs))])
  | _ => pure ()
  return (Json.mkObj [
    ("computationShape",← checked (computationShape ci pure)),
    ("structure",structureFacts),("recursorRules",Json.arr recursorRules)], dependencies, expressions)

def fullRecord (recursorsByInduct : RecursorIndex) (cache : AxiomCache) (ci : ConstantInfo) (mode : String)
    (readValue : Bool) : MetaM (Json × Array (Name × String)) := do
  let env ← getEnv
  requireClosed s!"actual TYPE {ci.name}" ci.type
  let value := if readValue then ci.value? (allowOpaque := true) else none
  let mut inferredType := Json.null
  if let some v := value then
    inferredType := ← checked (encodeExpr (← checkedValueType ci.name.toString v ci.type))
  let axs ← cachedAxioms cache ci.name
  let taxs ← expressionAxioms cache ci.type
  let vaxs ← match value with
    | none => pure #[]
    | some v => expressionAxioms cache v
  for xs in #[axs,taxs,vaxs] do ensureStandard ci.name.toString xs
  let (metadata, metadataNames, metadataExprs) ← actualMetadata recursorsByInduct ci
  let mut deps : Array (Name × String) := #[]
  for n in ci.type.getUsedConstants do deps := deps.push (n,"actual-TYPE")
  if let some v := value then
    for n in v.getUsedConstants do deps := deps.push (n,"actual-value")
  for n in metadataNames do deps := deps.push (n,"compiler-metadata")
  for e in metadataExprs do
    for n in e.getUsedConstants do deps := deps.push (n,"metadata-Expr")
  let prop ← isProp ci.type
  let owner := moduleOf env ci.name
  let closedSupport := prop && ci.levelParams.isEmpty && value.isSome
  let record := Json.mkObj [
    ("record",toJson "fullActualFact"),("name",toJson ci.name.toString),("nameExpr",encodeName ci.name),
    ("owner",toJson (owner.map Name.toString)),("ownerNameExpr",owner.map encodeName |>.getD Json.null),
    ("traversalMode",toJson mode),("kind",toJson (kind ci)),
    ("levelParams",namesJson ci.levelParams.toArray),
    ("actualTypeExpr",← checked (encodeExpr ci.type)),
    ("actualValueExpr",← match value with | none => pure Json.null | some v => checked (encodeExpr v)),
    ("valueRead",toJson value.isSome),("isProposition",toJson prop),
    ("closedZeroUniversePropSupport",toJson closedSupport),
    ("isInstance",toJson (Lean.Meta.isInstanceCore env ci.name)),
    ("binderInventory",toJson (binderInventory ci.type)),("telescope",← telescopeJson ci.type),
    ("directTypeConstants",namesJson (ci.type.getUsedConstants.qsort Name.lt)),
    ("directValueConstants",namesJson ((value.map Expr.getUsedConstants).getD #[] |>.qsort Name.lt)),
    ("metadata",metadata),
    ("kernelInferredValueTypeExpr",inferredType),
    ("kernelValueTypeMatchesActualTYPE",toJson value.isSome),
    ("axioms",toJson (axs.qsort Name.lt |>.map Name.toString)),
    ("typeAxioms",toJson (taxs.qsort Name.lt |>.map Name.toString)),
    ("valueAxioms",toJson (vaxs.qsort Name.lt |>.map Name.toString)),
    ("hasSorryAx",toJson (axs.contains `sorryAx))]
  return (record,deps)

def sourceRoots : Array (Name × Name) := #[
  (`TateCurvesTheta.TateParameter.summable_a₆Coeff_qFactor, `TateCurvesTheta.TateCurve.A6Series),
  (`TateCurvesTheta.TateParameter.tateCurve_a₁, `TateCurvesTheta.TateCurve.Weierstrass),
  (`TateCurvesTheta.TateParameter.tateCurve_a₂, `TateCurvesTheta.TateCurve.Weierstrass),
  (`TateCurvesTheta.TateParameter.tateCurve_a₃, `TateCurvesTheta.TateCurve.Weierstrass),
  (`TateCurvesTheta.TateParameter.tateCurve_a₄, `TateCurvesTheta.TateCurve.Weierstrass),
  (`TateCurvesTheta.TateParameter.tateCurve_a₆, `TateCurvesTheta.TateCurve.Weierstrass)]

run_meta do
  unless Lean.versionString == "4.35.0-rc3" do
    throwError "Expected Lean 4.35.0-rc3 for the source export"
  let output ← absoluteEnv "B1_TATE_ANALYTIC_SUPPLEMENT_SOURCE"
  let env ← getEnv
  let cache ← IO.mkRef ({} : Std.HashMap Name (Array Name))
  let records ← sourceRoots.mapM fun (name, owner) => do
    let ci ← getConstInfo name
    unless moduleOf env name == some owner do
      throwError "Unexpected source module for {name}, expected {owner}"
    unless kind ci == "theorem" && (ci.value? (allowOpaque := true)).isSome do
      throwError "Expected an imported theorem with its proof for {name}"
    let (record, _) ← fullRecord {} cache ci "source-tate-analytic-supplement" true
    return record
  let report := Json.mkObj [
    ("schema", toJson "b1-tate-analytic-supplement-source/v1"),
    ("compilerVersion", toJson Lean.versionString),
    ("records", Json.arr records)]
  IO.FS.writeFile output (report.compress ++ "\n")
  logInfo m!"Exported {records.size} Tate analytic source theorems with full proofs"

end B1SourceActualClosure
