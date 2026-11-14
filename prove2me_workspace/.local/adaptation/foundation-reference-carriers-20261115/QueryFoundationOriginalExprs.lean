import Lean
import Iut.Cor312.ThetaData.Places
import Iut.Cor312.ThetaData.PointMap
import Iut.Cor312.RationalPlace
import Iut.Cor312.Procession
import Iut.Cor312.PacketPresentation

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
  env.header.moduleNames[index.toNat]?

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
namespace FoundationOriginalExport
open Lean FoundationAudit

run_meta do
  unless Lean.versionString == "4.35.0-rc3" do
    throwError "Expected source compiler 4.35.0-rc3, got {Lean.versionString}"
  let config ← jsonFile (← absoluteEnv "FOUNDATION_EXPORT_CONFIG")
  let entries ← checked (arrayField config "records")
  unless entries.size == 151 do throwError "Expected 151 original declarations"
  let mut seen : Array Name := #[]
  let mut records : Array Json := #[]
  let mut selectedCount := 0
  for entry in entries do
    let name ← checked (decodeName (← checked (field entry "nameExpr")))
    unless name.toString == (← checked (stringField entry "name")) do
      throwError "Structural source name mismatch"
    if seen.contains name then throwError "Duplicate original declaration {name}"
    seen := seen.push name
    let ci ← getConstInfo name
    let sourceModule ← checked (stringField entry "module")
    unless moduleOf (← getEnv) name == some sourceModule.toName do
      throwError "Original owner mismatch for {name}"
    if let .axiomInfo _ := ci then throwError "Original declares an axiom: {name}"
    let axs ← collectAxioms name
    let taxs ← expressionAxioms ci.type
    let value? := ci.value? (allowOpaque := true)
    let vaxs ← match value? with
      | some value => expressionAxioms value
      | none => pure #[]
    ensureStandard s!"original {name}" axs
    ensureStandard s!"original type {name}" taxs
    ensureStandard s!"original value {name}" vaxs
    let valueJson ← match value? with
      | some value => checked (encodeExpr value)
      | none => pure Json.null
    let selected ← checked (entry.getObjValAs? Bool "selected")
    if selected then selectedCount := selectedCount + 1
    let recRules ← match ci with
      | .recInfo i => i.rules.toArray.mapM fun rule => checked (encodeExpr rule.rhs)
      | _ => pure #[]
    let structJson := match getStructureInfo? (← getEnv) name with
      | none => Json.null
      | some info => Json.mkObj [
          ("fieldsInConstructorOrder", toJson (info.fieldNames.map Name.toString)),
          ("projections", Json.arr (info.fieldInfo.map fun p => encodeName p.projFn))]
    records := records.push (Json.mkObj [
      ("name", toJson name.toString), ("nameExpr", encodeName name),
      ("module", toJson sourceModule), ("sourceSha256", ← checked (field entry "sourceSha256")),
      ("selected", toJson selected), ("constantKind", toJson (kind ci)),
      ("levelParams", Json.arr (ci.levelParams.toArray.map encodeName)),
      ("elaboratedExpr", ← checked (encodeExpr ci.type)),
      ("binderInventory", toJson (binderInventory ci.type)),
      ("telescope", ← telescopeJson ci.type),
      ("isProposition", toJson (← Lean.Meta.isProp ci.type)),
      ("valueExpr", valueJson), ("recursorRuleRhs", Json.arr recRules),
      ("computationShape", ← checked (computationShape ci pure)), ("structure", structJson),
      ("axioms", toJson (axs.map Name.toString)),
      ("typeAxioms", toJson (taxs.map Name.toString)),
      ("valueAxioms", toJson (vaxs.map Name.toString))])
  unless selectedCount == 83 do throwError "Expected 83 selected declarations"
  let path ← checked (stringField config "outputFile")
  IO.FS.writeFile path ((Json.mkObj [
    ("schema", toJson "foundation-original-exprs-v2"),
    ("compilerVersion", toJson Lean.versionString),
    ("inventorySha256", ← checked (field config "inventorySha256")),
    ("graphSha256", ← checked (field config "graphSha256")),
    ("serialization", toJson "actual ConstantInfo.type/value; recursive metadata erasure; structural Names; no pretty-printer round trip"),
    ("selectedCount", toJson selectedCount), ("records", Json.arr records)]).pretty ++ "\n")
  logInfo s!"Exported {records.size} original compiler declarations, {selectedCount} required, to {path}"

end FoundationOriginalExport
