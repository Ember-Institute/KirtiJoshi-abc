import Lean
import Definitions.Def_AbcAdaptation_Reference_Iut_Cor312_ThetaData_Places
import Definitions.Def_AbcAdaptation_Reference_Iut_Cor312_ThetaData_PointMap
import Definitions.Def_AbcAdaptation_Reference_Iut_Cor312_RationalPlace
import Definitions.Def_AbcAdaptation_Reference_Iut_Cor312_Procession
import Definitions.Def_AbcAdaptation_Reference_Iut_Cor312_PacketPresentation

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
namespace FoundationAudit
open Lean Elab Term Meta

structure Relocation where
  original : Name
  target : Name
  permutation : Option (Array Nat)
  expectedInstance : Option Bool

abbrev Relocations := Array Relocation

def projectName (n : Name) : Bool :=
  #[`Iut, `Genl, `AbcAdaptation, `Definitions, `Theorems, `Solutions].any (·.isPrefixOf n)

def standardModule (n : Name) : Bool :=
  #[`Init, `Lean, `Std, `Mathlib, `Batteries, `Aesop, `Qq, `Plausible,
    `ProofWidgets, `ImportGraph, `Cli, `LeanSearchClient].any (·.isPrefixOf n)

def relocated (rs : Relocations) (n : Name) : Except String Name := do
  if let some r := rs.find? (·.original == n) then return r.target
  if projectName n then throw s!"Unmapped project name {n}"
  return n

def inverseRelocated (rs : Relocations) (n : Name) : Except String Name := do
  if let some r := rs.find? (·.target == n) then return r.original
  if projectName n then throw s!"Unmapped wrapped name {n}"
  return n

def reorder (indices : Array Nat) (us : Array α) : Except String (Array α) := do
  unless indices.size == us.size && indices.toList.eraseDups.length == us.size do
    throw "Universe permutation has incorrect size or repeated indices"
  indices.mapM fun i => match us[i]? with
    | some u => pure u
    | none => throw "Universe permutation index out of range"

partial def decodeExpr (rs : Relocations) (j : Json) : Except String Expr := do
  let recur := decodeExpr rs
  match ← stringField j "kind" with
  | "bvar" => return .bvar (← (← field j "index").getNat?)
  | "sort" => return .sort (← decodeLevel (← field j "level"))
  | "const" =>
    let original ← decodeName (← field j "name")
    let target ← relocated rs original
    let mut levels ← (← arrayField j "levels").mapM decodeLevel
    if let some r := rs.find? (·.original == original) then
      if let some indices := r.permutation then levels ← reorder indices levels
    return .const target levels.toList
  | "app" => return .app (← recur (← field j "fn")) (← recur (← field j "arg"))
  | "lam" => return .lam (← decodeName (← field j "name")) (← recur (← field j "type")) (← recur (← field j "body")) (← decodeBinder (← stringField j "binder"))
  | "forall" => return .forallE (← decodeName (← field j "name")) (← recur (← field j "type")) (← recur (← field j "body")) (← decodeBinder (← stringField j "binder"))
  | "let" => return .letE (← decodeName (← field j "name")) (← recur (← field j "type")) (← recur (← field j "value")) (← recur (← field j "body")) (← (← field j "nondependent").getBool?)
  | "nat" => return .lit (.natVal (← (← field j "value").getNat?))
  | "string" => return .lit (.strVal (← stringField j "value"))
  | "proj" => return .proj (← relocated rs (← decodeName (← field j "name"))) (← (← field j "index").getNat?) (← recur (← field j "body"))
  | k => throw s!"Unknown Expr kind {k}"

def readRelocations (config : Json) : MetaM Relocations := do
  let mut result : Relocations := #[]
  for key in #["projectMap", "standardRenames"] do
    for row in ← checked (arrayField config key) do
      let original ← checked (decodeName (← checked (field row "originalName")))
      let target ← checked (decodeName (← checked (field row "targetName")))
      unless original.toString == (← checked (stringField row "original")) &&
        target.toString == (← checked (stringField row "target")) do
        throwError "Structural relocation name mismatch"
      if key == "standardRenames" then
        if projectName original || projectName target then
          throwError "Standard relocation contains project name"
        unless (← checked (stringField row "evidence")).length > 0 do
          throwError "Standard rename requires reviewed compiler/source evidence"
      else
        unless (`Iut).isPrefixOf original && (`AbcAdaptation.Reference.Iut).isPrefixOf target do
          throwError "Unexpected project relocation {original} -> {target}"
      if result.any (fun r => r.original == original || r.target == target) then
        throwError "Duplicate or non-injective relocation {original} -> {target}"
      let indicesJson ← checked (field row "targetToSourceUniverseIndices")
      let permutation ← if indicesJson == Json.null then pure none else
        pure (some (← checked ((← checked indicesJson.getArr?).mapM Json.getNat?)))
      let expectedInstance ← if key == "projectMap" then
        pure (some (← checked (row.getObjValAs? Bool "expectedIsInstance"))) else pure none
      result := result.push ⟨original, target, permutation, expectedInstance⟩
  return result

def requireClosed (label : String) (e : Expr) : MetaM Unit := do
  if e.hasMVar || e.hasFVar || e.hasLooseBVars then throwError "Open expression in {label}"

def kernelCheck (label : String) (e : Expr) : MetaM Expr := do
  requireClosed label e
  match Kernel.check (← getEnv) {} e with
  | .ok type => pure type
  | .error ex => throwKernelException ex

-- Kernel conversion assumes well-typed inputs. Check both terms and their types.
def kernelTermEq (label : String) (left right : Expr) : MetaM Unit := do
  let lt ← kernelCheck label left
  let rt ← kernelCheck label right
  match Kernel.isDefEq (← getEnv) {} lt rt with
  | .ok true => pure ()
  | .ok false => throwError "Kernel inferred types differ: {label}"
  | .error ex => throwKernelException ex
  match Kernel.isDefEq (← getEnv) {} left right with
  | .ok true => pure ()
  | .ok false => throwError "Kernel values/types differ: {label}"
  | .error ex => throwKernelException ex

def kernelTypeEq (label : String) (left right : Expr) : MetaM Unit := do
  for e in #[left, right] do
    match ← kernelCheck label e with
    | .sort _ => pure ()
    | _ => throwError "Expected type: {label}"
  kernelTermEq label left right

def allowedOwner (modules : Array Name) (name : Name) : MetaM Unit := do
  let some owner := moduleOf (← getEnv) name | throwError "No imported owner for {name}"
  unless standardModule owner || modules.contains owner do
    throwError "Forbidden dependency {name}, owner {owner}"
  if (`Iut).isPrefixOf name || (`Genl).isPrefixOf name then
    throwError "Unrelocated original project dependency {name}"

def auditDeclaration (modules : Array Name) (name : Name) : MetaM Json := do
  let ci ← getConstInfo name
  if let .axiomInfo _ := ci then throwError "Carrier declares an axiom {name}"
  let axs ← collectAxioms name
  let taxs ← expressionAxioms ci.type
  ensureStandard s!"carrier {name}" axs
  ensureStandard s!"carrier type {name}" taxs
  let value? := ci.value? (allowOpaque := true)
  let vaxs ← match value? with
    | some v => expressionAxioms v
    | none => pure #[]
  ensureStandard s!"carrier value {name}" vaxs
  for expr in #[ci.type] ++ value?.toArray do
    for dep in expr.getUsedConstants do allowedOwner modules dep
  if let .recInfo r := ci then
    for rule in r.rules do
      for dep in rule.rhs.getUsedConstants do allowedOwner modules dep
      ensureStandard s!"recursor rule {name}" (← expressionAxioms rule.rhs)
  return Json.mkObj [("name", toJson name.toString), ("constantKind", toJson (kind ci)),
    ("levelParams", Json.arr (ci.levelParams.toArray.map encodeName)),
    ("elaboratedExpr", ← checked (encodeExpr ci.type)),
    ("binderInventory", toJson (binderInventory ci.type)),
    ("axioms", toJson (axs.map Name.toString)),
    ("typeAxioms", toJson (taxs.map Name.toString)),
    ("valueAxioms", toJson (vaxs.map Name.toString)),
    ("hasSorryAx", toJson false), ("hasValue", toJson value?.isSome),
    ("isInstance", toJson (Lean.Meta.isInstanceCore (← getEnv) name))]

-- Paths distinguish binders at different positions even when the flattened
-- BinderInfo sequence is the same. Kernel conversion itself erases BinderInfo.
partial def binderPlacement (e : Expr) (path := "root") : Array String :=
  match e with
  | .forallE _ t b bi => #[path ++ ":forall:" ++ encodeBinder bi] ++
      binderPlacement t (path ++ ".domain") ++ binderPlacement b (path ++ ".body")
  | .lam _ t b bi => #[path ++ ":lambda:" ++ encodeBinder bi] ++
      binderPlacement t (path ++ ".domain") ++ binderPlacement b (path ++ ".body")
  | .app f a => binderPlacement f (path ++ ".fn") ++ binderPlacement a (path ++ ".arg")
  | .letE _ t v b _ => binderPlacement t (path ++ ".type") ++
      binderPlacement v (path ++ ".value") ++ binderPlacement b (path ++ ".body")
  | .mdata _ e => binderPlacement e path
  | .proj _ _ e => binderPlacement e (path ++ ".projected")
  | _ => #[]

def canonicalLevels (n : Nat) : List Name :=
  (List.range n).map fun i => Name.num (Name.str .anonymous "_foundationAuditUniverse") i

def compareRecord (rs : Relocations) (record : Json) (target : ConstantInfo) : MetaM Json := do
  let original ← checked (decodeName (← checked (field record "nameExpr")))
  let sourceParams ← namesFromJson (← checked (field record "levelParams"))
  unless sourceParams.eraseDups == sourceParams do throwError "Duplicate universe parameter {original}"
  unless sourceParams.length == target.levelParams.length do
    throwError "Universe parameter count differs for {original}"
  unless (← checked (stringField record "constantKind")) == kind target do
    throwError "ConstantInfo kind differs for {original}"
  for key in #["axioms", "typeAxioms", "valueAxioms"] do
    for ax in ← checked (arrayField record key) do
      unless (standardAxioms.map fun n => Json.str n.toString).contains ax do
        throwError "Unexpected original axiom for {original}"
  let canonical := (canonicalLevels sourceParams.length).map Level.param
  let some rel := rs.find? (·.original == original) | throwError "Missing map entry {original}"
  let some expectedInstance := rel.expectedInstance |
    throwError "Missing accepted-graph instance flag {original}"
  unless Lean.Meta.isInstanceCore (← getEnv) target.name == expectedInstance do
    throwError "Instance registry membership differs for {original}"
  let targetLevels ← match rel.permutation with
    | none => pure canonical
    | some indices => do
      let reordered ← checked (reorder indices canonical.toArray)
      pure reordered.toList
  let sourceTypeRaw ← checked (decodeExpr rs (← checked (field record "elaboratedExpr")))
  let sourceType := sourceTypeRaw.instantiateLevelParams sourceParams canonical
  let targetType := target.type.instantiateLevelParams target.levelParams targetLevels
  unless (← checked (record.getObjValAs? (Array String) "binderInventory")) == binderInventory sourceType do
    throwError "Source serialization BinderInfo inventory differs for {original}"
  unless binderInventory sourceType == binderInventory targetType do
    throwError "Full type BinderInfo inventory differs for {original}"
  unless binderPlacement sourceType == binderPlacement targetType do
    throwError "BinderInfo placement inside the type differs for {original}"
  kernelTypeEq s!"original versus target type {original}" sourceType targetType
  unless (← checked (field record "computationShape")) ==
      (← checked (computationShape target (inverseRelocated rs))) do
    throwError "Inductive/constructor/recursor computation shape differs for {original}"
  let sourceProp ← checked (record.getObjValAs? Bool "isProposition")
  unless sourceProp == (← isProp target.type) do throwError "Proposition status differs {original}"
  let mut comparedValue := false
  let originalValueJson ← checked (field record "valueExpr")
  -- Proof declarations are audited by exact type and axiom closure. For a data
  -- value containing proof fields, Kernel.isDefEq itself uses proof irrelevance.
  if !sourceProp && originalValueJson != Json.null then
    let sourceValue := (← checked (decodeExpr rs originalValueJson)).instantiateLevelParams sourceParams canonical
    let some targetValue := target.value? (allowOpaque := true) |
      throwError "Target value missing for {original}"
    let targetValue := targetValue.instantiateLevelParams target.levelParams targetLevels
    kernelTypeEq s!"original value inhabits original type {original}"
      (← kernelCheck s!"original value {original}" sourceValue) sourceType
    kernelTypeEq s!"target value inhabits target type {original}"
      (← kernelCheck s!"target value {original}" targetValue) targetType
    kernelTermEq s!"original versus target computational value {original}" sourceValue targetValue
    comparedValue := true
  let rules ← checked (arrayField record "recursorRuleRhs")
  let mut comparedRules := 0
  if let .recInfo r := target then
    unless rules.size == r.rules.length do throwError "Recursor rule count differs {original}"
    for i in [:rules.size] do
      let sourceRhs := (← checked (decodeExpr rs rules[i]!)).instantiateLevelParams sourceParams canonical
      let targetRhs := r.rules[i]!.rhs.instantiateLevelParams target.levelParams targetLevels
      kernelTermEq s!"recursor rule {original} #{i}" sourceRhs targetRhs
      comparedRules := comparedRules + 1
  else
    unless rules.isEmpty do throwError "Unexpected original recursor rules {original}"
  let sourceStruct ← checked (field record "structure")
  if sourceStruct != Json.null then
    let some info := getStructureInfo? (← getEnv) target.name |
      throwError "Target structure metadata missing {target.name}"
    unless (← checked (field sourceStruct "fieldsInConstructorOrder")) ==
        toJson (info.fieldNames.map Name.toString) do
      throwError "Structure field order differs {original}"
    let projections ← namesFromJson (← checked (field sourceStruct "projections"))
    let targetProjections ← projections.toArray.mapM fun n => checked (relocated rs n)
    unless targetProjections == info.fieldInfo.map (·.projFn) do
      throwError "Structure accessor identities/order differ {original}"
    for p in targetProjections do
      unless rs.any (·.target == p) do throwError "Unaudited structure accessor {p}"
  return Json.mkObj [("original", toJson original.toString), ("target", toJson target.name.toString),
    ("sourceRecord", record), ("kernelTypeEqual", toJson true),
    ("allExpressionBinderInfoEqual", toJson true),
    ("binderInfoPlacementEqual", toJson true),
    ("computationShapeEqual", toJson true), ("kernelValueEqual", toJson comparedValue),
    ("proofDeclaration", toJson sourceProp), ("recursorRulesCompared", toJson comparedRules),
    ("instanceRegistryMatchesAcceptedGraph", toJson true),
    ("expectedIsInstance", toJson expectedInstance),
    ("universeOriginalOrder", Json.arr (sourceParams.toArray.map encodeName)),
    ("universeTargetOrder", Json.arr (target.levelParams.toArray.map encodeName)),
    ("targetToSourceUniverseIndices", match rel.permutation with | none => Json.null | some a => toJson a)]

def audit : TermElabM Unit := do
  unless Lean.versionString == "4.33.1" do throwError "Expected platform4.33.1, got {Lean.versionString}"
  let config ← jsonFile (← absoluteEnv "FOUNDATION_AUDIT_CONFIG")
  unless (← checked (stringField config "schema")) == "foundation-kernel-audit-config-v2" do
    throwError "Wrong config schema"
  let source ← jsonFile (← checked (stringField config "originalExprFile"))
  unless (← checked (stringField source "schema")) == "foundation-original-exprs-v2" &&
      (← checked (stringField source "compilerVersion")) == "4.35.0-rc3" do
    throwError "Wrong original compiler/schema"
  for key in #["inventorySha256", "graphSha256"] do
    unless (← checked (field source key)) == (← checked (field config key)) do
      throwError "Input provenance hash differs: {key}"
  let records ← checked (arrayField source "records")
  unless records.size == 151 do throwError "Expected151 original records"
  let moduleRows ← checked (arrayField config "modules")
  unless moduleRows.size == 5 do throwError "Expected five target modules"
  let modules ← moduleRows.mapM fun row => return (← checked (stringField row "target")).toName
  let rs ← readRelocations config
  let env ← getEnv
  for imported in env.header.moduleNames do
    unless standardModule imported || modules.contains imported do
      throwError "Forbidden imported module {imported}"
  let declarations := env.constants.fold (fun acc n _ =>
    if (moduleOf env n).any modules.contains then acc.push n else acc) (#[] : Array Name)
  unless declarations.size > 0 do throwError "No carrier declarations"
  let mut ownedReports := #[]
  let mut comparisons := #[]
  let mut seenOriginal : Array Name := #[]
  let mut requiredCount := 0
  let mut missingOptional := #[]
  for record in records do
    let original ← checked (decodeName (← checked (field record "nameExpr")))
    if seenOriginal.contains original then throwError "Duplicate original record {original}"
    seenOriginal := seenOriginal.push original
    unless original.toString == (← checked (stringField record "name")) do
      throwError "Original name identity differs"
    let sourceOwner ← checked (stringField record "module")
    let ownerRows := moduleRows.filter fun row => (stringField row "original").toOption == some sourceOwner
    unless ownerRows.size == 1 do throwError "Original module not in configured five: {sourceOwner}"
    unless (← checked (field record "sourceSha256")) ==
        (← checked (field ownerRows[0]! "sourceSha256")) do throwError "Original source hash differs"
    let selected ← checked (record.getObjValAs? Bool "selected")
    let targetName ← checked (relocated rs original)
    if selected then requiredCount := requiredCount + 1
    unless env.contains targetName do
      if selected then throwError "Required generated/source declaration missing: {original} -> {targetName}"
      missingOptional := missingOptional.push (toJson original.toString)
      continue
    unless moduleOf env targetName == some (← checked (stringField ownerRows[0]! "target")).toName do
      throwError "Wrong target artifact owner {targetName}"
    comparisons := comparisons.push (← compareRecord rs record (← getConstInfo targetName))
  unless requiredCount == 83 do throwError "Expected83 mandatory selected comparisons"
  let mut targetOnly := #[]
  for name in declarations.qsort Name.lt do
    ownedReports := ownedReports.push (← auditDeclaration modules name)
    if !(rs.any fun r => r.target == name && seenOriginal.contains r.original) then
      targetOnly := targetOnly.push (toJson name.toString)
  let output ← checked (stringField config "outputDir")
  IO.FS.createDirAll output
  IO.FS.writeFile (output ++ "/foundation-kernel-audit.json") ((Json.mkObj [
    ("schema", toJson "foundation-kernel-audit-v2"), ("compilerVersion", toJson Lean.versionString),
    ("originalCompilerVersion", toJson "4.35.0-rc3"),
    ("configuration", config), ("requiredComparedCount", toJson requiredCount),
    ("comparisons", Json.arr comparisons), ("ownedDeclarations", Json.arr ownedReports),
    ("missingUnselectedOriginalDeclarations", Json.arr missingOptional),
    ("targetOnlyCompilerDeclarations", Json.arr targetOnly),
    ("allOwnedTypeValueClosuresStandardAxiomsOnly", toJson true),
    ("hasSorryAx", toJson false),
    ("targetOnlyPolicy", toJson "all reported and axiom audited; review source-command generation provenance before acceptance")]).pretty ++ "\n")
  logInfo s!"Foundation audit: {requiredCount} mandatory exact types; {comparisons.size} total original/target pairs; {ownedReports.size} artifact-owned axiom closures"

end FoundationAudit

syntax (name := auditFoundation) "audit_foundation_carriers" : command
@[command_elab auditFoundation] def elabAuditFoundation : Lean.Elab.Command.CommandElab := fun _ => do
  Lean.Elab.Command.liftTermElabM FoundationAudit.audit

audit_foundation_carriers
