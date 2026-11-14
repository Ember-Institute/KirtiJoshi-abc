import Lean
import Theorems.Thm_AbcAdaptation_Reference_Iut_ChebyshevBound_exists_prime_notMem
import Solutions.Sol_AbcAdaptation_Reference_Iut_ChebyshevBound_exists_prime_notMem

set_option pp.fullNames true
set_option pp.funBinderTypes true
set_option pp.piBinderTypes true
set_option pp.universes true


/-! Stable JSON for *actual compiler Exprs*. No pretty-printer text is decoded here.
    Metadata is erased; local/metavariables are rejected. -/
namespace PrimeSelectionAudit
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

abbrev NameRelocations := Array (Name × Name)

def relocateName (names : NameRelocations) (n : Name) : Except String Name := do
  if let some (_, target) := names.find? (fun pair => pair.1 == n) then return target
  if (`Iut).isPrefixOf n then throw s!"Unmapped project constant: {n}"
  return n

partial def decodeExpr (names : NameRelocations) (j : Json) : Except String Expr := do
  let recur := decodeExpr names
  match ← stringField j "kind" with
  | "bvar" => return .bvar (← (← field j "index").getNat?)
  | "sort" => return .sort (← decodeLevel (← field j "level"))
  | "const" =>
    let name ← relocateName names (← decodeName (← field j "name"))
    let levels ← (← arrayField j "levels").mapM decodeLevel
    return .const name levels.toList
  | "app" =>
    let fn ← recur (← field j "fn")
    let arg ← recur (← field j "arg")
    return .app fn arg
  | "lam" =>
    let name ← decodeName (← field j "name")
    let type ← recur (← field j "type")
    let body ← recur (← field j "body")
    let binder ← decodeBinder (← stringField j "binder")
    return .lam name type body binder
  | "forall" =>
    let name ← decodeName (← field j "name")
    let type ← recur (← field j "type")
    let body ← recur (← field j "body")
    let binder ← decodeBinder (← stringField j "binder")
    return .forallE name type body binder
  | "let" =>
    let name ← decodeName (← field j "name")
    let type ← recur (← field j "type")
    let value ← recur (← field j "value")
    let body ← recur (← field j "body")
    let nondependent ← (← field j "nondependent").getBool?
    return .letE name type value body nondependent
  | "nat" => return .lit (.natVal (← (← field j "value").getNat?))
  | "string" => return .lit (.strVal (← stringField j "value"))
  | "proj" =>
    let name ← relocateName names (← decodeName (← field j "name"))
    let index ← (← field j "index").getNat?
    let body ← recur (← field j "body")
    return .proj name index body
  | k => throw s!"Unknown Expr kind: {k}"

end PrimeSelectionAudit


/-! This template is concatenated with the codec into each independent leaf.
    It deliberately does not import any Solution module. -/
namespace PrimeSelectionAudit
open Lean Elab Term Meta

def checked {α : Type} (x : Except String α) : MetaM α :=
  match x with
  | .ok a => pure a
  | .error e => throwError "{e}"

def readJson (path : String) : MetaM Json := do
  checked (Json.parse (← IO.FS.readFile path))

def moduleOf (env : Environment) (name : Name) : Option Name := do
  let index ← env.getModuleIdxFor? name
  env.header.moduleNames[index.toNat]?

def standardAxioms : Array Name := #[`propext, `Classical.choice, `Quot.sound]

def ensureStandard (label : String) (axs : Array Name) (allowSorry := false) : MetaM Unit := do
  for ax in axs do
    unless standardAxioms.contains ax || (allowSorry && ax == `sorryAx) do
      throwError "Unexpected axiom in {label}: {ax}"

def expressionAxioms (e : Expr) : MetaM (Array Name) := do
  let mut result : Array Name := #[]
  for name in e.getUsedConstants do
    for ax in ← collectAxioms name do
      unless result.contains ax do result := result.push ax
  return result.qsort Name.lt

def telescopeJson (type : Expr) : MetaM Json :=
  forallTelescope type fun xs result => do
    let binders ← xs.mapM fun x => do
      let decl ← x.fvarId!.getDecl
      return Json.mkObj [("name", toJson decl.userName.toString),
        ("binderInfo", toJson (reprStr decl.binderInfo)),
        ("type", toJson (← ppExpr decl.type).pretty)]
    return Json.mkObj [("binders", Json.arr binders), ("result", toJson (← ppExpr result).pretty)]

partial def binderShape : Expr → Array String
  | .forallE _ _ body info => #[reprStr info] ++ binderShape body
  | .mdata _ e => binderShape e
  | _ => #[]

-- Kernel conversion ignores BinderInfo. Compare the full binder inventory too,
-- including binders inside the result proposition and implicit argument types.
partial def binderInventory : Expr → Array String
  | .forallE _ t body info => #["forall:" ++ reprStr info] ++ binderInventory t ++ binderInventory body
  | .lam _ t body info => #["lambda:" ++ reprStr info] ++ binderInventory t ++ binderInventory body
  | .app f a => binderInventory f ++ binderInventory a
  | .letE _ t value body _ => binderInventory t ++ binderInventory value ++ binderInventory body
  | .mdata _ e => binderInventory e
  | .proj _ _ e => binderInventory e
  | _ => #[]

def canonicalLevels (count : Nat) : List Name :=
  (List.range count).map fun i => Name.num (Name.str .anonymous "_primeSelectionAuditUniverse") i

def alphaType (ci : ConstantInfo) (canonical : List Name) : MetaM Expr := do
  unless ci.levelParams.length == canonical.length do
    throwError "Universe parameter count differs: {ci.name}"
  return ci.type.instantiateLevelParams ci.levelParams (canonical.map Level.param)

def requireClosed (label : String) (e : Expr) : MetaM Unit := do
  if e.hasMVar || e.hasFVar || e.hasLooseBVars then
    throwError "Open expression in {label}"

def kernelEq (label : String) (a b : Expr) : MetaM Unit := do
  requireClosed label a
  requireClosed label b
  -- Kernel conversion assumes well-typed expressions. Recheck the relocated
  -- old-version expression against the actual target environment first.
  for e in #[a, b] do
    match Kernel.check (← getEnv) {} e with
    | .ok (.sort _) => pure ()
    | .ok _ => throwError "Expected a type in {label}"
    | .error ex => throwKernelException ex
  match Kernel.isDefEq (← getEnv) {} a b with
  | .ok true => pure ()
  | .ok false => throwError "Kernel type comparison failed: {label}"
  | .error e => throwKernelException e

def namesFromJson (j : Json) : MetaM (List Name) := do
  return (← checked ((← checked j.getArr?).mapM decodeName)).toList

def addRelocation (map : NameRelocations) (original wrapped : Name) : MetaM NameRelocations := do
  if let some (_, prior) := map.find? (fun pair => pair.1 == original) then
    unless prior == wrapped do throwError "Conflicting relocation for {original}"
    return map
  return map.push (original, wrapped)

def relocationMap (j : Json) : MetaM NameRelocations := do
  let mut result := #[]
  for entry in ← checked (arrayField j "sourceSymbolMap") do
    result ← addRelocation result
      (← checked (stringField entry "original")).toName
      (← checked (stringField entry "expectedWrapped")).toName
  -- The 14 project symbols omit generated structure projections. Their exact
  -- names are separately recorded in the original compiler query's node facts.
  for node in ← checked (arrayField j "nodes") do
    for entry in ← checked (arrayField node "typeProjectConstantRelocations") do
      result ← addRelocation result
        (← checked (stringField entry "original")).toName
        (← checked (stringField entry "expectedWrapped")).toName
  for (original, wrapped) in result do
    unless (← getEnv).contains wrapped do
      -- Inline helpers are intentionally absent from some independent leaves.
      if (← checked (arrayField j "nodes")).any (fun node =>
          (stringField node "wrappedTheoremName").toOption == some wrapped.toString) then
        pure ()
      else if original == `Iut.ChebyshevBound || original == `Iut.LocalHeightData ||
          original == `Iut.thetaSet || original == `Iut.LocalHeightData.height then
        throwError "Required relocated definition is absent: {wrapped}"
  return result

def auditDefinitions : MetaM Json := do
  let env ← getEnv
  let defsModule := `Definitions.Def_AbcAdaptation_Reference_Iut_Implication_PrimeSelection
  let declarations := env.constants.fold (fun names name _ =>
    if moduleOf env name == some defsModule then names.push name else names
    ) #[]
  unless declarations.size > 0 do throwError "Definitions module contains no audited declarations"
  let mut reports := #[]
  for name in declarations.qsort Name.lt do
    let ci ← getConstInfo name
    if let .axiomInfo _ := ci then throwError "Definitions declares an axiom: {name}"
    let allAxioms ← collectAxioms name
    let typeAxioms ← expressionAxioms ci.type
    let value? := ci.value? (allowOpaque := true)
    let valueAxioms ← match value? with
      | some value => expressionAxioms value
      | none => pure #[]
    ensureStandard s!"Definitions {name}" allAxioms
    ensureStandard s!"Definitions type {name}" typeAxioms
    ensureStandard s!"Definitions value {name}" valueAxioms
    reports := reports.push (Json.mkObj [
      ("name", toJson name.toString), ("kind", toJson (match ci with
        | .ctorInfo _ => "constructor" | .inductInfo _ => "inductive"
        | .recInfo _ => "recursor" | .defnInfo _ => "definition"
        | .thmInfo _ => "theorem" | .opaqueInfo _ => "opaque" | _ => "other")),
      ("levelParams", toJson (ci.levelParams.map Name.toString)),
      ("type", toJson (← ppExpr ci.type).pretty),
      ("telescope", ← telescopeJson ci.type),
      ("typeAxioms", toJson (typeAxioms.map Name.toString)),
      ("hasValue", toJson value?.isSome),
      ("valueAxioms", toJson (valueAxioms.map Name.toString)),
      ("closureAxioms", toJson (allAxioms.map Name.toString)),
      ("hasSorryAx", toJson (allAxioms.contains `sorryAx))])
  let mut structures := #[]
  for name in #[`AbcAdaptation.Reference.Iut.ChebyshevBound,
      `AbcAdaptation.Reference.Iut.LocalHeightData] do
    let some info := getStructureInfo? env name | throwError "Missing structure: {name}"
    let ci ← getConstInfo name
    let .inductInfo inductiveInfo := ci | throwError "Expected inductive structure: {name}"
    for ctor in inductiveInfo.ctors do
      unless declarations.contains ctor do throwError "Unaudited constructor: {ctor}"
    for projection in info.fieldInfo do
      unless declarations.contains projection.projFn do
        throwError "Unaudited projection: {projection.projFn}"
    structures := structures.push (Json.mkObj [
      ("name", toJson name.toString), ("fieldsInConstructorOrder", toJson (info.fieldNames.map Name.toString)),
      ("constructors", toJson (inductiveInfo.ctors.map Name.toString)),
      ("projections", toJson (info.fieldInfo.map fun p => p.projFn.toString))])
  return Json.mkObj [("module", toJson defsModule.toString),
    ("declarations", Json.arr reports), ("structures", Json.arr structures),
    ("allTypeValueClosuresUseOnlyStandardAxioms", toJson true)]

def audit (original wrapped : Name) (allowOpenDependencies : Bool) : TermElabM Unit := do
  unless Lean.versionString == "4.33.1" do
    throwError "Expected platform compiler 4.33.1; got {Lean.versionString}"
  let originalRoot := (← IO.getEnv "PRIME_SELECTION_ORIGINAL_FACTS_DIR").getD
    "/home/admin-wsl/Coq/abc/prove2me_workspace/.local/adaptation/reference-extraction-20261115/prime-selection-source-facts"
  let mapPath := (← IO.getEnv "PRIME_SELECTION_NAME_MAP").getD
    "/tmp/p2m-prime-selection-mechanical-adapter-20261115/generated/original-wrapped-type-name-map.json"
  let exprPath := (← IO.getEnv "PRIME_SELECTION_ORIGINAL_EXPR_FILE").getD
    "/tmp/p2m-prime-selection-type-audit-20261115/original-exprs.json"
  let outputRoot := (← IO.getEnv "PRIME_SELECTION_AUDIT_OUTPUT_DIR").getD
    "/tmp/p2m-prime-selection-type-audit-20261115/results"
  let originalFact ← readJson (originalRoot ++ "/" ++ original.toString.replace "." "-" ++ ".json")
  unless (← checked (stringField originalFact "compilerVersion")) == "4.35.0-rc3" do
    throwError "Wrong compiler in original fact"
  unless (← checked (stringField originalFact "name")) == original.toString do
    throwError "Original fact name differs"
  let sourceExprFile ← readJson exprPath
  unless (← checked (stringField sourceExprFile "schema")) == "prime-selection-original-expr-v1" do
    throwError "Wrong original Expr schema"
  unless (← checked (stringField sourceExprFile "compilerVersion")) == "4.35.0-rc3" do
    throwError "Wrong compiler in original Expr file"
  let records ← checked (arrayField sourceExprFile "records")
  let matchingRecords := records.filter fun row => (stringField row "name").toOption == some original.toString
  unless matchingRecords.size == 1 do throwError "Expected one original Expr record: {original}"
  let record := matchingRecords[0]!
  unless (← checked (decodeName (← checked (field record "nameExpr")))) == original do
    throwError "Original Expr's structural declaration name differs"
  let sourceParams ← namesFromJson (← checked (field record "levelParams"))
  let oldParams ← checked (arrayField originalFact "levelParams")
  unless oldParams == sourceParams.toArray.map (fun n => Json.str n.toString) do
    throwError "Original Expr and previous compiler query disagree on universe parameter order"
  let relocations ← relocationMap (← readJson mapPath)
  let sourceType ← checked (decodeExpr relocations (← checked (field record "elaboratedExpr")))
  let target ← getConstInfo wrapped
  let solution ← getConstInfo `solution
  let canonical := canonicalLevels sourceParams.length
  let sourceType := sourceType.instantiateLevelParams sourceParams (canonical.map Level.param)
  let targetType ← alphaType target canonical
  let solutionType ← alphaType solution canonical
  unless binderShape sourceType == binderShape targetType &&
      binderShape targetType == binderShape solutionType do
    throwError "Top-level binder information differs"
  unless binderInventory sourceType == binderInventory targetType &&
      binderInventory targetType == binderInventory solutionType do
    throwError "Binder information inside the full type expression differs"
  let previousBinders ← checked (arrayField (← checked (field originalFact "elaboratedTelescope")) "binders")
  let previousShape ← previousBinders.mapM fun b => checked (stringField b "binderInfo")
  unless previousShape == binderShape sourceType do
    throwError "Previous compiler query and serialized Expr disagree on binder information"
  unless ← Meta.isDefEq targetType solutionType do throwError "Meta target/solution type comparison failed"
  kernelEq "target versus solution after universe alpha-renaming" targetType solutionType
  kernelEq "actual original compiler Expr relocated versus wrapped target" sourceType targetType
  let solutionValue ← match solution.value? (allowOpaque := true) with
    | some value => pure value
    | none => throwError "solution has no proof value"
  unless !(solutionValue.getUsedConstants.contains `sorryAx) do
    throwError "solution body directly contains sorryAx"
  let axs ← collectAxioms `solution
  ensureStandard "solution" axs allowOpenDependencies
  let expectedOpen := #[`AbcAdaptation.Reference.Iut.ChebyshevBound.exists_prime_notMem,
    `AbcAdaptation.Reference.Iut.sum_log_primeFactors_le]
  let directProject := solutionValue.getUsedConstants.filter fun n =>
    (`AbcAdaptation.Reference.Iut).isPrefixOf n
  -- Check *all* constants used by the proof, including Mathlib/private helpers;
  -- a namespace filter alone could miss an unrelated path to sorryAx.
  for name in solutionValue.getUsedConstants do
    if (← collectAxioms name).contains `sorryAx then
      unless allowOpenDependencies && expectedOpen.contains name do
        throwError "Unexpected direct dependency carrying sorryAx: {name}"
  let mut dependencies := #[]
  for name in directProject do
    let dependencyAxioms ← collectAxioms name
    if dependencyAxioms.contains `sorryAx then
      unless allowOpenDependencies && expectedOpen.contains name do
        throwError "Unexpected project dependency with sorryAx: {name}"
    dependencies := dependencies.push (Json.mkObj [("name", toJson name.toString),
      ("axioms", toJson (dependencyAxioms.map Name.toString)),
      ("isExpectedOpenStub", toJson (expectedOpen.contains name))])
  if allowOpenDependencies then
    -- Main must actually consume both stubs, and each must explain sorryAx.
    for name in expectedOpen do
      unless directProject.contains name do throwError "Main solution does not consume expected stub: {name}"
      unless (← collectAxioms name).contains `sorryAx do
        throwError "Expected imported open stub does not carry sorryAx: {name}"
  let definitions ← auditDefinitions
  let result := Json.mkObj [
    ("schema", toJson "prime-selection-kernel-type-audit-v1"),
    ("compilerVersion", toJson Lean.versionString),
    ("originalName", toJson original.toString), ("wrappedName", toJson wrapped.toString),
    ("originalExprInput", toJson exprPath), ("originalFactInput", toJson originalRoot),
    ("relocationMapInput", toJson mapPath),
    ("levelParamAlphaRenaming", Json.mkObj [
      ("originalKernelOrder", toJson (sourceParams.map Name.toString)),
      ("wrappedKernelOrder", toJson (target.levelParams.map Name.toString)),
      ("solutionKernelOrder", toJson (solution.levelParams.map Name.toString)),
      ("canonicalOrder", toJson (canonical.map Name.toString))]),
    ("metaTargetSolutionTypeEqual", toJson true),
    ("kernelTargetSolutionTypeEqual", toJson true),
    ("kernelOriginalExprRelocatedTypeEqual", toJson true),
    ("originalExprMetadataErased", toJson true),
    ("topLevelBinderInfoEqual", toJson true),
    ("allExpressionBinderInfoEqual", toJson true),
    ("wrappedType", toJson (← ppExpr target.type).pretty),
    ("solutionType", toJson (← ppExpr solution.type).pretty),
    ("wrappedTelescope", ← telescopeJson target.type),
    ("solutionTelescope", ← telescopeJson solution.type),
    ("solutionAxioms", toJson (axs.map Name.toString)),
    ("solutionBodyDirectSorryAx", toJson false),
    ("solutionHasTransitiveSorryAx", toJson (axs.contains `sorryAx)),
    ("permitsOnlyListedImportedOpenStubs", toJson allowOpenDependencies),
    ("directProjectDependencies", Json.arr dependencies),
    ("definitions", definitions)]
  IO.FS.createDirAll outputRoot
  let output := outputRoot ++ "/" ++ original.toString.replace "." "-" ++ ".json"
  IO.FS.writeFile output (result.pretty ++ "\n")
  logInfo s!"Kernel type/axiom audit written: {output}"

syntax (name := auditPrimeSelection) "audit_prime_selection " ident " => " ident " open_dependencies " ident : command

@[command_elab auditPrimeSelection] def elabAudit : Command.CommandElab := fun stx => do
  let allowOpen := stx[5].getId == `true
  unless stx[5].getId == `true || stx[5].getId == `false do
    throwError "open_dependencies must be true or false"
  Command.liftTermElabM (audit stx[1].getId stx[3].getId allowOpen)

end PrimeSelectionAudit


audit_prime_selection Iut.ChebyshevBound.exists_prime_notMem => AbcAdaptation.Reference.Iut.ChebyshevBound.exists_prime_notMem open_dependencies false

#print axioms solution
#print axioms AbcAdaptation.Reference.Iut.ChebyshevBound
#print axioms AbcAdaptation.Reference.Iut.thetaSet
#print axioms AbcAdaptation.Reference.Iut.LocalHeightData
#print axioms AbcAdaptation.Reference.Iut.LocalHeightData.height
