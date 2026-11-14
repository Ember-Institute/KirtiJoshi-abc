import Lean
import Theorems.Thm_AbcAdaptation_Reference_Iut_assembly
import Solutions.Sol_AbcAdaptation_Reference_Iut_assembly

set_option pp.fullNames true
set_option pp.funBinderTypes true
set_option pp.piBinderTypes true
set_option pp.universes true

namespace NumericTypeAudit
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

def requireStandardName (n : Name) : Except String Name := do
  if #[`Iut, `Genl, `AbcAdaptation, `Definitions, `Theorems, `Solutions].any (·.isPrefixOf n) then
    throw s!"Project constant in numeric type: {n}"
  return n

partial def decodeExpr (j : Json) : Except String Expr := do
  let recur := decodeExpr
  match ← stringField j "kind" with
  | "bvar" => return .bvar (← (← field j "index").getNat?)
  | "sort" => return .sort (← decodeLevel (← field j "level"))
  | "const" =>
    let name ← requireStandardName (← decodeName (← field j "name"))
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
    let name ← requireStandardName (← decodeName (← field j "name"))
    let index ← (← field j "index").getNat?
    let body ← recur (← field j "body")
    return .proj name index body
  | k => throw s!"Unknown Expr kind: {k}"

open Elab Term Meta

def checked {α : Type} (value : Except String α) : MetaM α :=
  match value with
  | .ok result => pure result
  | .error message => throwError "{message}"

def absoluteEnv (key : String) : MetaM String := do
  let some value ← IO.getEnv key | throwError "Missing environment variable: {key}"
  unless value.startsWith "/" do throwError "Expected an absolute path in {key}"
  return value

def moduleOf (env : Environment) (name : Name) : Option Name := do
  let index ← env.getModuleIdxFor? name
  env.header.moduleNames[index.toNat]?

def standardAxioms : Array Name := #[`propext, `Classical.choice, `Quot.sound]

def ensureStandard (label : String) (axioms : Array Name) : MetaM Unit := do
  for ax in axioms do
    unless standardAxioms.contains ax do throwError "Unexpected axiom in {label}: {ax}"

-- In particular, a standard namespace cannot hide a project-owned constant.
def standardModule (name : Name) : Bool :=
  #[`Init, `Lean, `Std, `Mathlib, `Batteries, `Aesop, `Qq,
    `Plausible, `ProofWidgets, `ImportGraph, `Cli].any (·.isPrefixOf name)

def requireStandardConstants (label : String) (type : Expr) : MetaM Unit := do
  let env ← getEnv
  for name in type.getUsedConstants do
    let _ ← checked (requireStandardName name)
    let some owner := moduleOf env name |
      throwError "Constant without imported standard owner in {label}: {name}"
    unless standardModule owner do
      throwError "Nonstandard constant owner in {label}: {name} from {owner}"

partial def binderInventory : Expr → Array String
  | .forallE _ type body info => #["forall:" ++ reprStr info] ++ binderInventory type ++ binderInventory body
  | .lam _ type body info => #["lambda:" ++ reprStr info] ++ binderInventory type ++ binderInventory body
  | .app fn arg => binderInventory fn ++ binderInventory arg
  | .letE _ type value body _ => binderInventory type ++ binderInventory value ++ binderInventory body
  | .mdata _ expr => binderInventory expr
  | .proj _ _ expr => binderInventory expr
  | _ => #[]

def canonicalLevels (count : Nat) : List Name :=
  (List.range count).map fun i => Name.num (Name.str .anonymous "_numericAuditUniverse") i

def alphaType (ci : ConstantInfo) (canonical : List Name) : MetaM Expr := do
  unless ci.levelParams.length == canonical.length do
    throwError "Universe parameter count differs: {ci.name}"
  return ci.type.instantiateLevelParams ci.levelParams (canonical.map Level.param)

def requireClosed (label : String) (expr : Expr) : MetaM Unit := do
  if expr.hasMVar || expr.hasFVar || expr.hasLooseBVars then
    throwError "Open expression in {label}"

def kernelEq (label : String) (left right : Expr) : MetaM Unit := do
  for expr in #[left, right] do
    requireClosed label expr
    match Kernel.check (← getEnv) {} expr with
    | .ok (.sort _) => pure ()
    | .ok _ => throwError "Expected a type in {label}"
    | .error ex => throwKernelException ex
  match Kernel.isDefEq (← getEnv) {} left right with
  | .ok true => pure ()
  | .ok false => throwError "Kernel type comparison failed: {label}"
  | .error ex => throwKernelException ex

def signatureJson (type : Expr) (realCount : Nat) : MetaM Json :=
  forallTelescope type fun xs result => do
    unless xs.size == realCount + 17 do throwError "Numeric binder count differs"
    let mut rows := #[]
    for index in [:xs.size] do
      let decl ← xs[index]!.fvarId!.getDecl
      if index < realCount then
        unless decl.binderInfo == .implicit do throwError "Expected implicit real parameter {index}"
        unless ← Meta.isDefEq decl.type (mkConst `Real) do
          throwError "Expected Real parameter {index}"
      else
        unless decl.binderInfo == .default do throwError "Expected explicit premise {index}"
        unless ← isProp decl.type do throwError "Expected proposition premise {index}"
      rows := rows.push (Json.mkObj [("name", toJson decl.userName.toString),
        ("binderInfo", toJson (reprStr decl.binderInfo)),
        ("type", toJson (← ppExpr decl.type).pretty)])
    unless ← isProp result do throwError "Expected a proposition result"
    return Json.mkObj [("binders", Json.arr rows), ("implicitRealCount", toJson realCount),
      ("explicitPropositionCount", toJson (17 : Nat)), ("result", toJson (← ppExpr result).pretty)]

def audit (original wrapped theoremModule solutionModule : Name) (realCount : Nat) : TermElabM Unit := do
  unless Lean.versionString == "4.33.1" do
    throwError "Expected platform compiler 4.33.1; got {Lean.versionString}"
  let exprPath ← absoluteEnv "NUMERIC_ORIGINAL_EXPR_FILE"
  let outputRoot ← absoluteEnv "NUMERIC_AUDIT_OUTPUT_DIR"
  let sourceFile ← checked (Json.parse (← IO.FS.readFile exprPath))
  unless (← checked (stringField sourceFile "schema")) == "numeric-source-original-expr-v1" do
    throwError "Wrong original Expr schema"
  unless (← checked (stringField sourceFile "compilerVersion")) == "4.35.0-rc3" do
    throwError "Wrong original compiler version"
  let records ← checked (arrayField sourceFile "records")
  unless records.size == 2 do throwError "Expected exactly two source records"
  for name in #["Iut.assembly", "Iut.c2_final"] do
    unless (records.filter fun row => (stringField row "name").toOption == some name).size == 1 do
      throwError "Original record missing or duplicated: {name}"
  let matching := records.filter fun row => (stringField row "name").toOption == some original.toString
  let record := matching[0]!
  unless (← checked (decodeName (← checked (field record "nameExpr")))) == original do
    throwError "Structural source declaration name differs"
  let sourceParams := (← checked ((← checked (arrayField record "levelParams")).mapM decodeName)).toList
  unless sourceParams.eraseDups == sourceParams do throwError "Duplicate source universe parameter"
  let originalType ← checked (decodeExpr (← checked (field record "elaboratedExpr")))
  requireClosed "original type" originalType
  requireStandardConstants "original type" originalType
  let originalAxioms ← checked (arrayField record "axioms")
  for ax in originalAxioms do
    unless (standardAxioms.map fun n => Json.str n.toString).contains ax do
      throwError "Unexpected original theorem axiom"
  let sourceModule ← checked (stringField record "module")
  let expectedSourceModule := if original == `Iut.assembly then
    "Iut.Implication.Theorem110" else "Iut.Implication.Corollary22"
  unless sourceModule == expectedSourceModule do throwError "Source module differs"
  let sourceSha ← checked (stringField record "sourceSha256")
  unless sourceSha.length == 64 do throwError "Missing source checksum"
  let env ← getEnv
  -- Only the two own artifacts may add project imports. There is no Definitions bundle.
  for imported in env.header.moduleNames do
    if #[`Iut, `Genl, `AbcAdaptation, `Definitions, `Theorems, `Solutions].any (·.isPrefixOf imported) then
      unless imported == theoremModule || imported == solutionModule do
        throwError "Forbidden project import: {imported}"
  let target ← getConstInfo wrapped
  let solution ← getConstInfo `solution
  unless moduleOf env wrapped == some theoremModule && moduleOf env `solution == some solutionModule do
    throwError "Target or solution was loaded from the wrong independent artifact"
  let canonical := canonicalLevels sourceParams.length
  let sourceType := originalType.instantiateLevelParams sourceParams (canonical.map Level.param)
  let targetType ← alphaType target canonical
  let solutionType ← alphaType solution canonical
  for type in #[targetType, solutionType] do requireStandardConstants "platform type" type
  unless binderInventory sourceType == binderInventory targetType &&
      binderInventory targetType == binderInventory solutionType do
    throwError "Full expression BinderInfo inventory differs"
  let sourceSignature ← signatureJson sourceType realCount
  let targetSignature ← signatureJson targetType realCount
  let solutionSignature ← signatureJson solutionType realCount
  unless ← Meta.isDefEq targetType solutionType do throwError "Meta target/solution type comparison failed"
  kernelEq "target versus solution" targetType solutionType
  kernelEq "original versus target" sourceType targetType
  kernelEq "original versus solution" sourceType solutionType
  -- Target may contain sorry: inspect its TYPE only. Proof auditing concerns solution.
  let some proof := solution.value? (allowOpaque := true) | throwError "solution has no proof value"
  requireClosed "solution proof" proof
  if proof.getUsedConstants.contains `sorryAx then throwError "Direct sorryAx in solution"
  let axioms ← collectAxioms `solution
  ensureStandard "solution transitive closure" axioms
  let mut dependencies := #[]
  for name in proof.getUsedConstants do
    let _ ← checked (requireStandardName name)
    let some owner := moduleOf env name | throwError "Proof dependency has no imported owner: {name}"
    unless standardModule owner || owner == solutionModule do
      throwError "Nonstandard proof dependency: {name} from {owner}"
    let dependencyAxioms ← collectAxioms name
    ensureStandard s!"direct dependency {name}" dependencyAxioms
    dependencies := dependencies.push (Json.mkObj [("name", toJson name.toString),
      ("axioms", toJson (dependencyAxioms.map Name.toString))])
  let result := Json.mkObj [
    ("schema", toJson "numeric-kernel-type-axiom-audit-v1"),
    ("compilerVersion", toJson Lean.versionString),
    ("originalCompilerVersion", toJson "4.35.0-rc3"),
    ("originalName", toJson original.toString), ("wrappedName", toJson wrapped.toString),
    ("originalExprInput", toJson exprPath), ("originalCompilerRecord", record),
    ("sourceModule", toJson sourceModule), ("sourceSha256", toJson sourceSha),
    ("theoremModule", toJson theoremModule.toString), ("solutionModule", toJson solutionModule.toString),
    ("universeAlphaRenaming", Json.mkObj [
      ("originalKernelOrder", toJson (sourceParams.map Name.toString)),
      ("wrappedKernelOrder", toJson (target.levelParams.map Name.toString)),
      ("solutionKernelOrder", toJson (solution.levelParams.map Name.toString)),
      ("canonicalOrder", toJson (canonical.map Name.toString))]),
    ("originalExprMetadataErased", toJson true), ("projectConstantRelocations", Json.arr #[]),
    ("originalTypeStandardConstantsOnly", toJson true),
    ("allExpressionBinderInfoEqual", toJson true),
    ("metaTargetSolutionTypeEqual", toJson true), ("kernelTargetSolutionTypeEqual", toJson true),
    ("kernelOriginalTargetTypeEqual", toJson true), ("kernelOriginalSolutionTypeEqual", toJson true),
    ("originalSignature", sourceSignature), ("wrappedSignature", targetSignature),
    ("solutionSignature", solutionSignature), ("originalType", ← checked (encodeExpr originalType)),
    ("wrappedType", ← checked (encodeExpr target.type)), ("solutionType", ← checked (encodeExpr solution.type)),
    ("solutionAxioms", toJson (axioms.map Name.toString)),
    ("solutionBodyDirectSorryAx", toJson false), ("solutionHasTransitiveSorryAx", toJson false),
    ("solutionClosureStandardAxiomsOnly", toJson true), ("permitsOpenChildren", toJson false),
    ("directProofDependencies", Json.arr dependencies), ("definitionsBundleCount", toJson (0 : Nat))]
  IO.FS.createDirAll outputRoot
  let output := outputRoot ++ "/" ++ original.toString.replace "." "-" ++ ".json"
  IO.FS.writeFile output (result.pretty ++ "\n")
  logInfo s!"Numeric kernel type/axiom audit written: {output}"

end NumericTypeAudit

syntax (name := auditNumeric) "audit_numeric" : command

@[command_elab auditNumeric] def elabAuditNumeric : Lean.Elab.Command.CommandElab := fun _ => do
  Lean.Elab.Command.liftTermElabM (NumericTypeAudit.audit `Iut.assembly `AbcAdaptation.Reference.Iut.assembly `Theorems.Thm_AbcAdaptation_Reference_Iut_assembly `Solutions.Sol_AbcAdaptation_Reference_Iut_assembly 11)

audit_numeric

#print axioms solution
