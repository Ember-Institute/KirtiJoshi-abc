import Lean
import Definitions.Def_AbcAdaptation_Reference_TateCurvesTheta_TateCurve_Discriminant

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

namespace TateAnalyticSupplementReview
open Lean Elab Term Meta FoundationAudit

def relocateName (n : Name) : Except String Name := do
  if Name.isPrefixOf `TateCurvesTheta n then
    return n.replacePrefix `TateCurvesTheta `AbcAdaptation.Reference.TateCurvesTheta
  if #[`Iut, `Genl, `AbcAdaptation, `_private].any (·.isPrefixOf n) then
    throw s!"Unmapped project constant {n}"
  return n

-- Decode the source Expr while preserving its binders and universe arguments.
-- Mathlib names retain their source spellings for target-kernel conversion.
partial def relocateExpr (j : Json) : Except String Expr := do
  let recur := relocateExpr
  let relocate := relocateName
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

def sourceRoots : Array (Name × Name) := #[
  (`TateCurvesTheta.TateParameter.summable_a₆Coeff_qFactor, `TateCurvesTheta.TateCurve.A6Series),
  (`TateCurvesTheta.TateParameter.tateCurve_a₁, `TateCurvesTheta.TateCurve.Weierstrass),
  (`TateCurvesTheta.TateParameter.tateCurve_a₂, `TateCurvesTheta.TateCurve.Weierstrass),
  (`TateCurvesTheta.TateParameter.tateCurve_a₃, `TateCurvesTheta.TateCurve.Weierstrass),
  (`TateCurvesTheta.TateParameter.tateCurve_a₄, `TateCurvesTheta.TateCurve.Weierstrass),
  (`TateCurvesTheta.TateParameter.tateCurve_a₆, `TateCurvesTheta.TateCurve.Weierstrass)]

def targetOwners : Array Name := #[
  `Definitions.Def_AbcAdaptation_Reference_TateCurvesTheta_TateCurve_A6Series,
  `Definitions.Def_AbcAdaptation_Reference_TateCurvesTheta_TateCurve_Discriminant,
  `Definitions.Def_AbcAdaptation_Reference_TateCurvesTheta_TateCurve_Discriminant,
  `Definitions.Def_AbcAdaptation_Reference_TateCurvesTheta_TateCurve_Discriminant,
  `Definitions.Def_AbcAdaptation_Reference_TateCurvesTheta_TateCurve_Discriminant,
  `Definitions.Def_AbcAdaptation_Reference_TateCurvesTheta_TateCurve_Discriminant]

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

def compare (cache : AxiomCache) (row : Json) (sourceName sourceOwner targetOwner : Name) :
    MetaM Json := do
  let decodedName ← checked (decodeName (← checked (field row "nameExpr")))
  let decodedOwner ← checked (decodeName (← checked (field row "ownerNameExpr")))
  unless decodedName == sourceName && decodedOwner == sourceOwner do
    throwError "Unexpected source export record for {sourceName} in {sourceOwner}"
  unless (← checked (stringField row "record")) == "fullActualFact" &&
      (← checked (stringField row "kind")) == "theorem" &&
      (← checked (row.getObjValAs? Bool "isProposition")) &&
      (← checked (row.getObjValAs? Bool "kernelValueTypeMatchesActualTYPE")) &&
      !(← checked (row.getObjValAs? Bool "hasSorryAx")) do
    throwError "Incomplete source theorem evidence for {sourceName}"
  let axs ← sourceAxioms row "axioms"
  let taxs ← sourceAxioms row "typeAxioms"
  let vaxs ← sourceAxioms row "valueAxioms"
  let env ← getEnv
  let targetName ← checked (relocateName sourceName)
  let ci ← getConstInfo targetName
  unless moduleOf env targetName == some targetOwner && kind ci == "theorem" do
    throwError "Unexpected native theorem owner for {targetName}, expected {targetOwner}"
  let some targetValue := ci.value? (allowOpaque := true) | throwError "No native proof for {targetName}"
  let sourceUniverses ← namesFromJson (← checked (field row "levelParams"))
  unless sourceUniverses == ci.levelParams do
    throwError "Named universe parameter order differs for {targetName}"
  let st ← checked (relocateExpr (← checked (field row "actualTypeExpr")))
  let sv ← checked (relocateExpr (← checked (field row "actualValueExpr")))
  let svt ← checked (relocateExpr (← checked (field row "kernelInferredValueTypeExpr")))
  let tt := ci.type
  unless binderPlacement st == binderPlacement tt do
    throwError "Binder placement differs for {targetName}"
  kernelEq s!"full theorem type {targetName}" st tt
  kernelEq s!"recorded mapped source proof type {targetName}" svt st
  kernelEq s!"actual mapped source proof type {targetName}" (← kernelCheck targetName.toString sv) tt
  kernelEq s!"actual native proof type {targetName}" (← kernelCheck targetName.toString targetValue) tt
  kernelEq s!"complete proof expressions {targetName}" sv targetValue
  let targetAxioms ← cachedAxioms cache targetName
  let mappedTypeAxioms ← expressionAxioms cache st
  let mappedProofAxioms ← expressionAxioms cache sv
  let targetTypeAxioms ← expressionAxioms cache tt
  let targetProofAxioms ← expressionAxioms cache targetValue
  for auditedAxioms in #[targetAxioms, mappedTypeAxioms, mappedProofAxioms,
      targetTypeAxioms, targetProofAxioms] do
    ensureStandard targetName.toString auditedAxioms
  let mappedType ← checked (encodeExpr st)
  let mappedProof ← checked (encodeExpr sv)
  let actualType ← checked (encodeExpr tt)
  let actualProof ← checked (encodeExpr targetValue)
  return Json.mkObj [
    ("source", toJson sourceName.toString), ("sourceOwner", toJson sourceOwner.toString),
    ("target", toJson targetName.toString), ("targetOwner", toJson targetOwner.toString),
    ("levelParams", toJson (ci.levelParams.map Name.toString)),
    ("typeBinderPlacement", toJson (binderPlacement tt)),
    ("mappedSourceProofBinderPlacement", toJson (binderPlacement sv)),
    ("targetProofBinderPlacement", toJson (binderPlacement targetValue)),
    ("mappedSourceTypeExpr", mappedType), ("targetTypeExpr", actualType),
    ("mappedSourceProofExpr", mappedProof), ("targetProofExpr", actualProof),
    ("mappedTypeSyntacticallyEqual", toJson (mappedType == actualType)),
    ("mappedProofSyntacticallyEqual", toJson (mappedProof == actualProof)),
    ("directTypeConstantDifferences", constantDifferences st tt),
    ("directProofConstantDifferences", constantDifferences sv targetValue),
    ("kernelTypeDefinitionalEquality", toJson true),
    ("kernelProofCheckedAtTargetType", toJson true),
    ("kernelProofDefinitionalEquality", toJson true),
    ("sourceAxioms", toJson axs), ("sourceTypeAxioms", toJson taxs), ("sourceProofAxioms", toJson vaxs),
    ("mappedSourceTypeAxioms", toJson (mappedTypeAxioms.map Name.toString)),
    ("mappedSourceProofAxioms", toJson (mappedProofAxioms.map Name.toString)),
    ("targetAxioms", toJson ((targetAxioms.qsort Name.lt).map Name.toString)),
    ("targetTypeAxioms", toJson (targetTypeAxioms.map Name.toString)),
    ("targetProofAxioms", toJson (targetProofAxioms.map Name.toString))]

run_meta do
  unless Lean.versionString == "4.33.1" do
    throwError "Expected Lean 4.33.1 for the native comparison"
  let sourceReport ← jsonFile (← absoluteEnv "B1_TATE_ANALYTIC_SUPPLEMENT_SOURCE")
  let output ← absoluteEnv "B1_TATE_ANALYTIC_SUPPLEMENT_COMPARISON"
  unless (← checked (stringField sourceReport "schema")) == "b1-tate-analytic-supplement-source/v1" &&
      (← checked (stringField sourceReport "compilerVersion")) == "4.35.0-rc3" do
    throwError "Unexpected source report schema or compiler"
  let rows ← checked (arrayField sourceReport "records")
  unless rows.size == sourceRoots.size && targetOwners.size == sourceRoots.size do
    throwError "Unexpected number of Tate analytic source or target records"
  let cache ← IO.mkRef ({} : Std.HashMap Name (Array Name))
  let mut reports := #[]
  for k in [:sourceRoots.size] do
    let (sourceName, sourceOwner) := sourceRoots[k]!
    reports := reports.push (← compare cache rows[k]! sourceName sourceOwner targetOwners[k]!)
  let report := Json.mkObj [
    ("schema", toJson "b1-tate-analytic-supplement-comparison/v1"),
    ("compilerVersion", toJson Lean.versionString),
    ("sourceCompilerVersion", toJson "4.35.0-rc3"),
    ("projectNamespaceMap", toJson "TateCurvesTheta → AbcAdaptation.Reference.TateCurvesTheta"),
    ("mathlibNameMap", toJson "identity"),
    ("knownInstanceRouteDifference", toJson
      "Source: Semifield.toCommSemiring then CommSemiring.toSemiring. Native: Semifield.toDivisionSemiring then DivisionSemiring.toSemiring."),
    ("records", Json.arr reports)]
  IO.FS.writeFile output (report.compress ++ "\n")
  logInfo m!"Kernel and standard-axiom review passed for {reports.size} Tate analytic theorems"

end TateAnalyticSupplementReview
