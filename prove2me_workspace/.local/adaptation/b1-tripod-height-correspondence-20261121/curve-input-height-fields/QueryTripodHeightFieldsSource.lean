import Lean
import B1SourceReplay

/-!
The constructor assignments are from Iut/Tripod/CurveFacts.lean (Apache-2.0),
revision 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8, lines 503, 508 and 509.
The statements below specialize the record fields to `h := P.h` and the
same `P.curve`, `P.arith` and `P.tate` as the constructor.
-/
namespace Iut.Tripod

-- CurveFacts.lean:403, which B1SourceReplay does not include.
def LegendreHeightHyp (P : CurveProviders) (K : CompactlyBounded) : Prop :=
  ((1 / 6 : ℝ) • P.h) ≈[K.set] htCan

/-- The assignment at line 503. -/
theorem curveInputsHeightEqReplay (P : CurveProviders) (K : CompactlyBounded) (d : ℕ) :
    ∀ (x : tripodTheory.Pt tripodTheory.tripod)
      (_hx : x ∈ tripodTheory.cbsSet K ∩ tripodTheory.ptLE tripodTheory.tripod d),
      ((P.curve x).localHeightData (P.arith x) (P.tate x)).height = P.h x :=
  fun _ _ => rfl

/-- The assignment at line 508. -/
theorem curveInputsHtCanEquivReplay (P : CurveProviders) (K : CompactlyBounded)
    (hh : LegendreHeightHyp P K) :
    ((1 / 6 : ℝ) • P.h) ≈[tripodTheory.cbsSet K] tripodTheory.htCan tripodTheory.tripod :=
  hh

/-- The assignment at line 509. -/
theorem curveInputsNorthcottReplay (P : CurveProviders) (K : CompactlyBounded) (d : ℕ)
    (hN : NorthcottHyp) (hh : LegendreHeightHyp P K) :
    ∀ H : ℝ, {x : tripodTheory.Pt tripodTheory.tripod |
      x ∈ tripodTheory.cbsSet K ∩ tripodTheory.ptLE tripodTheory.tripod d ∧ P.h x ≤ H}.Finite :=
  northcott_of_equiv hN K d hh

end Iut.Tripod

namespace TripodHeightFieldSourceExpressions

open Lean Elab Term Meta

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

def checked {α : Type} (x : Except String α) : MetaM α :=
  match x with
  | .ok a => pure a
  | .error e => throwError "{e}"

def jsonFile (p : String) : MetaM Json := do
  checked (Json.parse (← IO.FS.readFile p))

def absoluteEnv (key : String) : MetaM String := do
  let some p ← IO.getEnv key | throwError "Missing environment variable {key}"
  unless p.startsWith "/" do throwError "Expected absolute path: {key}"
  return p

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

def telescopeJson (type : Expr) : MetaM Json :=
  forallTelescope type fun xs result => do
    let binders ← xs.mapM fun x => do
      let d ← x.fvarId!.getDecl
      return Json.mkObj [("name", toJson d.userName.toString),
        ("binderInfo", toJson (encodeBinder d.binderInfo)),
        ("typeDisplay", toJson (← ppExpr d.type).pretty)]
    return Json.mkObj [("binders", Json.arr binders),
      ("resultDisplay", toJson (← ppExpr result).pretty)]

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

def fact (cache : AxiomCache) (name : Name) (line : Nat) (provenance : String) :
    MetaM Json := do
  let env ← getEnv
  let ci ← getConstInfo name
  let .thmInfo thm := ci | throwError "Expected a theorem: {name}"
  unless ci.levelParams.isEmpty do throwError "Unexpected universe parameter: {name}"
  if (env.getModuleIdxFor? name).isSome then throwError "Expected a theorem in the replay file: {name}"
  let type ← checkedValueType name.toString thm.value ci.type
  let axs ← cachedAxioms cache name
  let typeAxs ← expressionAxioms cache ci.type
  let valueAxs ← expressionAxioms cache thm.value
  for xs in #[axs, typeAxs, valueAxs] do ensureStandard name.toString xs
  let names := fun ns : Array Name => Json.arr (ns.qsort Name.lt |>.map encodeName)
  let axiomStrings := fun ns : Array Name => toJson (ns.qsort Name.lt |>.map Name.toString)
  return Json.mkObj [
    ("record", toJson "fullActualFact"),
    ("name", toJson name.toString), ("nameExpr", encodeName name),
    ("owner", toJson env.mainModule.toString), ("ownerNameExpr", encodeName env.mainModule),
    ("kind", toJson (kind ci)), ("levelParams", names ci.levelParams.toArray),
    ("actualTypeExpr", ← checked (encodeExpr ci.type)),
    ("actualValueExpr", ← checked (encodeExpr thm.value)),
    ("valueRead", toJson true), ("isProposition", toJson (← isProp ci.type)),
    ("binderInventory", toJson (binderInventory ci.type)), ("telescope", ← telescopeJson ci.type),
    ("directTypeConstants", names ci.type.getUsedConstants),
    ("directValueConstants", names thm.value.getUsedConstants),
    ("kernelInferredValueTypeExpr", ← checked (encodeExpr type)),
    ("kernelValueTypeMatchesActualTYPE", toJson true),
    ("axioms", axiomStrings axs), ("typeAxioms", axiomStrings typeAxs),
    ("valueAxioms", axiomStrings valueAxs), ("hasSorryAx", toJson (axs.contains `sorryAx)),
    ("referenceFile", toJson "Iut/Tripod/CurveFacts.lean"),
    ("referenceLine", toJson line), ("provenance", toJson provenance)]

run_meta do
  unless Lean.versionString == "4.35.0-rc3" do throwError "Expected Lean 4.35.0-rc3"
  let config ← jsonFile (← absoluteEnv "TRIPOD_HEIGHT_FIELD_SOURCE_CONFIG")
  unless (← checked (config.getObjValAs? String "schema")) == "tripod-height-field-source/v1" do
    throwError "Unexpected source export configuration"
  let output ← checked (config.getObjValAs? String "sourceFactsFile")
  unless output.startsWith "/" do throwError "Expected an absolute source facts file path"
  let cache ← IO.mkRef ({} : Std.HashMap Name (Array Name))
  let mut records : Array Json := #[]
  for (name, line) in #[
      (``Iut.Tripod.curveInputsHeightEqReplay, 503),
      (``Iut.Tripod.curveInputsHtCanEquivReplay, 508),
      (``Iut.Tripod.curveInputsNorthcottReplay, 509)] do
    records := records.push (← fact cache name line "source-constructor-field-rhs-replay")
  IO.FS.writeFile output (String.intercalate "\n" (records.toList.map Json.compress) ++ "\n")
  logInfo m!"Exported {records.size} source theorem types and values with kernel and axiom checks"

end TripodHeightFieldSourceExpressions
