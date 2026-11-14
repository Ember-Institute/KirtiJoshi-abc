import Lean
import Iut.Implication.PrimeSelection


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
  | "const" => return .const (← relocateName names (← decodeName (← field j "name")))
      ((← (← arrayField j "levels").mapM decodeLevel).toList)
  | "app" => return .app (← recur (← field j "fn")) (← recur (← field j "arg"))
  | "lam" => return .lam (← decodeName (← field j "name")) (← recur (← field j "type"))
      (← recur (← field j "body")) (← decodeBinder (← stringField j "binder"))
  | "forall" => return .forallE (← decodeName (← field j "name")) (← recur (← field j "type"))
      (← recur (← field j "body")) (← decodeBinder (← stringField j "binder"))
  | "let" => return .letE (← decodeName (← field j "name")) (← recur (← field j "type"))
      (← recur (← field j "value")) (← recur (← field j "body"))
      (← (← field j "nondependent").getBool?)
  | "nat" => return .lit (.natVal (← (← field j "value").getNat?))
  | "string" => return .lit (.strVal (← stringField j "value"))
  | "proj" => return .proj (← relocateName names (← decodeName (← field j "name")))
      (← (← field j "index").getNat?) (← recur (← field j "body"))
  | k => throw s!"Unknown Expr kind: {k}"

end PrimeSelectionAudit


open Lean
namespace PrimeSelectionOriginalExprQuery

def names : Array Name := #[
  `Iut.ChebyshevBound.exists_prime_notMem,
  `Iut.LocalHeightData.exists_prime_selection,
  `Iut.sum_log_primeFactors_le]

def orThrow {α : Type} (value : Except String α) : MetaM α :=
  match value with
  | .ok a => pure a
  | .error e => throwError "{e}"

run_meta do
  unless Lean.versionString == "4.35.0-rc3" do
    throwError "Expected source compiler 4.35.0-rc3; got {Lean.versionString}"
  let mut records : Array Json := #[]
  for name in names do
    let ci ← getConstInfo name
    let typeJson ← orThrow (PrimeSelectionAudit.encodeExpr ci.type)
    let axioms ← collectAxioms name
    for ax in axioms do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Unexpected source theorem axiom {ax} in {name}"
    records := records.push (Json.mkObj [
      ("name", Json.str name.toString),
      ("nameExpr", PrimeSelectionAudit.encodeName name),
      ("levelParams", Json.arr (ci.levelParams.toArray.map PrimeSelectionAudit.encodeName)),
      ("levelParamDisplay", toJson (ci.levelParams.map Name.toString)),
      ("elaboratedExpr", typeJson),
      ("axioms", toJson (axioms.map Name.toString))])
  let path := (← IO.getEnv "PRIME_SELECTION_ORIGINAL_EXPR_OUTPUT").getD
    "/tmp/p2m-prime-selection-type-audit-20261115/original-exprs.json"
  IO.FS.writeFile path ((Json.mkObj [
    ("schema", Json.str "prime-selection-original-expr-v1"),
    ("compilerVersion", Json.str Lean.versionString),
    ("sourceModule", Json.str "Iut.Implication.PrimeSelection"),
    ("serialization", Json.str "compiler ConstantInfo.type; recursive metadata erasure; no pretty-printer round-trip"),
    ("records", Json.arr records)]).pretty ++ "\n")
  logInfo s!"Exported actual compiler types for {records.size} declarations to {path}"

end PrimeSelectionOriginalExprQuery
