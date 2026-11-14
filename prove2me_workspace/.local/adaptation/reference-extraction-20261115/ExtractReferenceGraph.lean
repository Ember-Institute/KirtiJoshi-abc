/-
Draft, not yet compiled. Derived from:
  prove2me_workspace/scripts/extract_decl_graph.lean
  .local/adaptation/different-accounting-sourceproof-20261115/ExtractDifferentAccountingGraph.lean

Read this in the built reference environment, through MCP-CI only. Keep this
file without a `module` header: the old-style import environment loads private
declaration bodies transitively. If converted to the new module system, the
participating modules need `import all` visibility before extracting proof edges.

Unlike the baseline, emit ALL project constants, including compiler auxiliaries,
and do NOT flatten hidden constants into their consumers. Exact direct edges
and external dependencies remain available. Reachability precedes subtraction.
-/
import Lean
import Iut.Tripod.ClassicalAbcOfVariant

set_option pp.fullNames true
set_option pp.funBinderTypes true
set_option pp.piBinderTypes true
set_option pp.universes true
set_option pp.explicit true

open Lean
namespace ReferenceExtraction

def roots : Array Name := #[`Iut.Tripod.classicalABC_of_variant]
def projectPrefix : Name := `Iut
def outputPath : String :=
  "/tmp/p2m-reference-skeleton-tool-20261115/reference-decl-graph.jsonl"

def namesJson (ns : Array Name) : Json :=
  toJson ((ns.qsort Name.lt).map Name.toString)

def valueConstants (ci : ConstantInfo) : Array Name :=
  -- `value?` without allowOpaque omits theorem values on both toolchains.
  match ci with
  | .thmInfo t => t.value.getUsedConstants
  | .defnInfo d => d.value.getUsedConstants
  | .opaqueInfo o => o.value.getUsedConstants
  | _ => #[]

def kind (ci : ConstantInfo) : String :=
  match ci with
  | .thmInfo _ => "theorem" | .defnInfo _ => "def" | .axiomInfo _ => "axiom"
  | .opaqueInfo _ => "opaque" | .inductInfo _ => "inductive" | .ctorInfo _ => "ctor"
  | .recInfo _ => "rec" | .quotInfo _ => "quot"

def positionJson (p : Position) : Json :=
  Json.mkObj [("line", toJson p.line), ("col", toJson p.column)]

def declarationRangeJson (r : DeclarationRange) : Json :=
  Json.mkObj [("start", positionJson r.pos), ("end", positionJson r.endPos),
    ("startUtf16", toJson r.charUtf16), ("endUtf16", toJson r.endCharUtf16)]

run_meta do
  let env ← getEnv
  let moduleOf : Name → Option Name := fun n => do
    let idx ← env.getModuleIdxFor? n
    env.header.moduleNames[idx.toNat]?
  let isProject : Name → Bool := fun n =>
    (moduleOf n).any (projectPrefix.isPrefixOf ·)
  for root in roots do
    unless isProject root do throwError "Reference root missing from imported environment: {root}"
  let modules := env.header.moduleNames.filter (projectPrefix.isPrefixOf ·)
  let mut lines : Array String := #[(Json.mkObj [
    ("record", Json.str "manifest"), ("schema", Json.str "reference-graph-v1"),
    ("roots", namesJson roots), ("projectPrefix", Json.str projectPrefix.toString),
    ("participatingModules", namesJson modules),
    ("directEdgesIncludeExternal", toJson true),
    ("compilerAuxiliariesRetained", toJson true)]).compress]
  let constants := env.constants.toList.toArray.qsort fun a b => Name.lt a.1 b.1
  for (n, ci) in constants do
    let some m := moduleOf n | continue
    unless projectPrefix.isPrefixOf m do continue
    let tdeps := ci.type.getUsedConstants
    let vdeps := valueConstants ci
    let ctors := match ci with
      | .inductInfo i => i.ctors.toArray
      | _ => #[]
    let range ← findDeclarationRanges? n
    let axioms ← collectAxioms n
    let isInst ← Lean.Meta.isInstance n
    let userName := (privateToUserName? n).getD n
    let sourceFile := (m.toString.replace "." "/") ++ ".lean"
    let external := (tdeps ++ vdeps).filter (!isProject ·)
    let externalFacts := external.map fun dep => Json.mkObj [
      ("name", Json.str dep.toString),
      ("module", (moduleOf dep).map (Json.str ·.toString) |>.getD Json.null)]
    let elaboratedBinders ← Lean.Meta.forallTelescope ci.type fun xs result => do
      let mut bs : Array Json := #[]
      for x in xs do
        let d ← x.fvarId!.getDecl
        bs := bs.push (Json.mkObj [
          ("name", Json.str d.userName.toString),
          ("binderInfo", Json.str (reprStr d.binderInfo)),
          ("type", Json.str (← Lean.Meta.ppExpr d.type).pretty)])
      return Json.mkObj [("binders", Json.arr bs),
        ("result", Json.str (← Lean.Meta.ppExpr result).pretty)]
    lines := lines.push (Json.mkObj [
      ("record", Json.str "decl"), ("name", Json.str n.toString),
      ("userName", Json.str userName.toString),
      ("module", Json.str m.toString), ("sourceFile", Json.str sourceFile),
      ("kind", Json.str (kind ci)),
      ("isPrivate", toJson (privateToUserName? n).isSome),
      ("isInternal", toJson n.isInternal), ("isInstance", toJson isInst),
      ("elaboratedType", Json.str (← Lean.Meta.ppExpr ci.type).pretty),
      ("elaboratedTelescope", elaboratedBinders),
      ("range", range.map (declarationRangeJson ·.range) |>.getD Json.null),
      ("selectionRange", range.map (declarationRangeJson ·.selectionRange) |>.getD Json.null),
      ("startLine", toJson (range.map (·.range.pos.line) |>.getD 0)),
      ("endLine", toJson (range.map (·.range.endPos.line) |>.getD 0)),
      ("typeDeps", namesJson (tdeps.filter isProject)),
      ("valueDeps", namesJson (vdeps.filter isProject)),
      ("directTypeDeps", namesJson tdeps), ("directValueDeps", namesJson vdeps),
      ("constructors", namesJson ctors),
      ("externalDependencies", Json.arr externalFacts),
      ("axioms", namesJson axioms),
      ("hasSorryAx", toJson (axioms.contains `sorryAx))]).compress
  IO.FS.writeFile outputPath (String.intercalate "\n" lines.toList ++ "\n")
  logInfo s!"wrote {lines.size - 1} project constants to {outputPath}"

end ReferenceExtraction
