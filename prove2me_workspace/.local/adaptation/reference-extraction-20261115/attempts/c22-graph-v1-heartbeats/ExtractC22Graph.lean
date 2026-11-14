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
import Iut.Implication.Corollary22

set_option pp.fullNames true
set_option pp.funBinderTypes true
set_option pp.piBinderTypes true

open Lean
namespace ReferenceExtraction

def roots : Array Name := #[`Iut.Theorem110Invariants.theorem110, `Iut.ThetaDataExistence, `Iut.Corollary22Inputs.c2]
def participatingModules : Array Name := #[`TateCurvesTheta, `TateCurvesTheta.AnalyticQuotient, `TateCurvesTheta.Basic, `TateCurvesTheta.Uniformization, `Genl.GeneralPosition.HeightTheory, `Iut.Abc.Target, `Iut.Cor312.Container, `Iut.Cor312.ContainerHull, `Iut.Cor312.HolomorphicHull, `Iut.Cor312.LeftHandSide, `Iut.Cor312.LogVolume, `Iut.Cor312.PacketPresentation, `Iut.Cor312.Procession, `Iut.Cor312.RationalPlace, `Iut.Cor312.RightHandSide, `Iut.Cor312.Statement, `Iut.Implication.Corollary22, `Iut.Implication.Invariants, `Iut.Implication.LogVolumeBound, `Iut.Implication.PrimeSelection, `Iut.Implication.Theorem110, `TateCurvesTheta.Analysis.MaxTerm, `TateCurvesTheta.Analysis.Strassmann, `TateCurvesTheta.Analysis.StrassmannSphere, `TateCurvesTheta.Analysis.UltrametricSum, `TateCurvesTheta.Arithmetic.DivisorConvolution, `TateCurvesTheta.QParameter.BaseChange, `TateCurvesTheta.QParameter.Basic, `TateCurvesTheta.QParameter.Characterization, `TateCurvesTheta.QParameter.JParametrization, `TateCurvesTheta.QParameter.NormalizedOrder, `TateCurvesTheta.QParameter.PrimeToOrder, `TateCurvesTheta.TateCurve.A6Series, `TateCurvesTheta.TateCurve.AbelStep, `TateCurvesTheta.TateCurve.AdditionLaw, `TateCurvesTheta.TateCurve.CoordinateAnnulusLaurent, `TateCurvesTheta.TateCurve.CoordinateAnnulusLaurentY, `TateCurvesTheta.TateCurve.CoordinateBaseChange, `TateCurvesTheta.TateCurve.CoordinateExpansion, `TateCurvesTheta.TateCurve.CoordinateInversion, `TateCurvesTheta.TateCurve.DefectAnnulusLaurent, `TateCurvesTheta.TateCurve.DefectCoeffBaseChange, `TateCurvesTheta.TateCurve.DefectVanishing, `TateCurvesTheta.TateCurve.Discriminant, `TateCurvesTheta.TateCurve.EisensteinKernels, `TateCurvesTheta.TateCurve.EisensteinSeries, `TateCurvesTheta.TateCurve.GroupLaw, `TateCurvesTheta.TateCurve.IntegralModel, `TateCurvesTheta.TateCurve.JInvariant, `TateCurvesTheta.TateCurve.LargePointParametrization, `TateCurvesTheta.TateCurve.Parametrization, `TateCurvesTheta.TateCurve.PointMap, `TateCurvesTheta.TateCurve.Quotient, `TateCurvesTheta.TateCurve.SphereBounds, `TateCurvesTheta.TateCurve.SplitReduction, `TateCurvesTheta.TateCurve.SurjectivityAnnulus, `TateCurvesTheta.TateCurve.SurjectivitySphere, `TateCurvesTheta.TateCurve.TatePointMem, `TateCurvesTheta.TateCurve.TatePointOnCurve, `TateCurvesTheta.TateCurve.TateUniformization, `TateCurvesTheta.TateCurve.Weierstrass, `TateCurvesTheta.TateCurve.WeierstrassIdentity, `TateCurvesTheta.Theta.Basic, `TateCurvesTheta.Theta.Divisor, `TateCurvesTheta.Theta.Durfee, `TateCurvesTheta.Theta.FactorReciprocal, `TateCurvesTheta.Theta.FactorSeries, `TateCurvesTheta.Theta.Inversion, `TateCurvesTheta.Theta.LaurentSphere, `TateCurvesTheta.Theta.LaurentSphereReduce, `TateCurvesTheta.Theta.LaurentUnique, `TateCurvesTheta.Theta.LaurentUnitSphere, `TateCurvesTheta.Theta.Normalization, `TateCurvesTheta.Theta.Periodicity, `TateCurvesTheta.Theta.Product, `TateCurvesTheta.Theta.PuncturedProduct, `TateCurvesTheta.Theta.QBinomial, `TateCurvesTheta.Theta.RatioAnnulus, `TateCurvesTheta.Theta.SeriesZero, `TateCurvesTheta.Theta.StrictDominant, `TateCurvesTheta.Theta.ThetaProdGlobalLaurent, `TateCurvesTheta.Theta.ThetaProdLaurent, `TateCurvesTheta.Theta.TripleProduct, `TateCurvesTheta.Theta.Uniqueness, `TateCurvesTheta.Theta.WeightSpace, `Genl.Mathlib.Order.BoundedDiscrepancy, `Iut.Cor312.ThetaData.AdmissiblePrime, `Iut.Cor312.ThetaData.Basic, `Iut.Cor312.ThetaData.GlobalField, `Iut.Cor312.ThetaData.LocalConditions, `Iut.Cor312.ThetaData.Orbicurve, `Iut.Cor312.ThetaData.Places, `Iut.Cor312.ThetaData.PlacesOver, `Iut.Cor312.ThetaData.PointMap, `Iut.Cor312.ThetaData.TateFamily, `Iut.Cor312.ThetaData.TateStructure]
def outputPath : String :=
  "/home/admin-wsl/Coq/abc/prove2me_workspace/.local/adaptation/reference-extraction-20261115/c22-decl-graph.jsonl"

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
  unless Lean.versionString == "4.35.0-rc3" do
    throwError "Wrong original-source extraction compiler: {Lean.versionString}"
  let env ← getEnv
  let moduleOf : Name → Option Name := fun n => do
    let idx ← env.getModuleIdxFor? n
    env.header.moduleNames[idx.toNat]?
  let isProject : Name → Bool := fun n =>
    (moduleOf n).any participatingModules.contains
  for root in roots do
    unless isProject root do throwError "Reference root missing from imported environment: {root}"
  let modules := env.header.moduleNames.filter participatingModules.contains
  let mut lines : Array String := #[(Json.mkObj [
    ("record", Json.str "manifest"), ("schema", Json.str "reference-graph-v1"),
    ("roots", namesJson roots), ("compilerVersion", Json.str Lean.versionString),
    ("participatingModules", namesJson modules),
    ("directEdgesIncludeExternal", toJson true),
    ("compilerAuxiliariesRetained", toJson true)]).compress]
  let constants := env.constants.toList.toArray.qsort fun a b => Name.lt a.1 b.1
  for (n, ci) in constants do
    let some m := moduleOf n | continue
    unless participatingModules.contains m do continue
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

#print axioms Iut.Theorem110Invariants.theorem110
#print axioms Iut.ThetaDataExistence
#print axioms Iut.Corollary22Inputs.c2
