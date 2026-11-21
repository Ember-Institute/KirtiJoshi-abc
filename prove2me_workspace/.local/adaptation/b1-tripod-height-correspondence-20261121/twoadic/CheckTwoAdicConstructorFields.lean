import Lean
import Solutions.Source_TripodCurveInputsFromSource
import Solutions.Source_TripodCurveInputsTwoAdicField

set_option autoImplicit false

namespace TwoAdicConstructorFieldAudit

open AbcAdaptation.Tripod AbcAdaptation.Reference.Iut

/-- The source field with the constructor's hypothesis still explicit. -/
theorem heightEq_two_le_from_hB (P : CurveProviders) (K : CompactlyBounded) (d : ℕ)
    (hB : TwoAdicBoundHyp P K (max (4 * K.c) 0))
    (x : tripodTheory.Pt tripodTheory.tripod)
    (hx : x ∈ tripodTheory.cbsSet K ∩ tripodTheory.ptLE tripodTheory.tripod d) :
    ((P.curve x).localHeightData (P.arith x) (P.tate x)).heightEq 2 ≤ max (4 * K.c) 0 :=
  hB x hx.1

/-- The supplied arithmetic and Tate data give these fields in the Corollary 2.2 input. -/
theorem corollary22Fields (P : CurveProviders) (K : CompactlyBounded) (d : ℕ)
    {AG : AnabelianGeometry.{0}} {TK : ℝ}
    (CF : CurveFactsProp P K d TK) (hcore : CoreFinitenessHyp P K d AG)
    (hN : NorthcottHyp) (hh : LegendreHeightHyp P K)
    (x : tripodTheory.Pt tripodTheory.tripod)
    (hx : x ∈ tripodTheory.cbsSet K ∩ tripodTheory.ptLE tripodTheory.tripod d) :
    let CI := curveInputs_from_source P K d CF hcore hN hh (twoAdicBound P K)
    let I := CI.toCorollary22Inputs
    I.B = max (4 * K.c) 0 ∧
      I.B_nonneg = curveInputs_B_nonneg K ∧
      I.heightEq_two_le x hx = curveInputs_heightEq_two_le P K d x hx :=
  ⟨rfl, rfl, rfl⟩

open Lean Elab Term Meta

/- Read the compiled assignments as expressions so proof irrelevance cannot hide a change
in the constructor's use of the explicit hypothesis. -/
run_meta do
  let constructor := ``curveInputsOfSL2Image
  let structureName := ``CurveInputs
  let env ← getEnv
  let some structureInfo := getStructureInfo? env structureName |
    throwError "Could not read the CurveInputs field names"
  let .defnInfo declaration ← getConstInfo constructor |
    throwError "Could not read curveInputsOfSL2Image"
  lambdaTelescope declaration.value fun args body => do
    let body := body.consumeMData
    let .const ctorName _ := body.getAppFn |
      throwError "Expected a CurveInputs constructor application"
    let ctor ← getConstInfoCtor ctorName
    unless ctor.induct == structureName do
      throwError "Expected the CurveInputs constructor"
    let fields := body.getAppArgs
    let fieldValue (name : Name) : MetaM Expr := do
      let some index := structureInfo.fieldNames.findIdx? (· == name) |
        throwError "Could not find field {name}"
      let some value := fields[ctor.numParams + index]? |
        throwError "Could not read field {name}"
      -- Lean moves nontrivial proof fields into auxiliary theorems of this definition.
      let proof ← deltaExpand value (fun n => constructor.isPrefixOf (privateToUserName n))
        (allowOpaque := true)
      return proof.consumeMData
    let nonneg ← fieldValue `B_nonneg
    unless nonneg.getAppFn.isConstOf ``le_max_right do
      throwError "Expected le_max_right in B_nonneg, found {nonneg.getAppFn}"
    let binderNames ← args.mapM fun arg => return (← arg.fvarId!.getDecl).userName
    let some index := binderNames.findIdx? (· == `hB) |
      throwError "Could not find the two-adic hypothesis binder"
    let hB := args[index]!
    lambdaTelescope (← fieldValue `heightEq_two_le) fun binders proof => do
      let proof := proof.consumeMData
      let actual := proof.getAppArgs
      unless binders.size == 2 && proof.getAppFn == hB && actual.size == 2 &&
          actual[0]! == binders[0]! do
        throwError "Expected heightEq_two_le to apply hB to the field's point and membership"
      let membership := actual[1]!.consumeMData
      let compactMembership := match membership with
        | .proj name index premise =>
          name == ``And && index == 0 && premise == binders[1]!
        | _ =>
          membership.getAppFn.isConstOf ``And.left &&
            membership.getAppArgs[membership.getAppNumArgs - 1]? == some binders[1]!
      unless compactMembership do
        throwError "Expected the compact membership obtained from hx.1"
  logInfo "Read the compiled B_nonneg and heightEq_two_le assignments"

#print axioms heightEq_two_le_from_hB
#print axioms corollary22Fields

end TwoAdicConstructorFieldAudit
