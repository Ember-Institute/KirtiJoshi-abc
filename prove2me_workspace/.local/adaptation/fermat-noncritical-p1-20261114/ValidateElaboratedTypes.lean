import Definitions.Def_FermatNoncriticalP1Reduction

set_option autoImplicit false
open scoped IntermediateField

theorem AbcAdaptation.Tripod.Fermat.Proper.noncriticalP1Normalize : ∀ (T : Finset AbcAdaptation.Tripod.Qbar),
  AbcAdaptation.Tripod.Fermat.Proper.NoncriticalP1.IsGalStable T →
    ∀ {τ : ℚ},
      ↑τ ∉ T →
        ∃ (u : AbcAdaptation.Tripod.Fermat.Proper.NoncriticalP1.ElemMap) (T₁ : Finset AbcAdaptation.Tripod.Qbar),
          AbcAdaptation.Tripod.Fermat.Proper.NoncriticalP1.IsGalStable T₁ ∧
            (∀ y ∈ T₁, ‖AbcAdaptation.Tripod.Fermat.Proper.NoncriticalP1.ι y‖ ≤ 1) ∧
              (∀ (d : ℕ),
                  1 ≤ d →
                    (∀ t ∈ T, AbcAdaptation.Tripod.deg t ≤ d) →
                      (∀ y ∈ T₁, AbcAdaptation.Tripod.deg y ≤ d) ∧
                        (2 ≤ d →
                          {y ∈ T₁ | AbcAdaptation.Tripod.deg y = d}.card ≤
                            {t ∈ T | AbcAdaptation.Tripod.deg t = d}.card)) ∧
                ∀ (hs : List AbcAdaptation.Tripod.Fermat.Proper.NoncriticalP1.ElemMap),
                  AbcAdaptation.Tripod.Fermat.Proper.NoncriticalP1.IsNoncriticalBelyi hs
                      (AbcAdaptation.Tripod.Fermat.Proper.NoncriticalP1.withInf T₁)
                      (AbcAdaptation.Tripod.Fermat.Proper.NoncriticalP1.ofRat 9) →
                    AbcAdaptation.Tripod.Fermat.Proper.NoncriticalP1.IsNoncriticalBelyi (u :: hs)
                      (AbcAdaptation.Tripod.Fermat.Proper.NoncriticalP1.withInf T)
                      (AbcAdaptation.Tripod.Fermat.Proper.NoncriticalP1.ofRat τ) := by sorry

theorem AbcAdaptation.Tripod.Fermat.Proper.noncriticalP1Rational : ∀ (T : Finset AbcAdaptation.Tripod.Qbar),
  (∀ y ∈ T, ‖AbcAdaptation.Tripod.Fermat.Proper.NoncriticalP1.ι y‖ ≤ 1) →
    (∀ y ∈ T, AbcAdaptation.Tripod.deg y ≤ 1) →
      ∃ (hs : List AbcAdaptation.Tripod.Fermat.Proper.NoncriticalP1.ElemMap),
        AbcAdaptation.Tripod.Fermat.Proper.NoncriticalP1.IsNoncriticalBelyi hs
          (AbcAdaptation.Tripod.Fermat.Proper.NoncriticalP1.withInf T)
          (AbcAdaptation.Tripod.Fermat.Proper.NoncriticalP1.ofRat 9) := by sorry

theorem AbcAdaptation.Tripod.Fermat.Proper.noncriticalP1Minpoly : ∀ (T : Finset AbcAdaptation.Tripod.Qbar),
  AbcAdaptation.Tripod.Fermat.Proper.NoncriticalP1.IsGalStable T →
    (∀ y ∈ T, ‖AbcAdaptation.Tripod.Fermat.Proper.NoncriticalP1.ι y‖ ≤ 1) →
      ∀ {d n : ℕ},
        2 ≤ d →
          (∀ y ∈ T, AbcAdaptation.Tripod.deg y ≤ d) →
            {y ∈ T | AbcAdaptation.Tripod.deg y = d}.card ≤ n + 1 →
              ∀ {σ₀ : AbcAdaptation.Tripod.Qbar},
                σ₀ ∈ T →
                  AbcAdaptation.Tripod.deg σ₀ = d →
                    ∃ (T₂ : Finset AbcAdaptation.Tripod.Qbar) (τ₂ : ℚ),
                      AbcAdaptation.Tripod.Fermat.Proper.NoncriticalP1.IsGalStable T₂ ∧
                        ↑τ₂ ∉ T₂ ∧
                          (∀ y ∈ T₂, AbcAdaptation.Tripod.deg y ≤ d) ∧
                            {y ∈ T₂ | AbcAdaptation.Tripod.deg y = d}.card ≤ n ∧
                              ∃ (u : AbcAdaptation.Tripod.Fermat.Proper.NoncriticalP1.ElemMap),
                                ∀ (hs : List AbcAdaptation.Tripod.Fermat.Proper.NoncriticalP1.ElemMap),
                                  AbcAdaptation.Tripod.Fermat.Proper.NoncriticalP1.IsNoncriticalBelyi hs
                                      (AbcAdaptation.Tripod.Fermat.Proper.NoncriticalP1.withInf T₂)
                                      (AbcAdaptation.Tripod.Fermat.Proper.NoncriticalP1.ofRat τ₂) →
                                    AbcAdaptation.Tripod.Fermat.Proper.NoncriticalP1.IsNoncriticalBelyi (u :: hs)
                                      (AbcAdaptation.Tripod.Fermat.Proper.NoncriticalP1.withInf T)
                                      (AbcAdaptation.Tripod.Fermat.Proper.NoncriticalP1.ofRat 9) := by sorry

set_option pp.fullNames true
set_option pp.funBinderTypes true
open Lean
run_meta do
  let mut rows : Array Json := #[]
  let info ← getConstInfo `AbcAdaptation.Tripod.Fermat.Proper.noncriticalP1Normalize
  let fmt ← Lean.Meta.ppExpr info.type
  rows := rows.push (Json.mkObj [("name", Json.str "AbcAdaptation.Tripod.Fermat.Proper.noncriticalP1Normalize"), ("type", Json.str fmt.pretty)])
  let info ← getConstInfo `AbcAdaptation.Tripod.Fermat.Proper.noncriticalP1Rational
  let fmt ← Lean.Meta.ppExpr info.type
  rows := rows.push (Json.mkObj [("name", Json.str "AbcAdaptation.Tripod.Fermat.Proper.noncriticalP1Rational"), ("type", Json.str fmt.pretty)])
  let info ← getConstInfo `AbcAdaptation.Tripod.Fermat.Proper.noncriticalP1Minpoly
  let fmt ← Lean.Meta.ppExpr info.type
  rows := rows.push (Json.mkObj [("name", Json.str "AbcAdaptation.Tripod.Fermat.Proper.noncriticalP1Minpoly"), ("type", Json.str fmt.pretty)])
  IO.FS.writeFile ".local/adaptation/fermat-noncritical-p1-20261114/upload-elaborated-types.json" (Json.pretty (Json.arr rows))
