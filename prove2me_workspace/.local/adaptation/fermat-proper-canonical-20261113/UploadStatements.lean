import Definitions.Def_FermatProperCarrier
import Definitions.Def_FermatProperComposition
import Definitions.Def_FermatProperDivisorHeight
import Definitions.Def_FermatProperDivisorComposition
import Definitions.Def_FermatLocalBelyi
import Definitions.Def_FermatLocalBelyiComposition
import Definitions.Def_FermatBelyiComparisons
import Definitions.Def_FermatCanonicalBelyiComposition

set_option autoImplicit false

theorem AbcAdaptation.Tripod.Fermat.Proper.modelExists : ∀ (N : ℕ), 3 < N → Nonempty (AbcAdaptation.Tripod.Fermat.Proper.Model N) := by sorry

theorem AbcAdaptation.Tripod.Fermat.Proper.placesDiscrete : ∀ {N : ℕ} (M : AbcAdaptation.Tripod.Fermat.Proper.Model N), AbcAdaptation.Tripod.Fermat.Proper.PlacesDiscrete M := by sorry

theorem AbcAdaptation.Tripod.Fermat.Proper.residuesFinite : ∀ {N : ℕ} (M : AbcAdaptation.Tripod.Fermat.Proper.Model N), AbcAdaptation.Tripod.Fermat.Proper.ResiduesFinite M := by sorry

theorem AbcAdaptation.Tripod.Fermat.Proper.affineIdentification : ∀ {N : ℕ} (M : AbcAdaptation.Tripod.Fermat.Proper.Model N),
  AbcAdaptation.Tripod.Fermat.Proper.PlacesDiscrete M →
    AbcAdaptation.Tripod.Fermat.Proper.ResiduesFinite M →
      Nonempty (AbcAdaptation.Tripod.Fermat.Proper.AffineIdentification M) := by sorry

theorem AbcAdaptation.Tripod.Fermat.Proper.noncriticalSelection : ∀ {N : ℕ} (M : AbcAdaptation.Tripod.Fermat.Proper.Model N) (hDVR : AbcAdaptation.Tripod.Fermat.Proper.PlacesDiscrete M),
  AbcAdaptation.Tripod.Fermat.Proper.ResiduesFinite M → AbcAdaptation.Tripod.Fermat.Proper.NoncriticalSelection M hDVR := by sorry

theorem AbcAdaptation.Tripod.Fermat.Proper.cuspsFinite : ∀ {N : ℕ} (M : AbcAdaptation.Tripod.Fermat.Proper.Model N) (hDVR : AbcAdaptation.Tripod.Fermat.Proper.PlacesDiscrete M),
  AbcAdaptation.Tripod.Fermat.Proper.ResiduesFinite M →
    ∀ (φ : ↥M.K),
      AbcAdaptation.Tripod.Fermat.Proper.IsBelyi M hDVR φ → (AbcAdaptation.Tripod.Fermat.Proper.cusps M hDVR φ).Finite := by sorry

theorem AbcAdaptation.Tripod.Fermat.Proper.polarPresentationExists : ∀ {N : ℕ} (M : AbcAdaptation.Tripod.Fermat.Proper.Model N) (hDVR : AbcAdaptation.Tripod.Fermat.Proper.PlacesDiscrete M),
  AbcAdaptation.Tripod.Fermat.Proper.ResiduesFinite M →
    ∀ (D : AbcAdaptation.Tripod.Fermat.Proper.Divisor M),
      Nonempty (AbcAdaptation.Tripod.Fermat.Proper.PolarPresentation M hDVR D) := by sorry

theorem AbcAdaptation.Tripod.Fermat.Proper.canonicalDivisorExists : ∀ {N : ℕ} (M : AbcAdaptation.Tripod.Fermat.Proper.Model N) (hDVR : AbcAdaptation.Tripod.Fermat.Proper.PlacesDiscrete M),
  AbcAdaptation.Tripod.Fermat.Proper.ResiduesFinite M →
    Nonempty (AbcAdaptation.Tripod.Fermat.Proper.CanonicalDivisorData M hDVR) := by sorry

theorem AbcAdaptation.Tripod.Fermat.Proper.infinityDivisorExists : ∀ {N : ℕ} (M : AbcAdaptation.Tripod.Fermat.Proper.Model N) (hDVR : AbcAdaptation.Tripod.Fermat.Proper.PlacesDiscrete M),
  AbcAdaptation.Tripod.Fermat.Proper.ResiduesFinite M →
    Nonempty (AbcAdaptation.Tripod.Fermat.Proper.InfinityDivisorData M hDVR) := by sorry

theorem AbcAdaptation.Tripod.Fermat.Proper.planeAdjunctionExists : ∀ {N : ℕ} (M : AbcAdaptation.Tripod.Fermat.Proper.Model N) (hDVR : AbcAdaptation.Tripod.Fermat.Proper.PlacesDiscrete M),
  3 < N →
    AbcAdaptation.Tripod.Fermat.Proper.ResiduesFinite M →
      ∀ (K : AbcAdaptation.Tripod.Fermat.Proper.CanonicalDivisorData M hDVR)
        (H : AbcAdaptation.Tripod.Fermat.Proper.InfinityDivisorData M hDVR),
        Nonempty (AbcAdaptation.Tripod.Fermat.Proper.PlaneAdjunctionData M hDVR K H) := by sorry

theorem AbcAdaptation.Tripod.Fermat.Proper.cuspGeneratorsExists : ∀ {N : ℕ} (M : AbcAdaptation.Tripod.Fermat.Proper.Model N) (hDVR : AbcAdaptation.Tripod.Fermat.Proper.PlacesDiscrete M),
  AbcAdaptation.Tripod.Fermat.Proper.ResiduesFinite M →
    ∀ (φ : ↥M.K),
      AbcAdaptation.Tripod.Fermat.Proper.IsBelyi M hDVR φ →
        ∀ (hfin : (AbcAdaptation.Tripod.Fermat.Proper.cusps M hDVR φ).Finite),
          Nonempty (AbcAdaptation.Tripod.Fermat.Proper.CuspGenerators M hDVR φ hfin) := by sorry

theorem AbcAdaptation.Tripod.Fermat.Proper.canonicalDivisorDegree : ∀ {N : ℕ} (M : AbcAdaptation.Tripod.Fermat.Proper.Model N) (hDVR : AbcAdaptation.Tripod.Fermat.Proper.PlacesDiscrete M),
  3 < N →
    AbcAdaptation.Tripod.Fermat.Proper.ResiduesFinite M →
      ∀ (K : AbcAdaptation.Tripod.Fermat.Proper.CanonicalDivisorData M hDVR)
        (H : AbcAdaptation.Tripod.Fermat.Proper.InfinityDivisorData M hDVR)
        (J : AbcAdaptation.Tripod.Fermat.Proper.PlaneAdjunctionData M hDVR K H),
        AbcAdaptation.Tripod.Fermat.Proper.divisorDegree M K.D =
          AbcAdaptation.Tripod.Fermat.Proper.planeCanonicalDegree N := by sorry

theorem AbcAdaptation.Tripod.Fermat.Proper.localCompactness : ∀ {N : ℕ} (M : AbcAdaptation.Tripod.Fermat.Proper.Model N),
  AbcAdaptation.Tripod.Fermat.Proper.PlacesDiscrete M →
    AbcAdaptation.Tripod.Fermat.Proper.ResiduesFinite M → AbcAdaptation.Tripod.Fermat.Proper.LocalCompactness M := by sorry

theorem AbcAdaptation.Tripod.Fermat.Proper.avoidanceRegularity : ∀ {N : ℕ} (M : AbcAdaptation.Tripod.Fermat.Proper.Model N) (hDVR : AbcAdaptation.Tripod.Fermat.Proper.PlacesDiscrete M),
  AbcAdaptation.Tripod.Fermat.Proper.AvoidanceRegularity M hDVR := by sorry

theorem AbcAdaptation.Tripod.Fermat.Proper.embeddingBoundsToSet : ∀ {N : ℕ} (M : AbcAdaptation.Tripod.Fermat.Proper.Model N),
  AbcAdaptation.Tripod.Fermat.Proper.ResiduesFinite M → AbcAdaptation.Tripod.Fermat.Proper.EmbeddingBoundsToSet M := by sorry

theorem AbcAdaptation.Tripod.Fermat.Proper.canonicalHeightIdentification : AbcAdaptation.Tripod.Fermat.Proper.CanonicalHeightIdentification := by sorry

theorem AbcAdaptation.Tripod.Fermat.Proper.belyiHeightRelation : AbcAdaptation.Tripod.Fermat.Proper.BelyiHeightRelation := by sorry

theorem AbcAdaptation.Tripod.Fermat.Proper.divisorDegreeHeightComparison : AbcAdaptation.Tripod.Fermat.Proper.DivisorDegreeHeightComparison := by sorry

theorem AbcAdaptation.Tripod.Fermat.Proper.belyiDifferentConductorComparison : AbcAdaptation.Tripod.Fermat.Proper.BelyiDifferentConductorComparison := by sorry

theorem AbcAdaptation.Tripod.Fermat.Proper.cuspConductorHeightComparison : AbcAdaptation.Tripod.Fermat.Proper.CuspConductorHeightComparison := by sorry

set_option pp.fullNames true
open Lean
run_meta do
  let mut rows : Array Json := #[]
  let info ← getConstInfo `AbcAdaptation.Tripod.Fermat.Proper.modelExists
  let fmt ← Lean.Meta.ppExpr info.type
  rows := rows.push (Json.mkObj [("name", Json.str "AbcAdaptation.Tripod.Fermat.Proper.modelExists"), ("type", Json.str fmt.pretty)])
  let info ← getConstInfo `AbcAdaptation.Tripod.Fermat.Proper.placesDiscrete
  let fmt ← Lean.Meta.ppExpr info.type
  rows := rows.push (Json.mkObj [("name", Json.str "AbcAdaptation.Tripod.Fermat.Proper.placesDiscrete"), ("type", Json.str fmt.pretty)])
  let info ← getConstInfo `AbcAdaptation.Tripod.Fermat.Proper.residuesFinite
  let fmt ← Lean.Meta.ppExpr info.type
  rows := rows.push (Json.mkObj [("name", Json.str "AbcAdaptation.Tripod.Fermat.Proper.residuesFinite"), ("type", Json.str fmt.pretty)])
  let info ← getConstInfo `AbcAdaptation.Tripod.Fermat.Proper.affineIdentification
  let fmt ← Lean.Meta.ppExpr info.type
  rows := rows.push (Json.mkObj [("name", Json.str "AbcAdaptation.Tripod.Fermat.Proper.affineIdentification"), ("type", Json.str fmt.pretty)])
  let info ← getConstInfo `AbcAdaptation.Tripod.Fermat.Proper.noncriticalSelection
  let fmt ← Lean.Meta.ppExpr info.type
  rows := rows.push (Json.mkObj [("name", Json.str "AbcAdaptation.Tripod.Fermat.Proper.noncriticalSelection"), ("type", Json.str fmt.pretty)])
  let info ← getConstInfo `AbcAdaptation.Tripod.Fermat.Proper.cuspsFinite
  let fmt ← Lean.Meta.ppExpr info.type
  rows := rows.push (Json.mkObj [("name", Json.str "AbcAdaptation.Tripod.Fermat.Proper.cuspsFinite"), ("type", Json.str fmt.pretty)])
  let info ← getConstInfo `AbcAdaptation.Tripod.Fermat.Proper.polarPresentationExists
  let fmt ← Lean.Meta.ppExpr info.type
  rows := rows.push (Json.mkObj [("name", Json.str "AbcAdaptation.Tripod.Fermat.Proper.polarPresentationExists"), ("type", Json.str fmt.pretty)])
  let info ← getConstInfo `AbcAdaptation.Tripod.Fermat.Proper.canonicalDivisorExists
  let fmt ← Lean.Meta.ppExpr info.type
  rows := rows.push (Json.mkObj [("name", Json.str "AbcAdaptation.Tripod.Fermat.Proper.canonicalDivisorExists"), ("type", Json.str fmt.pretty)])
  let info ← getConstInfo `AbcAdaptation.Tripod.Fermat.Proper.infinityDivisorExists
  let fmt ← Lean.Meta.ppExpr info.type
  rows := rows.push (Json.mkObj [("name", Json.str "AbcAdaptation.Tripod.Fermat.Proper.infinityDivisorExists"), ("type", Json.str fmt.pretty)])
  let info ← getConstInfo `AbcAdaptation.Tripod.Fermat.Proper.planeAdjunctionExists
  let fmt ← Lean.Meta.ppExpr info.type
  rows := rows.push (Json.mkObj [("name", Json.str "AbcAdaptation.Tripod.Fermat.Proper.planeAdjunctionExists"), ("type", Json.str fmt.pretty)])
  let info ← getConstInfo `AbcAdaptation.Tripod.Fermat.Proper.cuspGeneratorsExists
  let fmt ← Lean.Meta.ppExpr info.type
  rows := rows.push (Json.mkObj [("name", Json.str "AbcAdaptation.Tripod.Fermat.Proper.cuspGeneratorsExists"), ("type", Json.str fmt.pretty)])
  let info ← getConstInfo `AbcAdaptation.Tripod.Fermat.Proper.canonicalDivisorDegree
  let fmt ← Lean.Meta.ppExpr info.type
  rows := rows.push (Json.mkObj [("name", Json.str "AbcAdaptation.Tripod.Fermat.Proper.canonicalDivisorDegree"), ("type", Json.str fmt.pretty)])
  let info ← getConstInfo `AbcAdaptation.Tripod.Fermat.Proper.localCompactness
  let fmt ← Lean.Meta.ppExpr info.type
  rows := rows.push (Json.mkObj [("name", Json.str "AbcAdaptation.Tripod.Fermat.Proper.localCompactness"), ("type", Json.str fmt.pretty)])
  let info ← getConstInfo `AbcAdaptation.Tripod.Fermat.Proper.avoidanceRegularity
  let fmt ← Lean.Meta.ppExpr info.type
  rows := rows.push (Json.mkObj [("name", Json.str "AbcAdaptation.Tripod.Fermat.Proper.avoidanceRegularity"), ("type", Json.str fmt.pretty)])
  let info ← getConstInfo `AbcAdaptation.Tripod.Fermat.Proper.embeddingBoundsToSet
  let fmt ← Lean.Meta.ppExpr info.type
  rows := rows.push (Json.mkObj [("name", Json.str "AbcAdaptation.Tripod.Fermat.Proper.embeddingBoundsToSet"), ("type", Json.str fmt.pretty)])
  let info ← getConstInfo `AbcAdaptation.Tripod.Fermat.Proper.canonicalHeightIdentification
  let fmt ← Lean.Meta.ppExpr info.type
  rows := rows.push (Json.mkObj [("name", Json.str "AbcAdaptation.Tripod.Fermat.Proper.canonicalHeightIdentification"), ("type", Json.str fmt.pretty)])
  let info ← getConstInfo `AbcAdaptation.Tripod.Fermat.Proper.belyiHeightRelation
  let fmt ← Lean.Meta.ppExpr info.type
  rows := rows.push (Json.mkObj [("name", Json.str "AbcAdaptation.Tripod.Fermat.Proper.belyiHeightRelation"), ("type", Json.str fmt.pretty)])
  let info ← getConstInfo `AbcAdaptation.Tripod.Fermat.Proper.divisorDegreeHeightComparison
  let fmt ← Lean.Meta.ppExpr info.type
  rows := rows.push (Json.mkObj [("name", Json.str "AbcAdaptation.Tripod.Fermat.Proper.divisorDegreeHeightComparison"), ("type", Json.str fmt.pretty)])
  let info ← getConstInfo `AbcAdaptation.Tripod.Fermat.Proper.belyiDifferentConductorComparison
  let fmt ← Lean.Meta.ppExpr info.type
  rows := rows.push (Json.mkObj [("name", Json.str "AbcAdaptation.Tripod.Fermat.Proper.belyiDifferentConductorComparison"), ("type", Json.str fmt.pretty)])
  let info ← getConstInfo `AbcAdaptation.Tripod.Fermat.Proper.cuspConductorHeightComparison
  let fmt ← Lean.Meta.ppExpr info.type
  rows := rows.push (Json.mkObj [("name", Json.str "AbcAdaptation.Tripod.Fermat.Proper.cuspConductorHeightComparison"), ("type", Json.str fmt.pretty)])
  IO.FS.writeFile ".local/adaptation/fermat-proper-canonical-20261113/upload-elaborated-types.json" (Json.pretty (Json.arr rows))
