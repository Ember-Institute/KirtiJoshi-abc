/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors

Independent namespace adaptation and extraction of pinned Belyi source proofs.
Pinned Belyi: 9ce4d3f793d3bc831f2fc7214b7dbad90ea012d8.
Upstream: https://github.com/lana-agents/belyi.
Source: Belyi/CurveField/NoncriticalFinite.lean; SHA-256: 97605e681191f8a923c7de80df284e327550f708a884b5deb135e469b6a2bbf8.
-/
import Definitions.Def_FermatCurveDerivationAdjoin
import Definitions.Def_FermatCurveFieldPlace

set_option autoImplicit false

namespace AbcAdaptation.Tripod.Fermat.Proper.CurveDeriv

variable {K : Type*} [Field K] [CharZero K] [IsCurveField K]
variable {t : K} [Fact (Transcendental ℚ t)]

/-- Source span-induction block for actual chart module generators. -/
theorem derivAlong_mem_chartRing_of_generators (ht : Transcendental ℚ t)
    (P : Place K) (htP : t ∈ P.1) (G : Finset (chartRing t))
    (hG : Submodule.span (Algebra.adjoin ℚ {t}) (G : Set (chartRing t)) = ⊤)
    (hgood : ∀ g ∈ G, derivAlong t (g : K) ∈ P.1) :
    ∀ r : chartRing t, derivAlong t (r : K) ∈ P.1 := by
  intro r
  have hr : r ∈ Submodule.span (Algebra.adjoin ℚ {t}) (G : Set (chartRing t)) :=
    hG ▸ Submodule.mem_top
  induction hr using Submodule.span_induction with
  | mem g hg => exact hgood g hg
  | zero => simp
  | add x y _ _ hx hy =>
    rw [Subalgebra.coe_add, map_add]
    exact add_mem hx hy
  | smul a x _ hx =>
    rw [Subalgebra.coe_smul, Algebra.smul_def]
    change derivAlong t ((a : K) * x) ∈ P.1
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    exact add_mem (mul_mem (mem_of_mem_adjoin P.algebraMap_mem htP a.2) hx)
      (mul_mem (P.algebraMap_chartRing_mem t htP x)
        (derivAlong_mem_of_mem_adjoin ht P.algebraMap_mem htP a.2))

/-- Source localization block using the actual place, chart prime, and denominator inverse. -/
theorem derivAlong_mem_place_of_chartRing (P : Place K) (htP : t ∈ P.1)
    (hA : ∀ r : chartRing t, derivAlong t (r : K) ∈ P.1)
    {s : K} (hs : s ∈ P.1) : derivAlong t s ∈ P.1 := by
  have hs' : s ∈ (Place.ofChart t (P.toChart t htP)).1 := by rwa [Place.ofChart_toChart]
  rw [Place.ofChart_val] at hs'
  obtain ⟨a, u, hu, hsu⟩ := hs'
  subst hsu
  have hun : ((u : chartRing t) : K) ∉ P.1.nonunits := by
    rw [← Place.mem_toChart_iff t P htP]; exact hu
  rw [ValuationSubring.mem_nonunits_iff_or, not_or, not_not] at hun
  change derivAlong t ((a : K) * (u : K)⁻¹) ∈ P.1
  rw [← div_eq_mul_inv]
  rw [Derivation.leibniz_div, smul_eq_mul, smul_eq_mul, smul_eq_mul]
  exact mul_mem (pow_mem hun.2 2) (sub_mem (mul_mem (P.algebraMap_chartRing_mem t htP u) (hA a))
    (mul_mem (P.algebraMap_chartRing_mem t htP a) (hA u)))

end AbcAdaptation.Tripod.Fermat.Proper.CurveDeriv
