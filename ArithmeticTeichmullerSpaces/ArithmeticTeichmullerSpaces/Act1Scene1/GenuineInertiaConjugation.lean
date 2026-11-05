import ArithmeticTeichmullerSpaces.Act1Scene1.GenuineInertiaGenerators
import ArithmeticTeichmullerSpaces.Act1Scene1.GenuineSignedBaseNormalizationRing
import ArithmeticTeichmullerSpaces.Act1Scene1.GenuineSignedCompositum

/-!
source-id: JT-SCENE1-GENUINE-VALUATION-INERTIA-CONJUGATION
source: Joshi III `ss:theta-data-fixing2`; the valuation-inertia part of the
base generator construction.  The proof is independent of the reference
implementation and uses only the local valuation-subring API.
boundary: Scene1/Derived.  The result records conjugation stability of the
valuation witness and of the base generator set.  Closed normal quotients,
etale identities, Cartesian covering data, and all future quotient/producer
interfaces remain outside this file.
-/

namespace JoshiTeich.ReferenceIut.Anabelian.Genuine

open WeierstrassCurve
open scoped Classical
universe u
noncomputable section

variable {k : Type u} [Field k] [CharZero k]
  (E : WeierstrassCurve k) [E.IsElliptic]

/-! The strict valuation inequality is transported through a comap by using
the nonunit characterization.  This keeps the value groups of the two
valuation subrings separate. -/

theorem valuationInertiaAt_conj (h σ : Gal E) (W : ValuationSubring (Ω E))
    (hσ : valuationInertiaAt E σ W) :
    valuationInertiaAt E (h * σ * h⁻¹)
      (W.comap ((h⁻¹ : Gal E).toRingEquiv.toRingHom)) := by
  intro a ha
  let d : Ω E := (h * σ * h⁻¹) a - a
  have haW : h⁻¹ a ∈ W :=
    (ValuationSubring.mem_comap).mp ha
  have hsource : h⁻¹ d ∈ W.nonunits := by
    apply (W.mem_nonunits_iff).2
    have hdiff : h⁻¹ d = σ (h⁻¹ a) - h⁻¹ a := by
      dsimp [d]
      simp only [map_sub, AlgEquiv.symm_apply_apply]
    rw [hdiff]
    exact hσ (h⁻¹ a) haW
  rw [← (W.comap ((h⁻¹ : Gal E).toRingEquiv.toRingHom)).mem_nonunits_iff]
  rw [(W.comap ((h⁻¹ : Gal E).toRingEquiv.toRingHom)).mem_nonunits_iff_or]
  rw [W.mem_nonunits_iff_or] at hsource
  rcases hsource with hzero | hinv
  · left
    have hd : d = 0 := by
      apply (h⁻¹ : Gal E).injective
      simpa only [map_zero] using hzero
    change d = 0
    exact hd
  · right
    intro hd_inv
    apply hinv
    have hd_inv' : h⁻¹ (d⁻¹) ∈ W :=
      (ValuationSubring.mem_comap).mp hd_inv
    simpa only [map_inv₀] using hd_inv'

theorem valuationInertiaAt_conj_mem_comap (h σ : Gal E)
    (W : ValuationSubring (Ω E))
    (hσ : ∀ a ∈ W, W.valuation (σ a - a) < 1) :
    ∀ a ∈ W.comap ((h⁻¹ : Gal E).toRingEquiv.toRingHom),
      (W.comap ((h⁻¹ : Gal E).toRingEquiv.toRingHom)).valuation
        ((h * σ * h⁻¹) a - a) < 1 :=
  valuationInertiaAt_conj E h σ W hσ

private theorem act_conj_generic (h σ : Gal E)
    (hσ : act E σ (genericPoint E) = genericPoint E) :
    act E (h * σ * h⁻¹) (genericPoint E) = genericPoint E := by
  rcases act_generic_eq_or_neg E h with hh | hh <;>
    rcases act_generic_eq_or_neg E h⁻¹ with hi | hi
  · rw [act_mul, act_mul, hi, hσ, hh]
  · exfalso
    have hbad : genericPoint E = -genericPoint E := by
      calc
        genericPoint E = act E h (act E h⁻¹ (genericPoint E)) := by
          rw [← act_mul, mul_inv_cancel, act_one]
        _ = act E h (-genericPoint E) := by rw [hi]
        _ = -act E h (genericPoint E) := by rw [map_neg]
        _ = -genericPoint E := by rw [hh]
    exact (genericPoint_ne_neg E hbad).elim
  · exfalso
    have hbad : genericPoint E = -genericPoint E := by
      calc
        genericPoint E = act E h⁻¹ (act E h (genericPoint E)) := by
          rw [← act_mul, inv_mul_cancel, act_one]
        _ = act E h⁻¹ (-genericPoint E) := by rw [hh]
        _ = -act E h⁻¹ (genericPoint E) := by rw [map_neg]
        _ = -genericPoint E := by rw [hi]
    exact (genericPoint_ne_neg E hbad).elim
  · rw [act_mul, act_mul, hi, map_neg]
    rw [hσ, map_neg, hh, neg_neg]

theorem baseValuationInertiaGenerators_conj_mem
    (h σ : Gal E) (hσ : σ ∈ baseValuationInertiaGenerators E) :
    h * σ * h⁻¹ ∈ baseValuationInertiaGenerators E := by
  rcases hσ with ⟨hσG, W, hk, hx, hI⟩
  let W' : ValuationSubring (Ω E) :=
    W.comap ((h⁻¹ : Gal E).toRingEquiv.toRingHom)
  have hkc : ∀ c : k, algebraMap k (Ω E) c ∈ W' := by
    intro c
    rw [show W' = W.comap ((h⁻¹ : Gal E).toRingEquiv.toRingHom) from rfl,
      ValuationSubring.mem_comap]
    change h⁻¹ (algebraMap k (Ω E) c) ∈ W
    have hc : h⁻¹ (algebraMap k (Ω E) c) = algebraMap k (Ω E) c := by
      exact (σk E h⁻¹).commutes c
    rw [hc]
    exact hk c
  have hxc : xG E ∈ W' := by
    rw [show W' = W.comap ((h⁻¹ : Gal E).toRingEquiv.toRingHom) from rfl,
      ValuationSubring.mem_comap]
    change h⁻¹ (xG E) ∈ W
    have hxinv : h⁻¹ (xG E) = xG E := by
      exact h⁻¹.commutes ⟨_, xG_mem_baseField E⟩
    rw [hxinv]
    exact hx
  refine ⟨act_conj_generic E h σ hσG, W', hkc, hxc, ?_⟩
  exact valuationInertiaAt_conj E h σ W hI

theorem baseValuationInertiaGenerators_conj_stable (h : Gal E) :
    (fun σ => h * σ * h⁻¹) '' baseValuationInertiaGenerators E ⊆
      baseValuationInertiaGenerators E := by
  rintro σ ⟨τ, hτ, rfl⟩
  exact baseValuationInertiaGenerators_conj_mem E h τ hτ

theorem baseValuationInertiaGenerators_conj_eq (h : Gal E) :
    (fun σ => h * σ * h⁻¹) '' baseValuationInertiaGenerators E =
      baseValuationInertiaGenerators E := by
  apply Set.Subset.antisymm
  · exact baseValuationInertiaGenerators_conj_stable E h
  · rintro σ hσ
    refine ⟨h⁻¹ * σ * h, ?_, ?_⟩
    · exact baseValuationInertiaGenerators_conj_mem E h⁻¹ σ hσ
    · simp [mul_assoc]

end
end JoshiTeich.ReferenceIut.Anabelian.Genuine
