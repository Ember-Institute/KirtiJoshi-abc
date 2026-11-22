import Solutions.Source_ReferenceIutCor312CrystallineLogAllPowers
import Solutions.Source_ReferenceIutCor312CyclotomicLogLinear

set_option autoImplicit false

namespace JoshiTeich.Act1Scene1.CrystallineEnvelope

open LocalKummer

noncomputable section

variable (C : Type*) [NormedField C] [IsUltrametricDist C] [CompleteSpace C]
variable (p : ℕ) [Fact p.Prime] [Fact (0 < ‖(p : C)‖ ∧ ‖(p : C)‖ < 1)]
variable {Ω : Type*} [Field Ω] [CharZero Ω] [IsAlgClosed Ω]

/-- The crystalline period of the original Tate basis, transported by `j`. -/
abbrev mappedTateBasisPeriod (j : Ω →+* C) : ACrisInvertP C p :=
  algebraMap (ACris C p) (ACrisInvertP C p)
    (cyclotomicLog C p (mapCyclotomicTateGroup p j (TateBasis.generator (p := p) (Ω := Ω))))

/-- Every power of the original Tate period survives in the crystalline ring
after inverting `p`. -/
theorem mappedTateBasisPeriod_pow_ne_zero [IsAlgClosed C] (j : Ω →+* C) (m : ℕ) :
    mappedTateBasisPeriod C p j ^ m ≠ 0 := by
  let _ : CharZero C := charZero_of_injective_ringHom j.injective
  let ε := mapCyclotomicTateGroup p j (TateBasis.generator (p := p) (Ω := Ω))
  have hε : ε.1 1 ≠ 1 := by
    intro h
    change Units.map j.toMonoidHom ((TateBasis.generator (p := p) (Ω := Ω)).1 1) = 1 at h
    rw [← map_one (Units.map j.toMonoidHom)] at h
    exact (TateBasis.generator_isPrimitive (p := p) (Ω := Ω) 1).ne_one
      (by simpa only [pow_one] using (Fact.out : p.Prime).one_lt)
      (Units.map_injective (f := j.toMonoidHom) j.injective h)
  obtain ⟨b, hb, hxb⟩ := cyclotomicTeichmuller_exists_firstOrder C p ε hε
  exact logOfMemKer_pow_survives_of_firstOrder C p _
    (RootTower.cyclotomic_teichmuller_sub_one_mem_theta_ker ε) b hxb hb m

/-- The localization in which both `p` and the transported Tate period are
invertible. -/
abbrev ACrisInvertTatePeriod (j : Ω →+* C) :=
  Localization.Away (mappedTateBasisPeriod C p j)

instance instNontrivialACrisInvertTatePeriod [IsAlgClosed C] (j : Ω →+* C) :
    Nontrivial (ACrisInvertTatePeriod C p j) := by
  apply (IsLocalization.toLocalizationMap (Submonoid.powers (mappedTateBasisPeriod C p j))
    (ACrisInvertTatePeriod C p j)).nontrivial
  rintro ⟨m, hm⟩
  exact mappedTateBasisPeriod_pow_ne_zero C p j m hm

theorem ACrisInvertTatePeriod_period_isUnit (j : Ω →+* C) :
    IsUnit (algebraMap (ACrisInvertP C p) (ACrisInvertTatePeriod C p j)
      (mappedTateBasisPeriod C p j)) :=
  IsLocalization.Away.algebraMap_isUnit (S := ACrisInvertTatePeriod C p j) _

end

end JoshiTeich.Act1Scene1.CrystallineEnvelope
