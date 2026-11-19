@[simps]
def comap (f : R →+* S) (hf : Function.Surjective f) (v : HeightOneSpectrum S) :
    (HeightOneSpectrum R) where
  asIdeal := v.asIdeal.comap f
  isPrime := v.asIdeal.comap_isPrime f
  ne_bot := (Ideal.eq_bot_of_comap_eq_bot' hf).mt v.ne_bot

set_option backward.isDefEq.respectTransparency.types false in

@[simps]
def equivOfRingEquiv (e : R ≃+* S) : (HeightOneSpectrum R) ≃ (HeightOneSpectrum S) where
  toFun := HeightOneSpectrum.comap e.symm e.symm.surjective
  invFun := HeightOneSpectrum.comap e e.surjective
  left_inv x := by ext; simp
  right_inv x := by
    ext
    rw [← Ideal.map_comap_eq_self_of_equiv e x.asIdeal]
    simp only [comap_asIdeal, Ideal.mem_comap, RingHom.coe_coe, Ideal.symm_apply_mem_of_equiv_iff]
    exact Iff.rfl
