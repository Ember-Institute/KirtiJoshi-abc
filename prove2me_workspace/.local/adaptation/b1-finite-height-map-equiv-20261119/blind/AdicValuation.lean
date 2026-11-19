def intValuationDef (r : R) : ℤᵐ⁰ :=
  if r = 0 then 0
  else
    exp (-(Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {r} : Ideal R)).factors : ℤ)

def intValuation : Valuation R ℤᵐ⁰ where
  toFun := v.intValuationDef
  map_zero' := intValuation.map_zero' v
  map_one' := intValuation.map_one' v
  map_mul' := intValuation.map_mul' v
  map_add_le_max' := intValuation.map_add_le_max' v

def valuation (v : HeightOneSpectrum R) : Valuation K ℤᵐ⁰ :=
  v.intValuation.extendToLocalization
    (fun r hr => Set.mem_compl <| v.intValuation_ne_zero' ⟨r, hr⟩) K
