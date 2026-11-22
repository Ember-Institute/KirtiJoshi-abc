import Solutions.Source_ReferenceIutCor312KummerCrystallineBridge

set_option autoImplicit false

namespace JoshiTeich.Act1Scene1.CrystallineEnvelope

open JoshiTeich.Prologue

noncomputable section

variable (C : Type*) [NormedField C] [IsUltrametricDist C]
variable (p : ℕ) [Fact p.Prime] [Fact (0 < ‖(p : C)‖ ∧ ‖(p : C)‖ < 1)]

local notation "ι" => algebraMap (Ainf C p) (AinfInvertP C p)

private theorem mapInvertP_unit (f : Ainf C p →+* Ainf C p) :
    IsUnit (((ι).comp f) (p : Ainf C p)) := by
  simpa only [RingHom.comp_apply, map_natCast] using
    natCast_isUnit C p p (Fact.out : p.Prime).ne_zero

private def mapInvertP (f : Ainf C p →+* Ainf C p) :
    AinfInvertP C p →+* AinfInvertP C p :=
  Localization.awayLift ((ι).comp f) (p : Ainf C p) (mapInvertP_unit C p f)

@[simp]
private theorem mapInvertP_algebraMap (f : Ainf C p →+* Ainf C p) (x : Ainf C p) :
    mapInvertP C p f (ι x) = ι (f x) := by
  unfold mapInvertP
  exact IsLocalization.Away.lift_eq (p : Ainf C p) (mapInvertP_unit C p f) x

private theorem mapInvertP_gamma (f : Ainf C p →+* Ainf C p) (n : ℕ) (x : Ainf C p) :
    mapInvertP C p f (gamma C p n x) = gamma C p n (f x) := by
  apply (natCast_isUnit C p n.factorial n.factorial_ne_zero).mul_left_cancel
  rw [factorial_mul_gamma]
  simpa only [map_mul, map_natCast, map_pow, mapInvertP_algebraMap] using
    congrArg (mapInvertP C p f) (factorial_mul_gamma C p n x)

variable [CompleteSpace C]

local notation "θ" => (Perfectoid.thetaMap (O := LocalGeometricFontaine.integerRing C) (p := p))

private theorem mapInvertP_mem_A0 (f : Ainf C p →+* Ainf C p)
    (hf : ∀ x ∈ RingHom.ker θ, f x ∈ kerSupPrime C p)
    (a : AinfInvertP C p) (ha : a ∈ A0 C p) : mapInvertP C p f a ∈ A0 C p := by
  refine Algebra.adjoin_induction (p := fun z _ => mapInvertP C p f z ∈ A0 C p)
    ?_ ?_ ?_ ?_ ha
  · rintro _ ⟨n, x, hx, rfl⟩
    rw [mapInvertP_gamma]
    exact gamma_mem_A0_of_mem_ker_sup_prime C p n (hf x hx)
  · intro x
    rw [mapInvertP_algebraMap]
    exact (A0 C p).algebraMap_mem (f x)
  · intro x y _ _ hx hy
    rw [map_add]
    exact (A0 C p).add_mem hx hy
  · intro x y _ _ hx hy
    rw [map_mul]
    exact (A0 C p).mul_mem hx hy

/-- A Witt endomorphism extends to the integral divided-power subalgebra
if it sends the Fontaine kernel into the Fontaine kernel plus the prime ideal. -/
def mapA0 (f : Ainf C p →+* Ainf C p)
    (hf : ∀ x ∈ RingHom.ker θ, f x ∈ kerSupPrime C p) : A0 C p →+* A0 C p :=
  (mapInvertP C p f).restrict (A0 C p) (A0 C p) (mapInvertP_mem_A0 C p f hf)

@[simp]
theorem mapA0_algebraMap (f : Ainf C p →+* Ainf C p)
    (hf : ∀ x ∈ RingHom.ker θ, f x ∈ kerSupPrime C p) (x : Ainf C p) :
    mapA0 C p f hf (algebraMap (Ainf C p) (A0 C p) x) =
      algebraMap (Ainf C p) (A0 C p) (f x) := by
  apply Subtype.ext
  exact mapInvertP_algebraMap C p f x

theorem mapA0_gammaInOfMemKerSupPrime (f : Ainf C p →+* Ainf C p)
    (hf : ∀ x ∈ RingHom.ker θ, f x ∈ kerSupPrime C p) (n : ℕ) (x : Ainf C p)
    (hx : x ∈ kerSupPrime C p) (hfx : f x ∈ kerSupPrime C p) :
    mapA0 C p f hf (gammaInOfMemKerSupPrime C p n x hx) =
      gammaInOfMemKerSupPrime C p n (f x) hfx := by
  apply Subtype.ext
  exact mapInvertP_gamma C p f n x

local notation "I" => (Ideal.span {(p : A0 C p)} : Ideal (A0 C p))

private theorem adicPow_le_comap (f : A0 C p →+* A0 C p) (n : ℕ) :
    I ^ n ≤ (I ^ n).comap f := by
  rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow, Ideal.map_span, Set.image_singleton, map_natCast]

private def mapQuotient (f : A0 C p →+* A0 C p) (n : ℕ) :
    ((A0 C p) ⧸ I ^ n) →+* ((A0 C p) ⧸ I ^ n) :=
  Ideal.quotientMap (I ^ n) f (adicPow_le_comap C p f n)

@[simp]
private theorem mapQuotient_mk (f : A0 C p →+* A0 C p) (n : ℕ) (x : A0 C p) :
    mapQuotient C p f n (Ideal.Quotient.mk (I ^ n) x) =
      Ideal.Quotient.mk (I ^ n) (f x) :=
  Ideal.quotientMap_mk

private theorem factorPow_mapQuotient (f : A0 C p →+* A0 C p)
    {m n : ℕ} (hmn : m ≤ n) (z : (A0 C p) ⧸ I ^ n) :
    Ideal.Quotient.factorPow I hmn (mapQuotient C p f n z) =
      mapQuotient C p f m (Ideal.Quotient.factorPow I hmn z) := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
  simp only [mapQuotient_mk, Ideal.Quotient.factor_mk]

private theorem factorPow_eval (z : ACris C p) {m n : ℕ} (hmn : m ≤ n) :
    Ideal.Quotient.factorPow I hmn (AdicCompletion.evalₐ I n z) =
      AdicCompletion.evalₐ I m z := by
  obtain ⟨s, rfl⟩ := AdicCompletion.mk_surjective I (A0 C p) z
  rw [AdicCompletion.evalₐ_mk, Ideal.Quotient.factor_mk, AdicCompletion.evalₐ_mk]
  exact AdicCompletion.Ideal.mk_eq_mk I hmn s

private def mapACrisResidue (f : A0 C p →+* A0 C p) (k : ℕ) :
    ACris C p →+* (A0 C p) ⧸ I ^ k :=
  (mapQuotient C p f k).comp (AdicCompletion.evalₐ I k).toRingHom

private theorem mapACrisResidue_compatible (f : A0 C p →+* A0 C p) :
    ∀ {m n : ℕ} (hmn : m ≤ n),
      (Ideal.Quotient.factorPow I hmn).comp (mapACrisResidue C p f n) = mapACrisResidue C p f m := by
  intro m n hmn
  apply RingHom.ext
  intro z
  change Ideal.Quotient.factorPow I hmn (mapQuotient C p f n (AdicCompletion.evalₐ I n z)) =
    mapQuotient C p f m (AdicCompletion.evalₐ I m z)
  rw [factorPow_mapQuotient C p f hmn, factorPow_eval C p z hmn]

/-- An endomorphism of the integral divided-power subalgebra induces an
endomorphism of its p-adic completion by applying it to each residue. -/
def mapACris (f : A0 C p →+* A0 C p) : ACris C p →+* ACris C p :=
  AdicCompletion.liftRingHom I (mapACrisResidue C p f) (mapACrisResidue_compatible C p f)

theorem eval_mapACris_of_eq (f : A0 C p →+* A0 C p) (k : ℕ) (z : ACris C p) (x : A0 C p)
    (hx : AdicCompletion.evalₐ I k z = Ideal.Quotient.mk (I ^ k) x) :
    AdicCompletion.evalₐ I k (mapACris C p f z) = Ideal.Quotient.mk (I ^ k) (f x) := by
  calc
    _ = mapACrisResidue C p f k z :=
      AdicCompletion.evalₐ_liftRingHom I (mapACrisResidue C p f)
        (mapACrisResidue_compatible C p f) k z
    _ = mapQuotient C p f k (Ideal.Quotient.mk (I ^ k) x) :=
      congrArg (mapQuotient C p f k) hx
    _ = _ := mapQuotient_mk C p f k x

@[simp]
theorem mapACris_algebraMap (f : A0 C p →+* A0 C p) (x : A0 C p) :
    mapACris C p f (algebraMap (A0 C p) (ACris C p) x) =
      algebraMap (A0 C p) (ACris C p) (f x) := by
  apply AdicCompletion.ext_evalₐ
  intro n
  change AdicCompletion.evalₐ I n (mapACris C p f (AdicCompletion.of I (A0 C p) x)) =
    AdicCompletion.evalₐ I n (AdicCompletion.of I (A0 C p) (f x))
  exact (eval_mapACris_of_eq C p f n _ x (AdicCompletion.evalₐ_of I n x)).trans
    (AdicCompletion.evalₐ_of I n (f x)).symm

end

end JoshiTeich.Act1Scene1.CrystallineEnvelope
