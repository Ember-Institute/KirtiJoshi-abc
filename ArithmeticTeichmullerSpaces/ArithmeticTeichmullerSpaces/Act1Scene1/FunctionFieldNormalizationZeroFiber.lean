import ArithmeticTeichmullerSpaces.Act1Scene1.FunctionFieldNormalizationInertia
import ArithmeticTeichmullerSpaces.Act1Scene1.NormalizationPrimeValuation
import Mathlib.RingTheory.Ideal.GoingUp

/-!
source-id: JT-SCENE1-NORMALIZATION-ZERO-FIBER-20261107
source: IUT I Definition 3.1(d),(f); Joshi III `ss:theta-data-fixing2`;
the normalization chart over a transcendental coordinate.
fidelity: constructs the finite nonempty fiber above coordinate zero in the
actual integral closure. An inclusion of intermediate fields induces a
surjection of these fibers. The coordinate has valuation less than one there.
Original proofs; no reference implementation copied.
boundary: generic normalization algebra; no identification with torsion points,
a distinguished cusp, or a theta-root model is asserted.
-/

namespace JoshiTeich.Act1Scene1.FunctionFieldNormalization

open Polynomial IntermediateField
open scoped Classical IntermediateField.algebraAdjoinAdjoin
universe u
noncomputable section

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω]
variable (t : Ω) (ht : Transcendental k t)

/-- The coordinate as an element of its polynomial subalgebra. -/
def polynomialCoordinate : polynomialBase k t :=
  ⟨t, Algebra.subset_adjoin (Set.mem_singleton t)⟩

/-- Evaluation at zero in the transcendental polynomial subalgebra. -/
def zeroBaseEvaluation : polynomialBase k t →ₐ[k] k :=
  Algebra.adjoin.evalOfTranscendental t ht 0

theorem zeroBaseEvaluation_surjective : Function.Surjective (zeroBaseEvaluation t ht) := by
  intro a
  exact ⟨algebraMap k (polynomialBase k t) a, (zeroBaseEvaluation t ht).commutes a⟩

/-- The closed prime defined by coordinate zero. -/
def zeroBaseIdeal : Ideal (polynomialBase k t) :=
  RingHom.ker (zeroBaseEvaluation t ht).toRingHom

theorem zeroBaseIdeal_isMaximal : (zeroBaseIdeal t ht).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective _ (zeroBaseEvaluation_surjective t ht)

theorem zeroBaseIdeal_ne_bot : zeroBaseIdeal t ht ≠ ⊥ :=
  Ring.ne_bot_of_isMaximal_of_not_isField (zeroBaseIdeal_isMaximal t ht)
    (notFieldBase t ht)

theorem polynomialCoordinate_mem_zeroBaseIdeal :
    polynomialCoordinate t ∈ zeroBaseIdeal t ht := by
  change zeroBaseEvaluation t ht (polynomialCoordinate t) = 0
  have h := Algebra.adjoin.evalOfTranscendental_aeval (s := t) ht (0 : k)
    (p := (X : k[X]))
  simpa [polynomialCoordinate, zeroBaseEvaluation] using h

/-- The prime fiber above coordinate zero in the actual integral closure. -/
abbrev zeroFiber (L : IntermediateField (rationalBase k t) Ω) :=
  (zeroBaseIdeal t ht).primesOver (coordRing t L)

variable (L : IntermediateField (rationalBase k t) Ω)

private theorem zeroCoordRing_faithful :
    FaithfulSMul (polynomialBase k t) (coordRing t L) := by
  rw [faithfulSMul_iff_algebraMap_injective]
  intro a b hab
  exact Subtype.ext (congrArg (fun c : coordRing t L => ((c : L) : Ω)) hab)

theorem zeroFiber_nonempty : Nonempty (zeroFiber t ht L) := by
  have : (zeroBaseIdeal t ht).IsPrime := (zeroBaseIdeal_isMaximal t ht).isPrime
  have := zeroCoordRing_faithful t L
  exact Ideal.nonempty_primesOver (zeroBaseIdeal t ht)

variable [FiniteDimensional (rationalBase k t) L]
  [Algebra.IsSeparable (rationalBase k t) L]

theorem zeroFiber_finite : ((zeroBaseIdeal t ht).primesOver (coordRing t L)).Finite := by
  have := dedekindBase t ht
  have := dedekindRing t ht L
  have : (zeroBaseIdeal t ht).IsMaximal := zeroBaseIdeal_isMaximal t ht
  exact IsDedekindDomain.primesOver_finite (zeroBaseIdeal t ht) (coordRing t L)

/-- A zero-fiber prime is a nonzero Dedekind prime of the normalization. -/
def zeroFiberHeightOne (q : zeroFiber t ht L) :
    IsDedekindDomain.HeightOneSpectrum (coordRing t L) := by
  have := zeroCoordRing_faithful t L
  exact ⟨q.1, q.2.1, Ideal.ne_bot_of_mem_primesOver (zeroBaseIdeal_ne_bot t ht) q.2⟩

theorem zeroFiber_coordinate_valuation_lt_one (q : zeroFiber t ht L) :
    letI := dedekindRing t ht L
    letI := fractionFieldRing t L
    (NormalizationPrimeValuation.primeSubring L (zeroFiberHeightOne t ht L q)).valuation
      (algebraMap (coordRing t L) L
        (algebraMap (polynomialBase k t) (coordRing t L) (polynomialCoordinate t))) < 1 := by
  have := dedekindRing t ht L
  have := fractionFieldRing t L
  apply (NormalizationPrimeValuation.valuation_lt_one_iff_mem
    (K := L) (zeroFiberHeightOne t ht L q)
    (algebraMap (polynomialBase k t) (coordRing t L) (polynomialCoordinate t))).mpr
  change polynomialCoordinate t ∈ q.1.under (polynomialBase k t)
  rw [← q.2.2.over]
  exact polynomialCoordinate_mem_zeroBaseIdeal t ht

variable {t} {F N : IntermediateField (rationalBase k t) Ω}

/-- Restriction of primes along the actual inclusion of normalization rings. -/
def zeroFiberMap (hFN : F ≤ N) : zeroFiber t ht N → zeroFiber t ht F := fun q =>
  ⟨q.1.comap (ringMap hFN).toRingHom, Ideal.comap_isPrime _ _, ⟨by
    change zeroBaseIdeal t ht =
      (q.1.comap (ringMap hFN).toRingHom).comap
        (algebraMap (polynomialBase k t) (coordRing t F))
    rw [q.2.2.over]
    rfl⟩⟩

theorem zeroFiberMap_surjective (hFN : F ≤ N) :
    Function.Surjective (zeroFiberMap ht hFN) := by
  intro p
  have hpmax : p.1.IsMaximal := by
    have hint : (algebraMap (polynomialBase k t) (coordRing t F)).IsIntegral :=
      algebraMap_isIntegral_iff.mpr inferInstance
    apply Ideal.isMaximal_of_isIntegral_of_isMaximal_comap
      (algebraMap (polynomialBase k t) (coordRing t F)) hint p.1
    change (p.1.under (polynomialBase k t)).IsMaximal
    rw [← p.2.2.over]
    exact zeroBaseIdeal_isMaximal t ht
  obtain ⟨q, hqmax, hq⟩ := normalization_exists_maximal_over hFN p.1 hpmax
  refine ⟨⟨q, hqmax.isPrime, ⟨?_⟩⟩, ?_⟩
  · change zeroBaseIdeal t ht = q.comap (algebraMap (polynomialBase k t) (coordRing t N))
    rw [p.2.2.over, ← hq]
    rfl
  · exact Subtype.ext hq

end
end JoshiTeich.Act1Scene1.FunctionFieldNormalization
