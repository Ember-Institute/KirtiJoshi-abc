import Solutions.Source_ReferenceIutCor312CrystallineThetaJetBounds
import Solutions.Source_ReferenceIutCor312CrystallineInvertP
import Solutions.Source_ReferenceIutCor312CyclotomicSurvival
import Mathlib.Algebra.Ring.GeomSum

set_option autoImplicit false

namespace JoshiTeich.Act1Scene1.CrystallineEnvelope

open JoshiTeich.Prologue

noncomputable section

private theorem prime_pow_dvd_of_completion_pow_eq_zero
    {R : Type*} [CommRing R] (p k r m : ℕ)
    (z : AdicCompletion (Ideal.span {(p : R)}) R) (a : R)
    (ha : AdicCompletion.evalₐ (Ideal.span {(p : R)}) k z =
      Ideal.Quotient.mk ((Ideal.span {(p : R)}) ^ k) a)
    (hz : (p : AdicCompletion (Ideal.span {(p : R)}) R) ^ r * z ^ m = 0) :
    (p : R) ^ k ∣ (p : R) ^ r * a ^ m := by
  let I : Ideal R := Ideal.span {(p : R)}
  let reduce := Ideal.Quotient.mk (I ^ k)
  let eval := (AdicCompletion.evalₐ I k).toRingHom
  have heval : eval z = reduce a := ha
  have hzero := congrArg eval hz
  rw [map_mul eval, map_pow eval, map_pow eval, map_natCast eval, heval, map_zero eval] at hzero
  have hreduce : reduce ((p : R) ^ r * a ^ m) = 0 := by
    rw [map_mul reduce, map_pow reduce, map_pow reduce, map_natCast reduce]
    exact hzero
  have hmem : (p : R) ^ r * a ^ m ∈ I ^ k := Ideal.Quotient.eq_zero_iff_mem.mp hreduce
  rw [Ideal.span_singleton_pow] at hmem
  exact Ideal.mem_span_singleton.mp hmem

variable (C : Type*) [NormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C]
variable (p : ℕ) [Fact p.Prime] [Fact (0 < ‖(p : C)‖ ∧ ‖(p : C)‖ < 1)]

local notation "𝒪" => LocalGeometricFontaine.integerRing C
local notation "A" => Ainf C p
local notation "B" => AinfInvertP C p
local notation "ι" => algebraMap A B
local notation "θ" => (Perfectoid.thetaMap (O := 𝒪) (p := p))
local notation "ξ" => fontainePrimitive C p
local notation "J" => thetaJetIdeal C p
local notation "q" => fun m : ℕ => Ideal.Quotient.mk (J m)
local notation "𝔦" => (Ideal.span {(p : A0 C p)} : Ideal (A0 C p))

private theorem image_primitive_ne_zero : ι ξ ≠ 0 := by
  intro h
  exact fontainePrimitive_ne_zero C p
    (algebraMap_injective C p (h.trans (map_zero ι).symm))

private theorem thetaAway_primitive : thetaAway C p (ι ξ) = 0 := by
  rw [thetaAway_algebraMap, RingHom.mem_ker.mp (fontainePrimitive_mem_ker C p), Subring.coe_zero]

private theorem primitive_pow_dvd_of_away_dvd (m : ℕ) (x : A)
    (hx : (ι ξ) ^ m ∣ ι x) : ξ ^ m ∣ x := by
  induction m generalizing x with
  | zero => simp only [pow_zero, one_dvd]
  | succ m ih =>
    have hz := map_dvd (thetaAway C p) hx
    rw [map_pow, thetaAway_primitive, zero_pow (Nat.succ_ne_zero m), zero_dvd_iff,
      thetaAway_algebraMap] at hz
    have hxker : x ∈ RingHom.ker θ :=
      RingHom.mem_ker.mpr (Subtype.ext hz)
    rw [fontaineKernel_eq_span C p, Ideal.mem_span_singleton] at hxker
    obtain ⟨y, hy⟩ := hxker
    have hdiv : (ι ξ) ^ m ∣ ι y := by
      apply (mul_dvd_mul_iff_left (image_primitive_ne_zero C p)).mp
      simpa only [pow_succ', hy, map_mul] using hx
    obtain ⟨z, hz⟩ := ih y hdiv
    exact ⟨z, by rw [hy, hz, pow_succ', mul_assoc]⟩

private theorem thetaJet_logPartialSum_pow
    (m : ℕ) (x : A) (hx : x ∈ RingHom.ker θ) (b : A) (hxb : x = ξ * b)
    {N : ℕ} (hN : 0 < N) :
    q m (((DividedPowerLog.logPartialSum
      (fun n => gammaInOfMemKerSupPrime C p n x (Ideal.mem_sup_left hx)) N : A0 C p) : B) ^ m) =
      q m (ι (x ^ m)) := by
  let a := (DividedPowerLog.logPartialSum
    (fun n => gammaInOfMemKerSupPrime C p n x (Ideal.mem_sup_left hx)) N : A0 C p)
  change q m ((a : B) ^ m) = q m (ι (x ^ m))
  obtain ⟨c, hc⟩ := logPartialSum_sub_algebraMap_dvd_primitive_sq C p x hx hN
  have ha : (a : B) = ι ξ * (ι b + ι ξ * c) := by
    calc
      _ = ι x + (ι ξ) ^ 2 * c := (sub_eq_iff_eq_add.mp hc).trans (add_comm _ _)
      _ = _ := by rw [hxb, map_mul, mul_add, pow_two, mul_assoc]
  have hd := sub_dvd_pow_sub_pow (ι b + ι ξ * c) (ι b) m
  rw [add_sub_cancel_left] at hd
  obtain ⟨d, hd⟩ := hd
  have hmem : (a : B) ^ m - ι (x ^ m) ∈ J m := by
    apply Ideal.mem_span_singleton.mpr
    refine ⟨c * d, ?_⟩
    rw [ha, hxb, map_pow, map_mul ι, mul_pow, mul_pow, ← mul_sub, hd, pow_succ]
    ac_rfl
  apply sub_eq_zero.mp
  rw [← map_sub]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr hmem

private theorem thetaJet_dvd_of_equal
    (m : ℕ) (x b y : A) (hxb : x = ξ * b) (r k : ℕ)
    (h : q m (ι ((m.factorial : A) ^ m * (p : A) ^ r * x ^ m)) =
      q m (ι ((p : A) ^ k * y))) :
    (p : 𝒪) ^ k ∣ (m.factorial : 𝒪) ^ m * (p : 𝒪) ^ r * θ b ^ m := by
  let u := ι ((m.factorial : A) ^ m * (p : A) ^ r * x ^ m)
  let v := ι ((p : A) ^ k * y)
  have hm : u - v ∈ J m := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_sub]
    exact sub_eq_zero.mpr h
  obtain ⟨s, hs⟩ := Ideal.mem_span_singleton.mp hm
  have hu : (ι ξ) ^ m ∣ u := by
    dsimp only [u]
    simp only [hxb, map_mul, map_pow, map_natCast, mul_pow]
    exact (dvd_mul_right _ _).mul_left _
  have hv : (ι ξ) ^ m ∣ v := by
    have hsub : (ι ξ) ^ m ∣ u - v := by
      rw [hs, pow_succ, mul_assoc]
      exact dvd_mul_right _ _
    have hd := dvd_sub hu hsub
    simpa only [sub_sub_cancel] using hd
  have hy : (ι ξ) ^ m ∣ ι y := by
    have hp := natCast_isUnit C p p (Fact.out : p.Prime).ne_zero
    apply (IsUnit.dvd_mul_left (hp.pow k)).mp
    simpa only [v, map_mul, map_pow, map_natCast] using hv
  obtain ⟨c, hc⟩ := primitive_pow_dvd_of_away_dvd C p m y hy
  have hfactor :
      (ι ξ) ^ m * ((m.factorial : B) ^ m * (p : B) ^ r * (ι b) ^ m - (p : B) ^ k * ι c) =
        (ι ξ) ^ m * (ι ξ * s) := by
    calc
      _ = u - v := by
        simp only [u, v, hxb, hc, map_mul, map_pow, map_natCast, mul_pow, mul_sub]
        congr 1 <;> ac_rfl
      _ = _ := by rw [hs, pow_succ, mul_assoc]
  have h := congrArg (thetaAway C p)
    (mul_left_cancel₀ (pow_ne_zero m (image_primitive_ne_zero C p)) hfactor)
  have hrhs : thetaAway C p (ι ξ * s) = 0 := by
    rw [map_mul, thetaAway_primitive, zero_mul]
  change thetaAway C p
    ((m.factorial : B) ^ m * (p : B) ^ r * (ι b) ^ m - (p : B) ^ k * ι c) = thetaAway C p (ι ξ * s) at h
  rw [hrhs] at h
  simp only [map_mul, map_sub, map_pow, map_natCast, thetaAway_algebraMap] at h
  refine ⟨θ c, Subtype.ext ?_⟩
  simpa only [Subring.coe_mul, Subring.coe_pow, Subring.coe_natCast] using sub_eq_zero.mp h

variable [CharZero C]

/-- Every power of the original logarithm survives after inverting the prime
when its first Fontaine coordinate is nonzero. -/
theorem logOfMemKer_pow_survives_of_firstOrder
    (x : A) (hx : x ∈ RingHom.ker θ) (b : A) (hxb : x = ξ * b) (hb : θ b ≠ 0)
    (m : ℕ) :
    (algebraMap (ACris C p) (ACrisInvertP C p)
      (logOfMemKerSupPrime C p x (Ideal.mem_sup_left hx))) ^ m ≠ 0 := by
  let z := logOfMemKerSupPrime C p x (Ideal.mem_sup_left hx)
  let i := algebraMap (ACris C p) (ACrisInvertP C p)
  intro hz
  have hzero : i (z ^ m) = 0 := (map_pow i z m).trans hz
  obtain ⟨⟨_, ⟨r, rfl⟩⟩, hr⟩ :=
    (IsLocalization.map_eq_zero_iff (Submonoid.powers (p : ACris C p))
      (ACrisInvertP C p) (z ^ m)).mp hzero
  change (p : ACris C p) ^ r * z ^ m = 0 at hr
  have hdiv (k : ℕ) :
      (p : 𝒪) ^ k ∣ (m.factorial : 𝒪) ^ m * (p : 𝒪) ^ r * θ b ^ m := by
    let N := p * k + 1
    let a := DividedPowerLog.logPartialSum
      (fun n => gammaInOfMemKerSupPrime C p n x (Ideal.mem_sup_left hx)) N
    have ha : AdicCompletion.evalₐ 𝔦 k z = Ideal.Quotient.mk (𝔦 ^ k) a :=
      eval_logOfMemKerSupPrime C p x (Ideal.mem_sup_left hx) (Nat.le_succ (p * k))
    obtain ⟨t, ht⟩ := prime_pow_dvd_of_completion_pow_eq_zero p k r m z a ha hr
    let val : A0 C p →+* B := (A0 C p).val.toRingHom
    have htB : (p : B) ^ r * (a : B) ^ m = (p : B) ^ k * (t : B) := by
      have hh := congrArg val ht
      rw [map_mul val, map_pow val, map_pow val, map_natCast val,
        map_mul val, map_pow val, map_natCast val] at hh
      exact hh
    obtain ⟨y, hy⟩ := thetaJet_exists_scaled_ainf C p m t
    have hq : q m ((a : B) ^ m) = q m (ι (x ^ m)) :=
      thetaJet_logPartialSum_pow C p m x hx b hxb (Nat.succ_pos (p * k))
    apply thetaJet_dvd_of_equal C p m x b y hxb r k
    calc
      _ = q m ((m.factorial : B) ^ m * ((p : B) ^ r * (a : B) ^ m)) := by
        simpa only [map_mul, map_pow, map_natCast, mul_assoc] using
          congrArg (fun v : B ⧸ J m =>
            (m.factorial : B ⧸ J m) ^ m * ((p : B ⧸ J m) ^ r * v)) hq.symm
      _ = q m ((p : B) ^ k * ((m.factorial : B) ^ m * (t : B))) := by
        rw [htB]
        congr 1
        ac_rfl
      _ = _ := by
        rw [map_mul (q m), hy]
        simp only [map_mul, map_pow, map_natCast]
  have hout : (m.factorial : 𝒪) ^ m * (p : 𝒪) ^ r * θ b ^ m = 0 := by
    apply IsHausdorff.haus (inferInstance : IsHausdorff (Ideal.span {(p : 𝒪)}) 𝒪)
    intro k
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow]
    exact Ideal.mem_span_singleton.mpr (hdiv k)
  exact (mul_ne_zero (mul_ne_zero
    (pow_ne_zero m (Nat.cast_ne_zero.mpr m.factorial_ne_zero))
    (pow_ne_zero r (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero))) (pow_ne_zero m hb)) hout

/-- Every power of the crystalline logarithm of the original Tate-basis generator
survives in `A_cris[1/p]`. -/
theorem cyclotomicLog_tateBasisGenerator_pow_survives (m : ℕ) :
    (algebraMap (ACris C p) (ACrisInvertP C p)
      (cyclotomicLog C p (LocalKummer.TateBasis.generator (p := p) (Ω := C)))) ^ m ≠ 0 := by
  obtain ⟨b, hb, hxb⟩ := tateBasisGenerator_exists_firstOrder C p
  exact logOfMemKer_pow_survives_of_firstOrder C p _
    (LocalKummer.RootTower.cyclotomic_teichmuller_sub_one_mem_theta_ker _) b hxb hb m

end

end JoshiTeich.Act1Scene1.CrystallineEnvelope
