import ArithmeticTeichmullerSpaces.Act1Scene1.LocalKummerImageLogKernel

/-!
source-id: JT-SCENE1-PRINCIPAL-KUMMER-P-SATURATED-LOG
source: p-power division in rational Kummer cohomology, Joshi III (3212--3226).
fidelity: extends the ordinary image logarithm to the actual p-power saturation
inside standard rational H1. Clearing denominators proves independence of the
chosen power, additivity and injectivity. This subgroup is not identified with
H^1_e; no BK comparison, topology or Q_p scalar closure is supplied.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.LocalPadicLog
open scoped Valued
universe u v
noncomputable section
variable {k : Type u} [Field k] [Valued k (WithZero (Multiplicative ℤ))]
  [Valuation.RankOne (Valued.v : Valuation k (WithZero (Multiplicative ℤ)))]
variable [CharZero k] [CompleteSpace k]
variable {Ω : Type v} [Field Ω] [Algebra k Ω] [IsGalois k Ω] [Algebra.IsIntegral k Ω]
variable [CharZero Ω] [IsAlgClosed Ω] (p : ℕ) [Fact p.Prime]
local notation "H" => continuousCohomology 1 (LocalKummer.Rational.topRep (K := k) (Ω := Ω) p)
local notation "I" => principalKummerImage (k := k) (Ω := Ω) p

def saturatedKummerImage : AddSubgroup H where
  carrier := {x | ∃ n : ℕ, (p ^ n) • x ∈ I}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro x y ⟨n, hx⟩ ⟨m, hy⟩
    refine ⟨n + m, ?_⟩
    rw [smul_add]
    apply (principalKummerImage (k := k) (Ω := Ω) p).add_mem
    · rw [pow_add, mul_smul, smul_comm]
      exact (principalKummerImage (k := k) (Ω := Ω) p).nsmul_mem hx (p ^ m)
    · rw [pow_add, mul_smul]
      exact (principalKummerImage (k := k) (Ω := Ω) p).nsmul_mem hy (p ^ n)
  neg_mem' := by
    rintro x ⟨n, hx⟩
    exact ⟨n, by rw [smul_neg]; exact (principalKummerImage (k := k) (Ω := Ω) p).neg_mem hx⟩

variable (hpk : ‖(p : k)‖ < 1)

def saturatedLogGraph (x : H) (y : k) : Prop :=
  ∃ (n : ℕ) (a : I), (p ^ n) • x = (a : H) ∧
    (p ^ n) • y = principalImageLog p hpk a

private theorem graph_unique {x : H} {y z : k}
    (hy : saturatedLogGraph (Ω := Ω) p hpk (x : H) y) (hz : saturatedLogGraph (Ω := Ω) p hpk (x : H) z) : y = z := by
  obtain ⟨n, a, hxa, hya⟩ := hy
  obtain ⟨m, b, hxb, hzb⟩ := hz
  have hab : (p ^ m) • a = (p ^ n) • b := by
    apply Subtype.ext
    change (p ^ m) • (a : H) = (p ^ n) • (b : H)
    rw [← hxa, ← hxb, smul_comm]
  have hl := congrArg (principalImageLog (Ω := Ω) p hpk) hab
  rw [map_nsmul, map_nsmul, ← hya, ← hzb, ← mul_smul, ← mul_smul,
    mul_comm (p ^ n) (p ^ m)] at hl
  have hn : ((p ^ m * p ^ n : ℕ) : k) ≠ 0 :=
    Nat.cast_ne_zero.mpr (mul_ne_zero (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)
      (pow_ne_zero _ (Fact.out : p.Prime).ne_zero))
  exact mul_left_cancel₀ hn (by simpa only [nsmul_eq_mul] using hl)

private theorem graph_exists (x : saturatedKummerImage (k := k) (Ω := Ω) p) :
    ∃ y : k, saturatedLogGraph (Ω := Ω) p hpk (x : H) y := by
  obtain ⟨n, hn⟩ := x.2
  let a : I := ⟨(p ^ n) • (x : H), hn⟩
  refine ⟨principalImageLog p hpk a / (p ^ n : k), n, a, rfl, ?_⟩
  rw [nsmul_eq_mul, Nat.cast_pow]
  exact mul_div_cancel₀ _ (pow_ne_zero n
    (show (p : k) ≠ 0 from Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero))

private def logValue (x : saturatedKummerImage (k := k) (Ω := Ω) p) : k :=
  Classical.choose (graph_exists p hpk x)

private theorem logValue_spec (x : saturatedKummerImage (k := k) (Ω := Ω) p) :
    saturatedLogGraph (Ω := Ω) p hpk (x : H) (logValue p hpk x) :=
  Classical.choose_spec (graph_exists p hpk x)

private theorem graph_raise {x : H} {y : k} {n : ℕ} {a : I}
    (hx : (p ^ n) • x = (a : H)) (hy : (p ^ n) • y = principalImageLog p hpk a)
    (m : ℕ) :
    (p ^ (n + m)) • x = ((p ^ m) • a : I) ∧
      (p ^ (n + m)) • y = principalImageLog p hpk ((p ^ m) • a) := by
  constructor
  · change (p ^ (n + m)) • x = (p ^ m) • (a : H)
    rw [pow_add, mul_smul, smul_comm, hx]
  · rw [pow_add, mul_smul, smul_comm, hy, map_nsmul]

def saturatedImageLog : saturatedKummerImage (k := k) (Ω := Ω) p →+ k where
  toFun := logValue p hpk
  map_zero' := graph_unique p hpk (logValue_spec p hpk 0)
    ⟨0, 0, by simp, by simp⟩
  map_add' x y := by
    obtain ⟨n, a, hxa, hya⟩ := logValue_spec p hpk x
    obtain ⟨m, b, hxb, hzb⟩ := logValue_spec p hpk y
    have ha := graph_raise p hpk hxa hya m
    have hb := graph_raise p hpk hxb hzb n
    rw [Nat.add_comm m n] at hb
    apply graph_unique p hpk (logValue_spec p hpk (x + y))
    refine ⟨n + m, (p ^ m) • a + (p ^ n) • b, ?_, ?_⟩
    · change (p ^ (n + m)) • ((x : H) + (y : H)) = _
      rw [smul_add, ha.1, hb.1]
      rfl
    · rw [smul_add, ha.2, hb.2, map_add]

theorem saturatedImageLog_eq_of_graph
    (x : saturatedKummerImage (k := k) (Ω := Ω) p) (y : k)
    (h : saturatedLogGraph (Ω := Ω) p hpk (x : H) y) : saturatedImageLog p hpk x = y :=
  graph_unique p hpk (logValue_spec p hpk x) h

def saturatedClassOfImage (a : I) (n : ℕ) :
    saturatedKummerImage (k := k) (Ω := Ω) p :=
  ⟨((p : ℚ_[p]) ^ n)⁻¹ • (a : H), n, by
    rw [← Nat.cast_smul_eq_nsmul ℚ_[p], Nat.cast_pow, smul_smul,
      mul_inv_cancel₀ (pow_ne_zero n
        (show (p : ℚ_[p]) ≠ 0 from Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)),
      one_smul]
    exact a.2⟩

theorem saturatedImageLog_classOfImage (a : I) (n : ℕ) :
    saturatedImageLog p hpk (saturatedClassOfImage p a n) =
      ((p : k) ^ n)⁻¹ * principalImageLog p hpk a := by
  apply saturatedImageLog_eq_of_graph
  refine ⟨n, a, ?_, ?_⟩
  · change (p ^ n) • (((p : ℚ_[p]) ^ n)⁻¹ • (a : H)) = (a : H)
    rw [← Nat.cast_smul_eq_nsmul ℚ_[p], Nat.cast_pow, smul_smul,
      mul_inv_cancel₀ (pow_ne_zero n
        (show (p : ℚ_[p]) ≠ 0 from Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)),
      one_smul]
  · rw [nsmul_eq_mul, Nat.cast_pow, mul_inv_cancel_left₀]
    exact pow_ne_zero n (show (p : k) ≠ 0 from Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)

theorem saturatedImageLog_injective :
    Function.Injective (saturatedImageLog (k := k) (Ω := Ω) p hpk) := by
  suffices hz : ∀ x, saturatedImageLog (Ω := Ω) p hpk x = 0 → x = 0 by
    intro x y h
    have hd := hz (x - y) (by rw [map_sub, h, sub_self])
    exact sub_eq_zero.mp hd
  intro x hx
  obtain ⟨n, a, hxa, hya⟩ := logValue_spec p hpk x
  change (p ^ n) • saturatedImageLog p hpk x = principalImageLog p hpk a at hya
  rw [hx, smul_zero] at hya
  have ha : a = 0 := principalImageLog_injective p hpk (hya.symm.trans
    (map_zero (principalImageLog (Ω := Ω) p hpk)).symm)
  rw [ha] at hxa
  apply Subtype.ext
  change (x : H) = 0
  rw [← Nat.cast_smul_eq_nsmul ℚ_[p]] at hxa
  exact (smul_eq_zero.mp hxa).resolve_left
    (Nat.cast_ne_zero.mpr (pow_ne_zero n (Fact.out : p.Prime).ne_zero))

end
end JoshiTeich.Act1Scene1.LocalPadicLog
