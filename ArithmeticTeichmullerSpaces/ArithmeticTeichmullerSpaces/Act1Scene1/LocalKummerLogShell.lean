import ArithmeticTeichmullerSpaces.Act1Scene1.LocalKummerSaturatedTopology

/-!
source-id: JT-SCENE1-KUMMER-LOG-SHELL
source: Joshi III 2843--2853 and 3212--3236, the existing ordinary
log-shell and the original saturated Kummer logarithm.
fidelity: the ordinary log-shell is a Z_p submodule. Its inverse under
the original saturated log consists exactly of (2p)^(-1) times actual
principal-unit Kummer classes. This is not an integral-H1 or BK identity.
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
variable (hpk : ‖(p : k)‖ < 1)
variable [Algebra ℚ_[p] k] [ContinuousSMul ℚ_[p] k]
local notation "S" => saturatedKummerPadicSubmodule (k := k) (Ω := Ω) p hpk

local instance shellIntegralModule : Module ℤ_[p] k :=
  Module.compHom k (algebraMap ℤ_[p] ℚ_[p])
local instance shellCohomologyIntegralModule : Module ℤ_[p] S :=
  Module.compHom S (algebraMap ℤ_[p] ℚ_[p])

include hpk in
theorem logShell_padicInt_smul (r : ℤ_[p]) {y : k} (hy : y ∈ logShell p) :
    (r : ℚ_[p]) • y ∈ logShell p := by
  obtain ⟨a, ha, rfl⟩ := hy
  let u : principalUnits (k := k) :=
    ⟨Units.mk0 a (ne_zero_of_norm_sub_one_lt ha), ha⟩
  refine ⟨(principalPadicPower hpk u r : kˣ), (principalPadicPower hpk u r).2, ?_⟩
  rw [padicLog_principalPadicPower hpk u r]
  simp only [Algebra.smul_def]
  exact mul_left_comm _ _ _

/-- The carrier is exactly the existing ordinary log-shell. -/
def logShellIntegralSubmodule : Submodule ℤ_[p] k where
  carrier := logShell p
  zero_mem' := ⟨1, by simp, by simp [padicLog_one]⟩
  add_mem' := by
    rintro x y ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨a * b, norm_mul_sub_one_lt ha hb, by
      rw [padicLog_mul (Fact.out : p.Prime) hpk ha hb, mul_add]⟩
  smul_mem' := logShell_padicInt_smul p hpk

/-- The original saturated class of an actual principal unit. -/
def principalSaturatedClass (a : Additive (principalUnits (k := k))) : S :=
  ⟨principalKummerHom (Ω := Ω) p a, 0, by
    simpa using (show principalKummerHom (Ω := Ω) p a ∈ principalKummerImage p from ⟨a, rfl⟩)⟩

theorem saturatedPadicLog_principalSaturatedClass (a : Additive (principalUnits (k := k))) :
    saturatedPadicLog p hpk (principalSaturatedClass (Ω := Ω) p hpk a) =
      padicLog (a.toMul.1 : k) := by
  apply saturatedImageLog_eq_of_graph
  refine ⟨0, (principalKummerHom (Ω := Ω) p).rangeRestrict a, by simp [principalSaturatedClass], ?_⟩
  simpa using (principalImageLog_class (Ω := Ω) p hpk a).symm

def normalizedPrincipalSaturatedClass (a : Additive (principalUnits (k := k))) : S :=
  (2 * (p : ℚ_[p]))⁻¹ • principalSaturatedClass (Ω := Ω) p hpk a

theorem saturatedPadicLog_normalizedPrincipalClass (a : Additive (principalUnits (k := k))) :
    saturatedPadicLog p hpk (normalizedPrincipalSaturatedClass (Ω := Ω) p hpk a) =
      (2 * (p : k))⁻¹ * padicLog (a.toMul.1 : k) := by
  change saturatedPadicLog p hpk ((2 * (p : ℚ_[p]))⁻¹ • _) = _
  rw [map_smul, saturatedPadicLog_principalSaturatedClass]
  simp only [Algebra.smul_def, map_inv₀, map_mul, map_ofNat, map_natCast]

/-- The shell in original saturated H1 coordinates, with the original Z_p action. -/
def normalizedKummerShell : Submodule ℤ_[p] S where
  carrier := {x | saturatedPadicLog p hpk x ∈ logShell p}
  zero_mem' := by
    change saturatedPadicLog p hpk 0 ∈ logShell p
    rw [map_zero]
    exact (logShellIntegralSubmodule p hpk).zero_mem
  add_mem' := by
    intro x y hx hy
    change saturatedPadicLog p hpk (x + y) ∈ logShell p
    rw [map_add]
    exact (logShellIntegralSubmodule p hpk).add_mem hx hy
  smul_mem' := by
    intro r x hx
    change saturatedPadicLog p hpk ((r : ℚ_[p]) • x) ∈ logShell p
    rw [map_smul]
    exact logShell_padicInt_smul p hpk r hx

theorem mem_normalizedKummerShell_iff (x : S) :
    x ∈ normalizedKummerShell (Ω := Ω) p hpk ↔
      ∃ a : Additive (principalUnits (k := k)),
        normalizedPrincipalSaturatedClass (Ω := Ω) p hpk a = x := by
  constructor
  · rintro ⟨a, ha, hlog⟩
    let u : principalUnits (k := k) :=
      ⟨Units.mk0 a (ne_zero_of_norm_sub_one_lt ha), ha⟩
    refine ⟨Additive.ofMul u, (saturatedPadicLogEquiv p hpk).injective ?_⟩
    exact (saturatedPadicLog_normalizedPrincipalClass (Ω := Ω) p hpk _).trans hlog.symm
  · rintro ⟨a, rfl⟩
    change saturatedPadicLog p hpk _ ∈ logShell p
    rw [saturatedPadicLog_normalizedPrincipalClass]
    exact ⟨a.toMul.1, a.toMul.2, rfl⟩

variable [FiniteDimensional ℚ_[p] k]

/-- The restriction retains the original subspace topologies on both shells. -/
def normalizedKummerShellLogEquiv :
    normalizedKummerShell (Ω := Ω) p hpk ≃L[ℤ_[p]] logShellIntegralSubmodule p hpk where
  toFun x := ⟨saturatedPadicLog p hpk x.1, x.2⟩
  invFun y := ⟨(saturatedPadicLogContinuousEquiv (Ω := Ω) p hpk).symm y.1, by
    change saturatedPadicLog p hpk _ ∈ logShell p
    simpa only [show (saturatedPadicLog p hpk : S → k) =
      saturatedPadicLogContinuousEquiv p hpk from rfl,
      ContinuousLinearEquiv.apply_symm_apply] using (show (y : k) ∈ logShell p from y.2)⟩
  left_inv x := Subtype.ext ((saturatedPadicLogContinuousEquiv p hpk).symm_apply_apply x.1)
  right_inv y := Subtype.ext ((saturatedPadicLogContinuousEquiv p hpk).apply_symm_apply y.1)
  map_add' x y := Subtype.ext (map_add (saturatedPadicLog p hpk) x.1 y.1)
  map_smul' r x := Subtype.ext (map_smul (saturatedPadicLog p hpk) (r : ℚ_[p]) x.1)
  continuous_toFun := continuous_induced_rng.mpr
    ((saturatedPadicLog_continuous (Ω := Ω) p hpk).comp continuous_subtype_val)
  continuous_invFun := continuous_induced_rng.mpr
    ((saturatedPadicLogContinuousEquiv (Ω := Ω) p hpk).symm.continuous.comp continuous_subtype_val)

end
end JoshiTeich.Act1Scene1.LocalPadicLog
