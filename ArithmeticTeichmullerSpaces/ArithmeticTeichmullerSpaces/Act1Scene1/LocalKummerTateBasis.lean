import ArithmeticTeichmullerSpaces.Act1Scene1.LocalKummerPrimitiveTower
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.Topology.Homeomorph.Lemmas

/-!
source-id: JT-SCENE1-LOCAL-KUMMER-TATE-BASIS
source: Z_p(1) as a topological rank-one Z_p module, Joshi III (3190--3208).
fidelity: constructs the unique p-adic exponent of every compatible root
sequence. Scalar multiplication by a primitive compatible sequence is a
continuous linear equivalence from Z_p to the actual Tate inverse limit.
boundary: Scene1/Derived
-/

namespace JoshiTeich.Act1Scene1.LocalKummer.TateBasis
open scoped Topology
universe v
noncomputable section
variable {p : ℕ} [Fact p.Prime] {Ω : Type v} [Field Ω] [CharZero Ω] [IsAlgClosed Ω]

local instance levelModNeZero (n : ℕ) : NeZero (p ^ n) :=
  ⟨(pow_pos (Fact.out : p.Prime).pos n).ne'⟩

def levelExponent (x : cyclotomicTateGroup p Ω) (n : ℕ) : ℕ :=
  Classical.choose ((generator_isPrimitive (p := p) (Ω := Ω) n).eq_pow_of_mem_rootsOfUnity
    ((mem_rootsOfUnity _ _).mpr (x.2.1 n)))

theorem levelExponent_spec (x : cyclotomicTateGroup p Ω) (n : ℕ) :
    levelExponent x n < p ^ n ∧
      (generator (p := p) (Ω := Ω)).1 n ^ levelExponent x n = x.1 n :=
  Classical.choose_spec ((generator_isPrimitive (p := p) (Ω := Ω) n).eq_pow_of_mem_rootsOfUnity
    ((mem_rootsOfUnity _ _).mpr (x.2.1 n)))

theorem levelExponent_compatible (x : cyclotomicTateGroup p Ω) (n : ℕ) :
    levelExponent x (n + 1) ≡ levelExponent x n [MOD p ^ n] := by
  have he : (generator (p := p) (Ω := Ω)).1 n ^ levelExponent x (n + 1) =
      (generator (p := p) (Ω := Ω)).1 n ^ levelExponent x n := by
    rw [(levelExponent_spec x n).2]
    rw [← (generator (p := p) (Ω := Ω)).2.2 n, ← pow_mul, Nat.mul_comm, pow_mul,
      (levelExponent_spec x (n + 1)).2, x.2.2 n]
  have hm := pow_eq_pow_iff_modEq.mp he
  rwa [← (generator_isPrimitive (p := p) (Ω := Ω) n).eq_orderOf] at hm

private theorem exponent_dvd (x : cyclotomicTateGroup p Ω) (n : ℕ) :
    (p : ℤ) ^ n ∣ (levelExponent x (n + 1) : ℤ) - levelExponent x n := by
  rw [← Int.natCast_pow, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
  simp only [Int.cast_sub, Int.cast_natCast, sub_eq_zero]
  exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr (levelExponent_compatible x n)

def exponent (x : cyclotomicTateGroup p Ω) : ℤ_[p] :=
  PadicInt.ofIntSeq (fun n => (levelExponent x n : ℤ))
    (PadicInt.isCauSeq_padicNorm_of_pow_dvd_sub _ p (exponent_dvd x))

theorem exponent_toZModPow (x : cyclotomicTateGroup p Ω) (n : ℕ) :
    PadicInt.toZModPow n (exponent x) = (levelExponent x n : ZMod (p ^ n)) := by
  simpa only [exponent, Int.cast_natCast] using
    PadicInt.toZModPow_ofIntSeq_of_pow_dvd_sub (fun i => (levelExponent x i : ℤ))
      p (exponent_dvd x) n

theorem padicPower_exponent (x : cyclotomicTateGroup p Ω) :
    padicPower (exponent x) (generator (p := p) (Ω := Ω)) = x := by
  apply Subtype.ext
  funext n
  rw [padicPower_apply, exponent_toZModPow, ZMod.val_natCast,
    Nat.mod_eq_of_lt (levelExponent_spec x n).1, (levelExponent_spec x n).2]

theorem padicPower_generator_injective :
    Function.Injective (fun r : ℤ_[p] => padicPower r (generator (p := p) (Ω := Ω))) := by
  intro r s hrs
  apply PadicInt.ext_of_toZModPow.mp
  intro n
  apply ZMod.val_injective
  apply (generator_isPrimitive (p := p) (Ω := Ω) n).pow_inj
    (ZMod.val_lt _) (ZMod.val_lt _)
  exact congrArg (fun x : cyclotomicTateGroup p Ω => x.1 n) hrs

def scalarMap : ℤ_[p] →ₗ[ℤ_[p]] Additive (cyclotomicTateGroup p Ω) :=
  LinearMap.toSpanSingleton ℤ_[p] _ (Additive.ofMul (generator (p := p) (Ω := Ω)))

theorem scalarMap_bijective : Function.Bijective (scalarMap (p := p) (Ω := Ω)) := by
  constructor
  · intro r s hrs
    apply padicPower_generator_injective (p := p) (Ω := Ω)
    exact congrArg Additive.toMul hrs
  · intro x
    exact ⟨exponent x.toMul, congrArg Additive.ofMul (padicPower_exponent x.toMul)⟩

def linearEquiv : ℤ_[p] ≃ₗ[ℤ_[p]] Additive (cyclotomicTateGroup p Ω) :=
  LinearEquiv.ofBijective scalarMap scalarMap_bijective

theorem continuous_scalarMap : Continuous (scalarMap (p := p) (Ω := Ω)) := by
  exact continuous_smul.comp
    (show Continuous (fun r : ℤ_[p] => (r, Additive.ofMul (generator (p := p) (Ω := Ω)))) from
      continuous_id.prodMk continuous_const)

local instance levelUnitsTopology : TopologicalSpace Ωˣ := ⊥
local instance levelUnitsDiscrete : DiscreteTopology Ωˣ := ⟨rfl⟩

instance tateT2Space : T2Space (cyclotomicTateGroup p Ω) :=
  (Topology.IsEmbedding.induced
    (Subtype.val_injective : Function.Injective (fun x : cyclotomicTateGroup p Ω => x.1))).t2Space

instance tateAdditiveT2Space : T2Space (Additive (cyclotomicTateGroup p Ω)) :=
  T2Space.of_injective_continuous
    (f := fun x : Additive (cyclotomicTateGroup p Ω) => x.toMul)
    (fun _ _ h => congrArg Additive.ofMul h) continuous_toMul

def equiv : ℤ_[p] ≃L[ℤ_[p]] Additive (cyclotomicTateGroup p Ω) :=
  ContinuousLinearEquiv.ofIsHomeomorph linearEquiv
    (isHomeomorph_iff_continuous_bijective.mpr ⟨continuous_scalarMap, linearEquiv.bijective⟩)

theorem equiv_apply (r : ℤ_[p]) :
    equiv (p := p) (Ω := Ω) r = r • Additive.ofMul (generator (p := p) (Ω := Ω)) := rfl

end
end JoshiTeich.Act1Scene1.LocalKummer.TateBasis
