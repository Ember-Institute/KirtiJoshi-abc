import Solutions.Source_ReferenceIutCor312CrystallineLogAdd
import Solutions.Source_ReferenceIutCor312CrystallinePadicScalars
import ArithmeticTeichmullerSpaces.Act1Scene1.LocalKummerTateBasis

set_option autoImplicit false

namespace JoshiTeich.Act1Scene1.LocalKummer

noncomputable section

/-- Apply the given field map to every coordinate of the original Tate tower. -/
def mapCyclotomicTateGroup {Ω C : Type*} [Field Ω] [Field C] (p : ℕ) (j : Ω →+* C) :
    cyclotomicTateGroup p Ω →* cyclotomicTateGroup p C where
  toFun ε := ⟨fun n => Units.map j.toMonoidHom (ε.1 n), by
    constructor
    · intro n
      rw [← map_pow, ε.2.1 n, map_one]
    · intro n
      rw [← map_pow, ε.2.2 n]⟩
  map_one' := Subtype.ext (funext fun _ => map_one (Units.map j.toMonoidHom))
  map_mul' ε δ := Subtype.ext (funext fun n => map_mul (Units.map j.toMonoidHom) (ε.1 n) (δ.1 n))

end

end JoshiTeich.Act1Scene1.LocalKummer

namespace JoshiTeich.Act1Scene1.CrystallineEnvelope

open JoshiTeich.Prologue LocalKummer

noncomputable section

variable (C : Type*) [NormedField C] [IsUltrametricDist C] [CompleteSpace C]
variable (p : ℕ) [Fact p.Prime] [Fact (0 < ‖(p : C)‖ ∧ ‖(p : C)‖ < 1)]

theorem cyclotomicLog_mul (ε δ : cyclotomicTateGroup p C) :
    cyclotomicLog C p (ε * δ) = cyclotomicLog C p ε + cyclotomicLog C p δ := by
  unfold cyclotomicLog
  apply logOfMemKerSupPrime_mul C p
  have h (z : Ainf C p) : 1 + (z - 1) = z :=
    (add_comm _ _).trans (sub_add_cancel _ _)
  simp only [h, map_mul]

/-- The logarithm is additive on the original multiplicative Tate group. -/
def cyclotomicLogHom : Additive (cyclotomicTateGroup p C) →+ ACris C p where
  toFun ε := cyclotomicLog C p ε.toMul
  map_zero' := by
    change cyclotomicLog C p 1 = 0
    have h := cyclotomicLog_mul C p 1 1
    rw [one_mul] at h
    exact add_left_cancel (h.symm.trans (add_zero _).symm)
  map_add' ε δ := cyclotomicLog_mul C p ε.toMul δ.toMul

variable {Ω : Type*} [Field Ω] [CharZero Ω] [IsAlgClosed Ω]

/-- The logarithm of the mapped tower is its original p-adic Tate coordinate
times the logarithm of the original basis tower. -/
theorem cyclotomicLog_mapTate_eq (j : Ω →+* C) (ε : cyclotomicTateGroup p Ω) :
    cyclotomicLog C p (mapCyclotomicTateGroup p j ε) =
      padicIntMapACris p C ((TateBasis.equiv (p := p) (Ω := Ω)).symm (Additive.ofMul ε)) *
        cyclotomicLog C p (mapCyclotomicTateGroup p j (TateBasis.generator (p := p) (Ω := Ω))) := by
  let e := TateBasis.equiv (p := p) (Ω := Ω)
  let t := cyclotomicLog C p (mapCyclotomicTateGroup p j (TateBasis.generator (p := p) (Ω := Ω)))
  let f := (cyclotomicLogHom C p).comp
    ((mapCyclotomicTateGroup p j).toAdditive.comp e.toLinearEquiv.toAddMonoidHom)
  let g := (AddMonoidHom.mulRight t).comp (padicIntMapACris p C).toAddMonoidHom
  have h1 : f 1 = g 1 := by
    change cyclotomicLog C p (mapCyclotomicTateGroup p j (e 1).toMul) =
      padicIntMapACris p C 1 * t
    simp only [e, TateBasis.equiv_apply, one_smul, map_one, one_mul, t]
    rfl
  have hfg := padicInt_addMonoidHom_ext_to_completion p f g h1
  let r := e.symm (Additive.ofMul ε)
  have he := DFunLike.congr_fun hfg r
  change cyclotomicLog C p (mapCyclotomicTateGroup p j (e r).toMul) =
    padicIntMapACris p C r * t at he
  rw [show e r = Additive.ofMul ε from e.apply_symm_apply _] at he
  exact he

end

end JoshiTeich.Act1Scene1.CrystallineEnvelope
