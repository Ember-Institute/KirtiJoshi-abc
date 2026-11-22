import Solutions.Source_ReferenceIutCor312CrystallineEnvelope

set_option autoImplicit false

namespace JoshiTeich.Act1Scene1.CrystallineEnvelope

open JoshiTeich.Prologue

noncomputable section

variable {C C' : Type*} [NormedField C] [IsUltrametricDist C]
variable [NormedField C'] [IsUltrametricDist C']
variable (p : ℕ) [Fact p.Prime]
variable [Fact (0 < ‖(p : C)‖ ∧ ‖(p : C)‖ < 1)]
variable [Fact (0 < ‖(p : C')‖ ∧ ‖(p : C')‖ < 1)]

local notation "ι" => algebraMap (Ainf C p) (AinfInvertP C p)
local notation "ι'" => algebraMap (Ainf C' p) (AinfInvertP C' p)

theorem map_gamma_of_algebraMap (w : Ainf C p →+* Ainf C' p)
    (l : AinfInvertP C p →+* AinfInvertP C' p)
    (hmap : ∀ x, l (ι x) = ι' (w x)) (n : ℕ) (x : Ainf C p) :
    l (gamma C p n x) = gamma C' p n (w x) := by
  apply (natCast_isUnit C' p n.factorial n.factorial_ne_zero).mul_left_cancel
  calc
    (n.factorial : AinfInvertP C' p) * l (gamma C p n x) =
        l ((n.factorial : AinfInvertP C p) * gamma C p n x) := by
      rw [map_mul, map_natCast]
    _ = l ((ι x) ^ n) := congrArg l (factorial_mul_gamma C p n x)
    _ = (ι' (w x)) ^ n := by rw [map_pow, hmap]
    _ = _ := (factorial_mul_gamma C' p n (w x)).symm

variable [CompleteSpace C] [CompleteSpace C']

local notation "θ" =>
  (Perfectoid.thetaMap (O := LocalGeometricFontaine.integerRing C) (p := p))
local notation "θ'" =>
  (Perfectoid.thetaMap (O := LocalGeometricFontaine.integerRing C') (p := p))

/-- A map of the localized Witt rings sends the integral divided-power
subalgebra into its counterpart when the inducing Witt map preserves the
Fontaine kernel. -/
theorem map_mem_A0_of_algebraMap (w : Ainf C p →+* Ainf C' p)
    (l : AinfInvertP C p →+* AinfInvertP C' p)
    (hmap : ∀ x, l (ι x) = ι' (w x))
    (hker : ∀ x ∈ RingHom.ker θ, w x ∈ RingHom.ker θ')
    (x : AinfInvertP C p) (hx : x ∈ A0 C p) :
    l x ∈ A0 C' p := by
  let generators : Set (AinfInvertP C p) :=
    {y | ∃ n : ℕ, ∃ z ∈ RingHom.ker θ, gamma C p n z = y}
  have hx' : x ∈ Algebra.adjoin (Ainf C p) generators := hx
  refine Algebra.adjoin_induction (R := Ainf C p) (A := AinfInvertP C p)
    (s := generators) (p := fun y _ => l y ∈ A0 C' p) ?_ ?_ ?_ ?_ hx'
  · rintro _ ⟨n, z, hz, rfl⟩
    rw [map_gamma_of_algebraMap p w l hmap]
    exact gamma_mem_A0 C' p n (hker z hz)
  · intro z
    rw [hmap]
    exact (A0 C' p).algebraMap_mem (w z)
  · intro a b _ _ ha hb
    rw [map_add]
    exact (A0 C' p).add_mem ha hb
  · intro a b _ _ ha hb
    rw [map_mul]
    exact (A0 C' p).mul_mem ha hb

end

end JoshiTeich.Act1Scene1.CrystallineEnvelope
