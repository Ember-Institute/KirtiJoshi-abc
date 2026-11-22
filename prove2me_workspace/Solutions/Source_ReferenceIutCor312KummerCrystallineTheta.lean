import Solutions.Source_ReferenceIutCor312CrystallineThetaLog
import Solutions.Source_ReferenceIutCor312KummerCrystallineBridge

set_option autoImplicit false

namespace JoshiTeich.Act1Scene1.CrystallineEnvelope

open JoshiTeich.Prologue
open scoped Valued

noncomputable section

variable (C : Type*) [NormedField C] [IsUltrametricDist C] [CompleteSpace C] [CharZero C]
variable (p : ℕ) [Fact p.Prime] [Fact (0 < ‖(p : C)‖ ∧ ‖(p : C)‖ < 1)]

local notation "𝒪" => (LocalGeometricFontaine.integerRing C)
local notation "θ" => (Perfectoid.thetaMap (O := 𝒪) (p := p))

/-- The Fontaine image of the logarithm of the original Kummer tower is the
embedded ordinary logarithm of its principal unit. -/
theorem thetaCrystalline_kummerLogOfExists_eq_padicLog [IsAlgClosed C]
    {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω]
    [Valued k (WithZero (Multiplicative ℤ))]
    [Valuation.RankOne (Valued.v : Valuation k (WithZero (Multiplicative ℤ)))]
    [CharZero k] [CompleteSpace k] {u : k}
    (R : LocalKummer.RootTower (Ω := Ω) p u) (j : Ω →+* C)
    (hj : Continuous (j.comp (algebraMap k Ω)))
    (ha : ‖j (algebraMap k Ω u)‖ ≤ 1)
    (hu : ∃ r : 𝒪, j (algebraMap k Ω u) = 1 + (p : C) * (r : C))
    (hpk : ‖(p : k)‖ < 1) (hprincipal : ‖u - 1‖ < 1) :
    (thetaCrystalline C p (kummerLogOfExists C p R j ha hu) : C) =
      j (algebraMap k Ω (LocalPadicLog.padicLog u)) := by
  let x := teichmullerSubOne C p (R.toGeometricPreTilt j ha)
  have hx : x ∈ kerSupPrime C p :=
    kummerTeichmullerSubOne_mem_kerSupPrime C p R j ha hu
  have hθ : (j.comp (algebraMap k Ω)) u = 1 + (θ x : C) := by
    change j (algebraMap k Ω u) = _
    simp only [x, teichmullerSubOne, map_sub, map_one, AddSubgroupClass.coe_sub, Subring.coe_one]
    rw [R.theta_teichmuller_toGeometricPreTilt j ha, add_comm (1 : C), sub_add_cancel]
  exact thetaCrystalline_logOfMemKerSupPrime_eq_padicLog C p (j.comp (algebraMap k Ω))
    hj hpk hprincipal x hx hθ

end

end JoshiTeich.Act1Scene1.CrystallineEnvelope
