import ArithmeticTeichmullerSpaces.Act1Scene1.Boundary

namespace JoshiTeich.Act1Scene2

open JoshiTeich.Act1Scene1

universe uK

/-!
Scene2 starts after Scene1 and receives each post-3.12 bridge as an explicit
proposition.  The proposition parameters are placeholders for later sourced
interfaces; this file proves none of them and defines no `abc` result.
-/
structure Scene2Input
    {K : Type uK} [Field K] [NumberField K]
    {O : Type uK} [CommRing O] (p : ℕ)
    [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
    [IsAdicComplete (Ideal.span {(p : O)}) O]
    (scene1 : Scene1Input K O p)
    (corollary312 theta_log_volume_upper_bound main_bound vojta strong_abc
      classical_abc : Prop) where
  scene1_input : Scene1Input K O p
  corollary312 : corollary312
  theta_log_volume_upper_bound : theta_log_volume_upper_bound
  main_bound : main_bound
  vojta : vojta
  strong_abc : strong_abc
  classical_abc : classical_abc

end JoshiTeich.Act1Scene2
