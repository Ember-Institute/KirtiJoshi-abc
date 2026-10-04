import ArithmeticTeichmullerSpaces.Prologue.Interfaces

namespace JoshiTeich.Act1Scene1

open JoshiTeich.Prologue

universe uK

/-!
Scene1 receives all Prologue obligations as explicit fields.  This boundary
does not construct any of them and does not state Corollary 3.12.
-/
structure Scene1Input (K : Type uK) [Field K] [NumberField K]
    (O : Type uK) [CommRing O] (p : ℕ)
    [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
    [IsAdicComplete (Ideal.span {(p : O)}) O] where
  data : PrologueInputData K O p
  input_laws : PrologueInputLaws p data
  adelic_theta_link : AdelicThetaLink data.link
  theta_lift_log : ThetaLiftLog data.link
  packet_collation_hull : PacketCollationHull data.link
  volume_transfer : VolumeTransfer data.link

/-!
The constructor keeps the six inputs visible at the call site.  It is only a
data-packaging operation; no downstream proposition is proved here.
-/
def Scene1Input.ofExplicit
    {K : Type uK} [Field K] [NumberField K]
    {O : Type uK} [CommRing O] (p : ℕ)
    [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
    [IsAdicComplete (Ideal.span {(p : O)}) O]
    (data : PrologueInputData K O p)
    (input_laws : PrologueInputLaws p data)
    (adelic_theta_link : AdelicThetaLink data.link)
    (theta_lift_log : ThetaLiftLog data.link)
    (packet_collation_hull : PacketCollationHull data.link)
    (volume_transfer : VolumeTransfer data.link) :
    Scene1Input K O p :=
  { data
    input_laws
    adelic_theta_link
    theta_lift_log
    packet_collation_hull
    volume_transfer }

end JoshiTeich.Act1Scene1
