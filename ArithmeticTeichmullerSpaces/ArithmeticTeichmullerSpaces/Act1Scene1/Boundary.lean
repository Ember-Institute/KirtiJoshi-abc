import ArithmeticTeichmullerSpaces.Prologue.Interfaces

namespace JoshiTeich.Act1Scene1

open JoshiTeich.Prologue

universe uK

/-!
Scene1 receives the source-bearing producer laws as explicit fields.  The
Prologue input bundle now contains only carrier-level and local laws; the four
global/analytic laws below are Scene1 obligations and are not Core premises.
This boundary does not state Corollary 3.12.
-/
structure Scene1ProducerLaws {K : Type uK} [Field K] [NumberField K]
    (D : AdelicThetaLinkData K) : Prop where
  adelic_theta_link : AdelicThetaLink D
  theta_lift_log : ThetaLiftLog D
  packet_collation_hull : PacketCollationHull D
  volume_transfer : VolumeTransfer D
structure Scene1Input (K : Type uK) [Field K] [NumberField K]
    (O : Type uK) [CommRing O] (p : ℕ)
    [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
    [IsAdicComplete (Ideal.span {(p : O)}) O] where
  data : PrologueInputData K O p
  input_laws : PrologueInputLaws p data
  producer_laws : Scene1ProducerLaws data.link

namespace Scene1Input

variable {K : Type uK} [Field K] [NumberField K]
variable {O : Type uK} [CommRing O] (p : ℕ)
variable [Fact p.Prime] [Fact (¬ IsUnit (p : O))]
variable [IsAdicComplete (Ideal.span {(p : O)}) O]

theorem adelic_theta_link (S : Scene1Input K O p) : AdelicThetaLink S.data.link :=
  S.producer_laws.adelic_theta_link

theorem theta_lift_log (S : Scene1Input K O p) : ThetaLiftLog S.data.link :=
  S.producer_laws.theta_lift_log

theorem packet_collation_hull (S : Scene1Input K O p) : PacketCollationHull S.data.link :=
  S.producer_laws.packet_collation_hull

theorem volume_transfer (S : Scene1Input K O p) : VolumeTransfer S.data.link :=
  S.producer_laws.volume_transfer

end Scene1Input

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
    producer_laws :=
      { adelic_theta_link
        theta_lift_log
        packet_collation_hull
        volume_transfer } }

end JoshiTeich.Act1Scene1
