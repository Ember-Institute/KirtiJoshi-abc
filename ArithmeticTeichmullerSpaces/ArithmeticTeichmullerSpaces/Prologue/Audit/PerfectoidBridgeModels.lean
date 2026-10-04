import ArithmeticTeichmullerSpaces.Prologue.Audit.Models
import ArithmeticTeichmullerSpaces.Prologue.Audit.PerfectoidModels

namespace JoshiTeich.Prologue.Audit

open JoshiTeich.Prologue
open scoped NumberField

local instance bridge_padicTwo_not_unit : Fact (¬ IsUnit (2 : ℤ_[2])) :=
  padicTwo_not_unit
local instance bridge_padicTwo_is_adic_complete :
    IsAdicComplete (Ideal.span {(2 : ℤ_[2])}) ℤ_[2] :=
  padicTwo_is_adic_complete

noncomputable def padicTwoPlaceData :
    @PerfectoidPlaceData ℚ inferInstance inferInstance ℤ_[2] inferInstance 2
      inferInstance bridge_padicTwo_not_unit bridge_padicTwo_is_adic_complete :=
  @PerfectoidPlaceData.mk ℚ inferInstance inferInstance ℤ_[2] inferInstance 2
    inferInstance bridge_padicTwo_not_unit bridge_padicTwo_is_adic_complete
    rationalTwoPlace padicTwoPerfectoidData

noncomputable def padicTwoIntegralMap : 𝓞 ℚ →+* ℤ_[2] :=
  (algebraMap ℤ ℤ_[2]).comp Rat.ringOfIntegersEquiv.toRingHom

noncomputable def padicTwoBridgeData :
    @PerfectoidBridgeData ℚ inferInstance inferInstance
      (auditData 2 0 0 7 2 3) ℤ_[2] inferInstance 2 inferInstance
      bridge_padicTwo_not_unit bridge_padicTwo_is_adic_complete padicTwoPlaceData :=
  @PerfectoidBridgeData.mk ℚ inferInstance inferInstance
    (auditData 2 0 0 7 2 3) ℤ_[2] inferInstance 2 inferInstance
    bridge_padicTwo_not_unit bridge_padicTwo_is_adic_complete padicTwoPlaceData
    padicTwoIntegralMap

theorem padicTwo_bridge_model :
    @PerfectoidBridgeLaws ℚ inferInstance inferInstance
      (auditData 2 0 0 7 2 3) ℤ_[2] inferInstance 2 inferInstance
      bridge_padicTwo_not_unit bridge_padicTwo_is_adic_complete padicTwoPlaceData
      padicTwoBridgeData := by
  have hlocal :
      @PerfectoidPlaceLaws ℚ inferInstance inferInstance ℤ_[2] inferInstance 2
        inferInstance bridge_padicTwo_not_unit bridge_padicTwo_is_adic_complete
        padicTwoPlaceData := by
    exact @PerfectoidPlaceLaws.mk ℚ inferInstance inferInstance ℤ_[2] inferInstance
      2 inferInstance bridge_padicTwo_not_unit bridge_padicTwo_is_adic_complete
      padicTwoPlaceData (by
        simpa [padicTwoPlaceData] using padicTwo_perfectoid_model)
  exact @PerfectoidBridgeLaws.mk ℚ inferInstance inferInstance
    (auditData 2 0 0 7 2 3) ℤ_[2] inferInstance 2 inferInstance
    bridge_padicTwo_not_unit bridge_padicTwo_is_adic_complete padicTwoPlaceData
    padicTwoBridgeData (by
      simp [padicTwoPlaceData, auditData]) hlocal

noncomputable def zeroPlaceData :
    @PerfectoidPlaceData ℚ inferInstance inferInstance ℤ_[2] inferInstance 2
      inferInstance bridge_padicTwo_not_unit bridge_padicTwo_is_adic_complete :=
  @PerfectoidPlaceData.mk ℚ inferInstance inferInstance ℤ_[2] inferInstance 2
    inferInstance bridge_padicTwo_not_unit bridge_padicTwo_is_adic_complete
    rationalTwoPlace zeroPerfectoidData

noncomputable def zeroBridgeData :
    @PerfectoidBridgeData ℚ inferInstance inferInstance
      (auditData 2 0 0 7 2 3) ℤ_[2] inferInstance 2 inferInstance
      bridge_padicTwo_not_unit bridge_padicTwo_is_adic_complete zeroPlaceData :=
  @PerfectoidBridgeData.mk ℚ inferInstance inferInstance
    (auditData 2 0 0 7 2 3) ℤ_[2] inferInstance 2 inferInstance
    bridge_padicTwo_not_unit bridge_padicTwo_is_adic_complete zeroPlaceData
    padicTwoIntegralMap

theorem zero_bridge_violates_laws :
    ¬ @PerfectoidBridgeLaws ℚ inferInstance inferInstance
      (auditData 2 0 0 7 2 3) ℤ_[2] inferInstance 2 inferInstance
      bridge_padicTwo_not_unit bridge_padicTwo_is_adic_complete zeroPlaceData
      zeroBridgeData := by
  intro h
  have hplace :
      @PerfectoidPlaceLaws ℚ inferInstance inferInstance ℤ_[2] inferInstance 2
        inferInstance bridge_padicTwo_not_unit bridge_padicTwo_is_adic_complete
        zeroPlaceData :=
    @PerfectoidBridgeLaws.local_laws ℚ inferInstance inferInstance
      (auditData 2 0 0 7 2 3) ℤ_[2] inferInstance 2 inferInstance
      bridge_padicTwo_not_unit bridge_padicTwo_is_adic_complete zeroPlaceData
      zeroBridgeData h
  have hperf :
      @Perfectoid.PerfectoidLaws ℤ_[2] inferInstance 2 inferInstance
        bridge_padicTwo_not_unit zeroPerfectoidData :=
    @PerfectoidPlaceLaws.perfectoid ℚ inferInstance inferInstance ℤ_[2]
      inferInstance 2 inferInstance bridge_padicTwo_not_unit
      bridge_padicTwo_is_adic_complete zeroPlaceData hplace
  have huntilt :
      @Perfectoid.UntiltingLaws ℤ_[2] inferInstance 2 inferInstance
        bridge_padicTwo_not_unit zeroUntilt :=
    @Perfectoid.PerfectoidLaws.untilting ℤ_[2] inferInstance 2 inferInstance
      bridge_padicTwo_not_unit zeroPerfectoidData hperf
  have hone := @Perfectoid.UntiltingLaws.one ℤ_[2] inferInstance 2 inferInstance
    bridge_padicTwo_not_unit zeroUntilt huntilt
  norm_num [zeroUntilt] at hone

end JoshiTeich.Prologue.Audit
