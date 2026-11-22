import Solutions.Source_ReferenceIutCor312RepresentativeCrystallinePlace

/-!
The crystalline numerator of Joshi III (9.9.4)–(9.9.6) at the representative
chosen by P7 comes from the root tower defining its rational Kummer class.
-/

set_option autoImplicit false

namespace AbcAdaptation.Reference.Iut.ThetaLocalData

open NumberField JoshiTeich.Act1Scene1 JoshiTeich.Prologue.Arithmetic

universe u v

noncomputable section

local instance representativeCrystallineSectionPrime {K : Type*} [Field K] [NumberField K]
    (s : FinitePlace K) : Fact (residueChar s).Prime :=
  LocalCompletion.selectedPrime s

variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}
variable {D : InitialThetaData AG TG} {LT : LocalTheory.{u, v} D.Kt}
variable (TL : ThetaLocalData D LT) (QI : QPilotInputs D) (w : QI.badModuliFinset)

local notation "s₀" => D.localData.sect.sectFin (Subtype.val w)
local notation "p₀" => residueChar s₀

/-- The Fontaine ideal membership at the P7 representative of a bad moduli place. -/
theorem section_paperQRootKummerPreTilt_teichmuller_sub_one_mem_theta_ker_sup_prime :
    CrystallineEnvelope.isPadicLogInput p₀ (paperQRootKummerPreTilt TL s₀) :=
  paperQRootKummerPreTilt_teichmuller_sub_one_mem_theta_ker_sup_prime TL s₀

/-- The crystalline logarithm at the finite place selected by the P7 section. -/
def sectionPaperQRootCrystallineLog : CrystallineEnvelope.PadicACris p₀ :=
  paperQRootCrystallineLog TL s₀

end

end AbcAdaptation.Reference.Iut.ThetaLocalData
