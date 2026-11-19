namespace AbcAdaptation.Tripod
open WeierstrassCurve NumberField
open scoped IntermediateField

noncomputable def gen' (l : Qbar) : fieldOf' l := ⟨l, mem_fieldOfExtended_self l⟩

end AbcAdaptation.Tripod
