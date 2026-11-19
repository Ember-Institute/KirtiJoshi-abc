noncomputable def tateParameter {w : FinitePlace C.F} (hw : w ∈ C.badAll) :
    TateParameter (localCompletion w) :=
  (TateParameter.exists_tateParameter_tateJ_eq (twelve_ne_zero w) (C.one_lt_norm_j hw)).choose

lemma tateParameter_tateJ {w : FinitePlace C.F} (hw : w ∈ C.badAll) :
    (C.tateParameter hw).tateJ = FinitePlace.embedding w.maximalIdeal C.E.j :=
  (TateParameter.exists_tateParameter_tateJ_eq (twelve_ne_zero w)
    (C.one_lt_norm_j hw)).choose_spec

noncomputable def tateInputs : C.TateInputs where
  tate _ hw := C.tateParameter hw
  tateJ_eq _ hw := C.tateParameter_tateJ hw
  unif w _ := (exists_isUniformizer w).choose
  unif_isUniformizer w _ := (exists_isUniformizer w).choose_spec
