# Finite-ramification independent readback

The JSON covers all nine source-level declarations in the assigned Definitions and Theorems directories. Every row has `declaration`, `path`, `line`, `kind`, `full_signature_static`, exact `source_signature`, expanded binders, and self-contained `en`, `zh_Hans`, and `ja` readbacks. There are no private declarations or source-level instances in these files. The structure-field proofs within `polyDeriv` belong to that definition, and its formula and laws are included. The parent proof's local `letI` is not a separate source-level instance.

## Exact construction and scalar assumptions

`extendOfFormallyEtale` uses three commutative rings R,S,T, all three algebra structures, a compatible scalar tower, and formal étaleness of T over S. It takes an actual R-derivation S→T. It returns the composite of the universal differential T→Ω[T/R], the inverse canonical equivalence Ω[T/R]→T⊗[S]Ω[S/R], and the base extension of the linear map induced by the input derivation. The equivalence direction is explicit. The declaration does not require fields or characteristic zero. No extra preservation law or uniqueness theorem is supplied.

The polynomial declarations use an arbitrary characteristic-zero field K and element t. The canonical ℚ-algebra structure is used. `polyDeriv` additionally assumes that t is transcendental. It acts on the subalgebra ℚ[t], not on the field ℚ(t), and evaluates the formal derivative of the representing polynomial at t. Both evaluation helper theorems are included.

`formallyEtale_adjoin` assumes that K is algebraic over ℚ(t). It does not assume transcendence of t or finite dimensionality. The proof passes through the localization ℚ[t]→ℚ(t), then uses separability in characteristic zero.

`derivAlong` has only the field, characteristic-zero, and t binders. It tests transcendence and algebraicity together. If both hold, it uses the polynomial derivation and the concrete Kähler extension. Otherwise it returns the zero derivation. The readbacks preserve this branch and do not turn either test into an unconditional assertion.

## The two open children

`noncriticalRegularRamifiedDerivNotMem` assumes a given model M, discrete valuation rings at every place, a transcendental field element ψ, a place P where ψ is in the actual local ring, and the strict integer inequality 1<ramIdx. It returns a field element s that belongs to that ring but whose actual derivative does not. No arbitrary derivation or derivative law is a hypothesis. Its body is `by sorry`.

`noncriticalDerivativeBadPlacesFinite` assumes a given model and a transcendental ψ. It ranges over all places where ψ belongs to the local ring and there exists a local element with derivative outside the ring. This set of places is finite. It does not assume `PlacesDiscrete`, residue-field finiteness, or a ramification condition. The witness s is quantified inside each place predicate. Its body is `by sorry`.

## The parent theorem

`noncriticalRamificationFinite` states finiteness of all places where the actual integer `ramIdx` exceeds one. The range includes poles. The written proof uses containment in the union of the pole set and the derivative-failure set. It does not assert equality with that union. Model supplies the existing curve-field property, which gives finite poles. The two open children supply the derivative-failure finite set and the local implication. Therefore the parent has a source combination proof that still depends on both sorry leaves.

The readbacks define the model's actual field data, the complete valuative-place carrier, and the local ring. Where needed, they give the actual order and ramification-index formulas. They add no existence theorem for models and no geometric smoothness, properness, residue-finiteness, or ramification law beyond the actual source declarations. N is an arbitrary natural-number binder; no positivity assumption on N is added.

## Language and citation

English uses direct mathematical statements. Simplified Chinese uses 导子、形式平展、赋值子环、离散赋值环、剩余域, and Latin spellings for named people such as Kähler and Leibniz. Code identifiers and mathematical symbols remain literal and are explained. Japanese uses standard mathematical encyclopedia-style wording. No untranslated unknown mathematical term was identified; `unknown_terms` is empty.

No original English Mochizuki source was independently checked. The target Lean files do not identify a complete original citation. The JSON leaves work, citation, locator, and quotation null. No quotation or source match is invented.

## Scope and uncertainty

Only the two assigned source directories and their imported Lean definitions were consulted. No README, ledger, external author prose, or reference directory was read. No compilation or MCP-CI call was made, and no repository or cache file was edited. A first attempt to locate Mathlib source used an absent package path; the import was then read from the installed Mathlib source at `/home/admin-wsl/Coq/mathlib4-0df444a`. This did not run any build.

Full signatures expand all section variables and typeclass arguments by static source analysis. They retain `Type*` rather than invent elaborated universe names. The bounded existential `∃ s∈P.1` is reconstructed as `∃ (s:M.K), s∈P.1 ∧ ...`; it does not quantify over a ring subtype without the membership condition. The source index comparison is in ℤ. No elaboration receipt or axiom audit is claimed.

## Static validation result

All eight static checks passed: exact nine-declaration coverage; exact raw signature matches; required schema and three languages; expanded binders present; open-leaf status; no omitted private or instance declaration; the algebraicity-only formal-étaleness hypothesis; and a null unchecked quotation. No compilation was run.
