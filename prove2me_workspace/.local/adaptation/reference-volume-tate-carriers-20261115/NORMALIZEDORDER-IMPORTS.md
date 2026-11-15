Keep the current reviewed source435 imports. Required imports.json and review edits: zero.

The inspection reads actual comment-stripped module headers and follows only
public imports. It excludes original Tate peer import closures. Exact paths,
line numbers, header bytes and file SHA256s are recorded in
normalizedorder-import-visibility.json.

* `linarith` and `nlinarith`: existing Archimedean.Real.Basic publicly imports
  Archimedean.Basic → Rat.Floor → Order.Round → Floor.Ring → Tactic.Linarith →
  Linarith.Frontend. Frontend syntax owners are lines 477 and 505.
* `by_contra`: existing Mathlib.Order.Defs.LinearOrder publicly imports
  Batteries.Tactic.Init, which defines the syntax/macro.
* `omega`: existing Log.Basic has a public chain through Exp,
  SpecificLimits.Normed, Spectrum, Ideal and Tactic.Order to Lean.Elab.Tactic.Omega.
* `exact_mod_cast`: implicit Init imports Init.TacticsExtra, whose line 91
  expands the macro to `exact mod_cast`. NormCast.lean:218 registers the builtin
  modCast term elaborator. This need not be re-exported by the selected source
  imports: the accepted driver imports Lean, which imports Elab.Tactic.NormCast;
  builtin elaborators live in a process IO.Ref table initialized before the
  selected source frontend (KeyedDeclsAttribute.lean:104–105,120–124).

A public source-header chain to NormCast was not claimed. An initial whole-file
scan included documentation snippets; it was discarded in favor of header-only
inspection. No main source/import/review edits were made. No compiler or CI job
was run. The authentic single-source oracle remains the acceptance gate.
