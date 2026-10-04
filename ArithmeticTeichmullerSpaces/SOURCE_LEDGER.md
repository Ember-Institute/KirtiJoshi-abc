# JoshiTeich 来源登记

本文件登记 `ArithmeticTeichmullerSpaces/` 中声明的来源和验证状态。`refer/iut`
不是本工程的上游、Lake 依赖或证明来源；它只能作为逐文件 API 参考。

## 冻结环境

- Lean: `v4.35.0-rc3`, commit `470d5ce1400764999581fd26d5d72b00d990b0f4`
- mathlib4: local path `/home/admin-wsl/Coq/mathlib4`, commit
  `389347a7c1cfa76f6bd5be2ca35d4cb621610ad3`
- Lean project root: `ArithmeticTeichmullerSpaces/`
- Development rule: after development starts, these versions and the toolchain are frozen.

## JoshiTeich references

| source-id | Reference | Used by | Status |
| --- | --- | --- | --- |
| `JT-AHS` | `refer/JoshiTeich/index-Arithmetic Holomorphic Structures.md` | arithmetic holomorphic structures, untilt and tempered objects | specification |
| `JT-ATS-I` | `refer/JoshiTeich/index-Arithmetic Teichmuller Spaces 1.md` | Berkovich/tempered invariance and adelic objects | specification |
| `JT-ATS-II` | `refer/JoshiTeich/index-Arithmetic Teichmuller Spaces 2.md` | Tate data, `q` scaling and theta-pilot prototype | specification |
| `JT-ATS-II5` | `refer/JoshiTeich/index-Arithmetic Teichmuller Spaces 2.5.md` | arithmeticoid, height and different/conductor interfaces | specification |
| `JT-ATS-III` | `refer/JoshiTeich/index-Arithmetic Teichmuller Spaces 3.md` | theta-link, log-shell and Corollary 3.12 interfaces | specification |
| `JT-ATS-IV` | `refer/JoshiTeich/index-Arithmetic Teichmuller Spaces 4.md` | main bounds, Vojta and `abc` dependency chain | specification |

## Current Lean declarations

| source-id | Declaration | File | Status |
| --- | --- | --- | --- |
| `JT-M-NF-FINPLACE` | `NumberField.FinitePlace` | mathlib `NumberField/Completion/FinitePlace.lean` | imported mathlib type |
| `JT-M-RAT-RINGINT` | `Rat.ringOfIntegersEquiv` | mathlib `NumberTheory/NumberField/Basic.lean` | imported mathlib equivalence |
| `JT-M-DIFFERENT-IDEAL` | `differentIdeal`, `NumberField.absNorm_differentIdeal` | mathlib `NumberTheory/NumberField/Discriminant/Different.lean` | imported ideal and norm theorem |
| `JT-ATS-II5-ARITH-DIVISOR` | `FinitePlaceDivisor`, `logDegree` | `ArithmeticTeichmullerSpaces/Prologue/Arithmetic/Basic.lean` | D-interface from II.5 arithmetic degree data |
| `JT-ATS-II5-HEIGHT` | `HeightData`, `HeightData.value_nonneg` | `ArithmeticTeichmullerSpaces/Prologue/Arithmetic/Basic.lean` | finite-place height interface from II.5 `def:heights` |
| `JT-ATS-IV-RAMIFICATION` | `RamificationProfile`, `differentLog`, `logTotal` | `ArithmeticTeichmullerSpaces/Prologue/Arithmetic/Basic.lean` | D-interface for IV log-different/log-conductor chain |
| `JT-M-PRETILT-UNTILT` | `PreTilt.untilt`, `PreTilt.mk_untilt_eq_coeff_zero`, `PreTilt.untilt_iterate_frobeniusEquiv_symm_pow` | mathlib `RingTheory/Perfectoid/Untilt.lean` | imported untilt map and reduction/Frobenius laws |
| `JT-M-FONTAINE-THETA` | `WittVector.fontaineTheta`, `WittVector.fontaineTheta_teichmuller` | mathlib `RingTheory/Perfectoid/FontaineTheta.lean` | imported Fontaine theta map and Teichmuller compatibility |
| `JT-ATS-PROLOGUE-PERFECTOID` | `untiltMap`, `thetaMap`, `UntiltingLaws`, `FontaineThetaLaws` and canonical law theorems | `ArithmeticTeichmullerSpaces/Prologue/Perfectoid/Untilts.lean` | D-adapter preserving explicit untilt, reduction, Frobenius and theta laws |
| `JT-ATS-AUDIT-PERFECTOID` | `padicTwoUntilt`, `padicTwoTheta`, zero countermodels and audit theorems | `ArithmeticTeichmullerSpaces/Prologue/Audit/PerfectoidModels.lean` | compiled non-degenerate `ℤ_[2]` model and law-violation witnesses |
| `JT-ATS-II-TATE-PARAMETER` | `TateParameterData`, `TateParameterLaws` | `ArithmeticTeichmullerSpaces/Prologue/Theta/Tate.lean` | D-interface for the finite-place Tate parameter function, nonzero parameter, and `0 < |q| < 1` local condition; based on II `th:tate-parameter-as-a-function`, III `pr:admissible-lifts-tate-params`, and II `se:tate-setup` |
| `JT-ATS-AUDIT-TATE` | `auditTateData_laws`, `auditTateData_violation` | `ArithmeticTeichmullerSpaces/Prologue/Audit/TateModels.lean` | compiled `q = 2` model at the genuine `(2)` place and zero-parameter countermodel |
| `JT-ATS-III-DATA-001` | `ThetaPilotData`, `PacketHullData`, `AdelicThetaLinkData` | `ArithmeticTeichmullerSpaces/Prologue/Interfaces/Carriers.lean` | type-checked data layer |
| `JT-ATS-III-CONTRACT-001` | `FirstAxiom` | `ArithmeticTeichmullerSpaces/Prologue/Interfaces/Contracts.lean` | conditional proposition interface |
| `JT-ATS-III-CONTRACT-002` | `AdelicThetaLink` | `ArithmeticTeichmullerSpaces/Prologue/Interfaces/Contracts.lean` | conditional proposition interface |
| `JT-ATS-III-CONTRACT-003` | `ThetaLiftLog` | `ArithmeticTeichmullerSpaces/Prologue/Interfaces/Contracts.lean` | conditional proposition interface |
| `JT-ATS-III-CONTRACT-004` | `PacketCollationHull` | `ArithmeticTeichmullerSpaces/Prologue/Interfaces/Contracts.lean` | conditional proposition interface |
| `JT-ATS-III-CONTRACT-005` | `VolumeTransfer` | `ArithmeticTeichmullerSpaces/Prologue/Interfaces/Contracts.lean` | conditional proposition interface |
| `JT-ATS-AUDIT-MODEL-001` | `rationalTwoPlace`, `auditData` | `ArithmeticTeichmullerSpaces/Prologue/Audit/Models.lean` | compiled non-degenerate model data |
| `JT-ATS-AUDIT-MODEL-002` | satisfying and violating model theorems | `ArithmeticTeichmullerSpaces/Prologue/Audit/Models.lean` | compiled audit witnesses |
| `JT-ATS-AUDIT-ARITH-001` | `auditHeight`, `auditConductor`, `auditRamificationProfile` | `ArithmeticTeichmullerSpaces/Prologue/Audit/Models.lean` | compiled arithmetic model data and positivity witnesses |

The Prologue boundary does not declare Corollary 3.12.  Its four construction theorems
are kept in `Prologue/Obligations` and are not imported by `Prologue/Interfaces`.

## IUT reference boundary

The reference checkout is `refer/iut` at commit `d9465c111ec4073709f67e9fccec7e3eb374a816`.
No IUT file is copied into the current tree and no Lean module imports `refer/iut`.
The checkout remains an API and statement reference only. Any future copied file must add
its source path, source commit, license, copyright notice, destination path and modification
summary before it is used.
