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
| `JT-DATA-001` | `ASTData` and carrier structures | `ArithmeticTeichmullerSpaces/Foundations/Carriers.lean` | type-checked data layer |
| `JT-AST0-001` | `AST₀` | `ArithmeticTeichmullerSpaces/Act2/Foundation.lean` | proposition specification |
| `JT-FIRST-001` | `FirstAxiom` | `ArithmeticTeichmullerSpaces/Act2/Foundation.lean` | proposition specification |
| `JT-C312-001` | `Corollary312` | `ArithmeticTeichmullerSpaces/Act2/Foundation.lean` | proposition specification |

`AST₀` contains structural conditions only. `Corollary312` is not represented as a
proved theorem until Act1 supplies the explicit intermediate contracts.

## IUT reference boundary

The reference checkout is `refer/iut` at commit `d9465c111ec4073709f67e9fccec7e3eb374a816`.
No file from it is currently copied into the Lean project, and no Lean module imports it.
Any future copied file must add a row here with its source path, source commit, license,
copyright notice, destination path and modification summary before it is used.
