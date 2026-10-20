# JoshiTeich 来源登记

本文件登记 `ArithmeticTeichmullerSpaces/` 中声明的来源和验证状态。计划规定
`refer/iut` 只能作为逐文件 API 参考。S1.136 的提交基线仍将 `refer/iut` 列为 Lake
依赖，并含有 `import Iut.*`；S1.137 已移除该依赖和导入，IUT 模块现位于本工程的
`ReferenceIut` 命名空间内。Lake 配置改为依赖独立的 `tate-curves-theta` 仓库，固定在
`ca6c2279d3cea0690cdb01328e727118d5485d68`。`lake check-build` 只确认默认目标配置有效；
S1.137 的 Scene1 与 ImportAudit 定向构建已通过，验证了该本地 IUT 依赖闭包在冻结 Lean
版本下可构建。此验证只覆盖这两个目标，不代表完整项目构建或 Corollary 3.12 的数学义务
已经闭合。历史迁移状态见 `docs/开发计划.V1Act1log2.md` 的 S1.136-S1.137。

## 冻结环境

- Lean: `v4.35.0-rc3`, commit `470d5ce1400764999581fd26d5d72b00d990b0f4`
- mathlib4: local path `/home/admin-wsl/Coq/mathlib4`, commit
  `389347a7c1cfa76f6bd5be2ca35d4cb621610ad3`
- Lean project root: `ArithmeticTeichmullerSpaces/`
- Development rule: after development starts, these versions and the toolchain are frozen.

## Build verification

- 2026-10-07: after S1.103, the full tree at local commit `c658a74` was built with
  `prlimit --as=64424509440 -- env LEAN_NUM_THREADS=1 /usr/bin/time -v lake build`;
  the address-space cap is `60 GiB`.
- Result: `7442/7442` jobs completed, exit status `0`, wall-clock time `5:59.74`, maximum
  resident set size `4,642,308 kB` (about `4.43 GiB`). This full build was run before the
  remote push because DNS resolution for `github.com` failed; the validated source tree was
  later pushed to `origin/main` together with its build record. The build validates that exact
  source tree.
- 2026-10-07: after the S1-BND-092 Mathlib interface repair, the full tree was built with
  `ulimit -v 62914560; /usr/bin/time -v lake build`.
- Result: `7408/7408` jobs completed, exit status `0`, wall-clock time `5:55.33`, maximum
  resident set size `4,576,432 kB` (about `4.36 GiB`).
- 2026-10-07: for the S1.112 tenth-push checkpoint, the first full build used
  `/usr/bin/time -v prlimit --as=64424509440:64424509440 -- env LEAN_NUM_THREADS=1 lake build`;
  it reached `7440/7446` jobs and failed in `Act1Scene1.Audit.Models` because two audit proofs
  still expected the old global-parameter carrier. Elapsed time was `5:19.40`, maximum RSS was
  `4,595,084 kB`, and the exit status was `1`. After both model proofs were updated to use the
  completion norm, the targeted `Act1Scene1.Audit.Models` build passed (`3684/3684` jobs, exit
  status `0`, `3:26.58`, maximum RSS `4,603,424 kB`) under the `16 GiB` cap; its active Lean
  child was checked with `prlimit --pid`.
- The full build was then rerun with the same `60 GiB` command. Result: `7446/7446` jobs completed,
  exit status `0`, wall-clock time `5:20.29`, maximum RSS `4,593,652 kB` (about `4.38 GiB`).
  `lake` and active Lean children were checked with `prlimit --pid`; their soft and hard address-
  space limits were both `64424509440` bytes. This build validates the S1.112 Lean source tree.
- 2026-10-08: at the S1.122 tenth-push checkpoint, bare `lake build` completed `18304/18304`
  compilation jobs but failed its final `arithmeticteichmullerspaces:exe` target; exit status `1`,
  elapsed time `1:31:42`, maximum RSS `8,158,860 kB`. The Lake process soft/hard address-space cap
  was `64424509440` bytes. Rebuilding the executable reproduced a Lake package dependency cycle:
  `oka:transDeps -> belyi:transDeps -> heights:transDeps -> iut:transDeps ->
  ArithmeticTeichmullerSpaces:transDeps -> Main:linkInfoNoExport -> exe -> oka:transDeps`.
- The complete project library target then built successfully with
  `/usr/bin/time -v prlimit --as=64424509440:64424509440 -- env LEAN_NUM_THREADS=1 lake build +ArithmeticTeichmullerSpaces`:
  `9159/9159` jobs, exit status `0`, elapsed time `2:54.68`, maximum RSS `1,067,164 kB`. This root
  imports Prologue, Act1Scene1, and Act1Scene2. The Lake process soft/hard address-space cap was
  `64424509440` bytes. Use this target for future full source builds; the separate example executable
  is excluded because its dependency graph contains the cycle above.
- 2026-10-08: for S1.135, the targeted section module built `9138/9138` jobs successfully
  (exit status `0`, elapsed `4:25.24`, maximum RSS `8,171,224 kB`) under
  `prlimit --as=17179869184:17179869184 -- env LEAN_NUM_THREADS=1`. The Scene1 aggregate and
  ImportAudit then built `9164/9164` jobs (exit status `0`, elapsed `6:17.90`, maximum RSS
  `8,172,044 kB`) under the same cap. The new section theorems' axiom audit lists only
  `propext`, `Classical.choice`, and `Quot.sound`.
- 2026-10-09: for S1.137, the targeted `ArithmeticTeichmullerSpaces.Act1Scene1` and
  `ArithmeticTeichmullerSpaces.Prologue.Audit.ImportAudit` build completed `9182/9182` jobs,
  exit status `0`, in about `2:18`, with maximum monitored process-group RSS `8.92 GiB`.
  The build used CPU affinity `0-14`, `-Kjobs=15`, and `LEAN_NUM_THREADS=1`. No memory cgroup
  was available, so a process-group RSS monitor used the documented `55 GiB` stop line under
  the `60 GiB` policy. Mathlib4 was not rebuilt. This verifies the migrated dependency closure
  for the two targets; it is not a full project build.
- 2026-10-09: after S1.150 reached the twentieth successful push, the cold full-source build used
  `setsid taskset -c 0-14 /usr/bin/time -v prlimit --as=64424509440:64424509440 -- env LEAN_NUM_THREADS=1 lake -Kjobs=15 build +ArithmeticTeichmullerSpaces`.
  It completed `9192/9192` jobs with exit status `0` in `1:56:08`. `/usr/bin/time` reported maximum
  RSS `8,277,824 kB`; a two-second process-group RSS monitor measured a peak of `8,428,544 KiB`.
  CPU affinity was `0-14`, Lake used 15 jobs, and each Lean worker used one thread. No memory cgroup
  was available, so the process-group monitor used the documented `55 GiB` stop line; the
  per-process `prlimit --as` value was `60 GiB` and is not the group limit. The existing Mathlib4
  build directory and cached artifacts were preserved and Mathlib4 was not rebuilt. The completed
  cold build resets the push counter to `0/20`; this build-record update will count as `1/20` after
  it is pushed.
- 2026-10-11: S1.185 targeted `PaperQRepresentativeSelectedQRootBridge` built `9162/9162`
  jobs successfully, followed by the `Act1Scene1` and `ImportAudit` aggregate at `9195/9195`
  jobs. Both builds used CPU affinity `0-13`, Lake `-Kjobs=15`, `LEAN_NUM_THREADS=1`, and the
  `60 GiB` per-process address-space limit via `prlimit`; Mathlib4 artifacts were reused.
- 2026-10-09: the S1.152 targeted build of the q-order base-change module, `Act1Scene1`, and
  `Prologue.Audit.ImportAudit` completed `9183/9183` jobs with exit status `0` in `3:02.99`.
  `/usr/bin/time` reported maximum RSS `8,189,160 kB`; two-second process-group sampling measured
  `9,259,376 KiB`. The build used CPU affinity `0-14`, `-Kjobs=15`, and `LEAN_NUM_THREADS=1`.
  No memory cgroup was available; the process-group monitor used the `55 GiB` stop line under the
  `60 GiB` policy. Mathlib4 targets were replayed from existing artifacts and were not rebuilt.
- Successful full builds validate Lean compilation only. They do not close the still-open
  `InitialThetaData`/`TateFamily`, `V_p^oss`, q-factor normalization, or theta-volume source
  obligations listed below.
- The cadence cycle that includes S1.112 started from the S1.103 full build; run one full build
  after every `10` successful pushes. The push that delivered S1.103 commit `c658a74` and build-record commit `3c3d048`
  counted as `1/10`; S1.104 counted as `2/10`; S1.105 counted as `3/10`; the S1.106 source
  change counts as `4/10` after its successful push; S1.107 counted as `5/10`; S1.108 counted as
  `6/10`; S1.109 counted as `7/10`; S1.110 counted as `8/10`; S1.111 counted as `9/10`;
  S1.112 counted as `10/10` after its successful push. The full build above was run at this
  tenth-push checkpoint; the interval restarted at `0/10` after that push. S1.113 reached
  `origin/main` as the first push in the new interval and counted as `1/10`; S1.114 counts as
  `2/10` after its successful push.
  Keep the full build address-space cap at `60 GiB`
  (`prlimit --as=64424509440:64424509440`) and the directed-build cap at `16 GiB`
  (`prlimit --as=17179869184:17179869184`); verify the active Lean child with `prlimit --pid`.
  The preceding baseline counted S1.94 through S1.100 as `1/10`
  through `7/10`, S1.101 as `8/10`, and S1.102 as `9/10`; the full build above supersedes it.
- In the cycle after the S1.112 full-build checkpoint, S1.113 through S1.121 reached `9/10`;
  the S1.122 push attempt failed because `github.com` did not resolve and did not increment the count.
  S1.123 commit `538a46f` was then pushed successfully as `10/10`. Its post-push full source build
  used `/usr/bin/time -v prlimit --as=64424509440:64424509440 -- env LEAN_NUM_THREADS=1 lake build +ArithmeticTeichmullerSpaces`
  and passed: `9159/9159` jobs, exit code `0`, elapsed `5:47.95`, maximum RSS `8,153,180 kB`;
  Lake's soft/hard address-space limits were both `64424509440` bytes. The interval restarted at
  `0/10` after this build. The successful push of this build-record update will count as `1/10` in the
  new interval. Continue running this full source target after every `10` successful pushes;
  directed/full-build address-space caps remain `16 GiB` / `60 GiB`.
- Since that checkpoint, the build-record update counted as `1/10`; S1.124 counted as `2/10`; the
  S1.125 push failed and did not increment the interval; S1.126 commit `2fdd658` was pushed as
  `3/10`; its record follow-up counted as `4/10`; S1.127, S1.128, and S1.129 reached `5/10`, `6/10`,
  and `7/10`. S1.130's successful push will count as `8/10`. Keep the full source target
  `lake build +ArithmeticTeichmullerSpaces` at the `10/10` checkpoint and retain the `60 GiB` full /
  `16 GiB` directed address-space caps.
- S1.130's first directed build failed (`4:39.66`, maximum RSS `8,150,260 kB`, exit status `1`) because
  the new bad-place finiteness module did not directly import `Iut.Cor312.ThetaData.PlaceUnder`, which
  defines `Iut.one_lt_valuation_j_of_mult`. After adding that import, the targeted
  `IutInitialThetaQRootAccounting`, `Act1Scene1`, and `ImportAudit` build passed (`9159/9159` jobs,
  exit status `0`, elapsed `10:52.27`, maximum RSS `8,187,528 kB)
  under `/usr/bin/time -v prlimit --as=17179869184:17179869184 -- env LEAN_NUM_THREADS=1 lake build ...`.
  A direct `lake env lean` check of `IutInitialThetaQRootAccounting.lean` also passed (exit status `0`,
  `3:08.02`, maximum RSS `8,172,220 kB`); active Lean PID `12597` had soft/hard address-space limits
  `17179869184` bytes. New declarations in ImportAudit depend only on `propext`, `Classical.choice`,
  and `Quot.sound`.
- The S1.131 full-build correction reset the cycle after its successful result-record push; that record
  update counted as `1/10`. S1.132 commit `65cd89d` was successfully pushed as `2/10`. The current
  build-record update will count as `3/10` if pushed. Continue running
  `lake build +ArithmeticTeichmullerSpaces` after each `10` successful pushes. Directed/full-build
  address-space caps remain `16 GiB` / `60 GiB`.

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
| `IUT-COR312-COMPLETION-UNIFORMIZER-NORM` | `Arithmetic.completionNorm_eq_residueChar_pow_neg_one_of_valued`, `Arithmetic.negLog_completionNorm_eq_inertDeg_mul_log_residueChar_of_valued` | `Prologue/Arithmetic/Basic.lean` | `iut`: `refer/iut/Iut/Concrete/ThetaLocalConstruct/Ordp.lean:285-345`; explicit valuation-adapted port of the general uniformizer norm/log calculation; it accepts `Valued.v x = exp(-1)` and does not identify `x` with a real `InitialThetaData` or `TateFamily` uniformizer |
| `IUT-COR312-COMPLETION-UNIFORMIZER-VALUED` | `Arithmetic.IsCompletionUniformizer`, `Arithmetic.valued_eq_exp_neg_one_of_isCompletionUniformizer` | `Prologue/Arithmetic/Basic.lean` | `iut`: `refer/iut/Iut/Concrete/ThetaLocalConstruct/Ordp.lean:285-345`; certificate shape: `refer/iut/.lake/packages/tate-curves-theta/TateCurvesTheta/QParameter/NormalizedOrder.lean:65-70`; port of the `IsUniformizer` valuation argument; no real `AdmissiblePrimeData` or `InitialThetaData` realization |
| `IUT-COR312-COMPLETION-UNIFORMIZER-CANONICAL-CERT` | `Arithmetic.completionUniformizer_isCompletionUniformizer` | `Prologue/Arithmetic/Basic.lean` | `iut`/`mathlib`: valuation argument from `refer/iut/Iut/Concrete/ThetaLocalConstruct/Ordp.lean:285-345`; canonical element from mathlib `valuation_exists_uniformizer` | canonical completion element satisfies the source-shaped three-field certificate; it is a comparison witness, not a real chosen Tate uniformizer |
| `JT-M-NF-FINPLACE` | `NumberField.FinitePlace` | mathlib `NumberField/Completion/FinitePlace.lean` | imported mathlib type |
| `JT-M-RAT-RINGINT` | `Rat.ringOfIntegersEquiv` | mathlib `NumberTheory/NumberField/Basic.lean` | imported mathlib equivalence |
| `JT-M-DIFFERENT-IDEAL` | `differentIdeal`, `NumberField.absNorm_differentIdeal` | mathlib `NumberTheory/NumberField/Discriminant/Different.lean` | imported ideal and norm theorem |
| `JT-ATS-II5-ARITH-DIVISOR` | `FinitePlaceDivisor`, `logDegree` | `ArithmeticTeichmullerSpaces/Prologue/Arithmetic/Basic.lean` | D-adapter from II.5 `def:arith-deg-ideloid`, lines 1176-1182 |
| `IUT-COR312-RESIDUE-CHAR` | `Arithmetic.residueChar`, `Arithmetic.residueChar_prime` | `ArithmeticTeichmullerSpaces/Prologue/Arithmetic/Basic.lean` | `iut`; port of the finite-place residue-characteristic definition and primality proof from the Corollary 3.12 ThetaData/Places layer; implemented over the local mathlib finite-place carrier without importing `iut` |
| `IUT-COR312-RESIDUE-NORM` | `Arithmetic.absNorm_eq_pow_residueChar` | `ArithmeticTeichmullerSpaces/Prologue/Arithmetic/Basic.lean` | `iut`; port of `absNorm_eq_pow_residueChar` from `refer/iut/Iut/Concrete/ThetaLocalConstruct/Ordp.lean:84-87`, using the local `residueChar_liesOver` and frozen mathlib `Ideal.pow_inertiaDeg`; this is a finite-place norm identity, not the q-pilot/global-degree normalization proof |
| `IUT-COR312-COMPLETION-NORM-ZPOW` | `Arithmetic.completionNorm_eq_residueChar_pow_of_valued` | `ArithmeticTeichmullerSpaces/Prologue/Arithmetic/Basic.lean` | `iut`; port of `norm_eq_zpow_of_valued` from `refer/iut/Iut/Concrete/ThetaLocalConstruct/Ordp.lean:97-103`, adapted to `w.maximalIdeal.adicCompletion K`; the valuation certificate remains explicit and this does not construct a Tate uniformizer or q-pilot source |
| `IUT-COR312-ORDP` | `Arithmetic.ordp`, `Arithmetic.ordp_eq_of_valued`, `Arithmetic.ordp_pow`, `Arithmetic.ordp_nonneg_of_norm_le_one` | `ArithmeticTeichmullerSpaces/Prologue/Arithmetic/Basic.lean` | `iut`: `refer/iut/Iut/Concrete/LocalTheory.lean:78` (`ordp`) and `refer/iut/Iut/Concrete/ThetaLocalConstruct/Ordp.lean:106-131`; ports the normalized `ord_p` definition, valuation formula, power law, and nonnegativity from norm bound. These are target-independent completion arithmetic facts; they do not supply a Tate parameter valuation or a q-root existence theorem |
| `IUT-COR312-COMPLETION-UNIFORMIZER` | `Arithmetic.completionUniformizer`, `Arithmetic.completionUniformizer_valued`, `Arithmetic.completionUniformizer_norm_eq_residueChar_pow_neg_one`, `Arithmetic.negLog_completionUniformizer_norm_eq_inertDeg_mul_log_residueChar` | `ArithmeticTeichmullerSpaces/Prologue/Arithmetic/Basic.lean` | `iut`/`mathlib`; port of the `valued_eq_of_isUniformizer` completion step from `refer/iut/Iut/Concrete/ThetaLocalConstruct/Ordp.lean:285-317`, using mathlib `valuation_exists_uniformizer` and `valuedAdicCompletion_eq_valuation'`; this canonical completion uniformizer is not yet identified with Scene1's Tate uniformizer field |
| `IUT-COR312-PLACE-OVER` | `Arithmetic.residueChar_liesOver`, `Corollary312SourceQPair.rationalPrime_liesOver` | `Prologue/Arithmetic/Basic.lean`, `Act1Scene1/QFamilyBridge.lean` | `iut`; port of the ideal-theoretic finite-place-over-rational-prime relation from `refer/iut/Iut/Cor312/ThetaData/Places.lean`, closed with mathlib `Int.liesOver_span_absNorm` and `Ideal.ringChar_quot`; the pair consumes the relation explicitly |
| `IUT-COR312-RESIDUE-CHAR-TRANSFER` | `Arithmetic.natCast_mem_maximalIdeal_iff`, `Arithmetic.residueChar_eq_of_liesOver` | `Prologue/Arithmetic/Basic.lean` | `iut`; port of `Iut.natCast_mem_maximalIdeal_iff` and `Iut.residueChar_eq_of_liesOver_place` from `refer/iut/Iut/Concrete/CurveArithmeticProved.lean`; quotient-field and ideal-over transfer are proved with the frozen mathlib APIs |
| `IUT-COR312-FINITE-PRIME-SUPPORT` | `Corollary312SourcePlacesOver`, `mem_sourcePlacesOver_iff_liesOver` | `Act1Scene1/QFamilyBridge.lean` | `iut`; finite-support adapter follows the `badCharsOf`/place filtering pattern in `refer/iut/Iut/Concrete/ThetaLocalConstruct/Data.lean`; the ideal-over equivalence is closed by the ported Prologue arithmetic lemmas and is explicitly not named as the completed `V_p^oss` construction |
| `JT-ATS-II5-HEIGHT` | `HeightData`, `HeightData.value_nonneg` | `ArithmeticTeichmullerSpaces/Prologue/Arithmetic/Basic.lean` | finite-place height interface from II.5 `def:heights`, lines 1657-1663 |
| `JT-ATS-IV-RAMIFICATION` | `RamificationProfile`, `differentLog`, `logTotal` | `ArithmeticTeichmullerSpaces/Prologue/Arithmetic/Basic.lean` | D-adapter from IV `pr:basic-ramification-data`, lines 1430-1440; `re:diff-rmk`, lines 1496-1502; `pr:tate-divisor`, lines 1542-1563; `th:diff-cond-thm`, lines 1661-1753 |
| `JT-M-PRETILT-UNTILT` | `PreTilt.untilt`, `PreTilt.mk_untilt_eq_coeff_zero`, `PreTilt.untilt_iterate_frobeniusEquiv_symm_pow` | mathlib `RingTheory/Perfectoid/Untilt.lean` | imported untilt map and reduction/Frobenius laws |
| `JT-M-FONTAINE-THETA` | `WittVector.fontaineTheta`, `WittVector.fontaineTheta_teichmuller` | mathlib `RingTheory/Perfectoid/FontaineTheta.lean` | imported Fontaine theta map and Teichmuller compatibility |
| `JT-ATS-PROLOGUE-PERFECTOID` | `untiltMap`, `thetaMap`, `UntiltingLaws`, `FontaineThetaLaws` and canonical law theorems | `ArithmeticTeichmullerSpaces/Prologue/Perfectoid/Untilts.lean` | D-adapter preserving explicit untilt, reduction, Frobenius and theta laws |
| `JT-ATS-PROLOGUE-PERFECTOID-DATA` | `PerfectoidData`, `PerfectoidLaws`, `canonicalPerfectoidData` and its law theorem | `ArithmeticTeichmullerSpaces/Prologue/Perfectoid/Data.lean` | bundled untilt/theta carrier with explicit law boundary |
| `JT-ATS-AUDIT-PERFECTOID` | `padicTwoPerfectoidData`, bundled law model, zero bundled countermodel and audit theorems | `ArithmeticTeichmullerSpaces/Prologue/Audit/PerfectoidModels.lean` | compiled non-degenerate `ℤ_[2]` model and law-violation witnesses |
| `JT-ATS-II-TATE-PARAMETER` | `TateParameterData`, `TateParameterLaws` | `ArithmeticTeichmullerSpaces/Prologue/Theta/Tate.lean` | D-interface for the finite-place Tate parameter function, nonzero parameter, and `0 < |q| < 1`; II `th:tate-parameter-as-a-function`, lines 609-630; III `pr:admissible-lifts-tate-params`, lines 1530-1539. The parameter carrier is the local completion `K_w`, matching `iut` `AdmissiblePrimeData.tate` in `refer/iut/Iut/Cor312/ThetaData/AdmissiblePrime.lean:144-146`; its integer order is derived from the completion valuation |
| `IUT-COR312-LOCAL-TATE-PARAMETER-CARRIER` | `TateParameterData.parameter`, `TateParameterLaws.norm_eq`, `AdelicThetaLinkData.qParameter`, `AdelicThetaLinkData.qNorm`, `AdelicThetaLink.valuation_scaling` | `Prologue/Theta/Tate.lean`, `Prologue/Interfaces/Carriers.lean`, `Prologue/Interfaces/Contracts.lean` | `iut`: `refer/iut/Iut/Cor312/ThetaData/AdmissiblePrime.lean:144-146` stores each bad-place Tate parameter in `localCompletion w`; this port makes both Prologue Tate and adelic q-parameter fields elements of `K_w` and measures them by the completion norm. This is a carrier correction, not a new mathematical assumption or a 3.12 conclusion |
| `IUT-COR312-Q-ORDER` | `Arithmetic.completionQOrder`, `Arithmetic.completionQOrder_pos`, `Arithmetic.completionQOrder_valued`, `Arithmetic.completionNorm_eq_residueChar_pow_neg_qOrder`, `TateParameterData.qOrder`, `TateParameterData.qOrder_pos`, `Corollary312SourceQPair.tate_place`, `Corollary312SourceQPair.qOrder`, `Corollary312SourceQPair.qOrder_pos`, `Corollary312SourceQPair.q_order_coprime`, `Audit.sceneTateData_qOrder` | `Prologue/Arithmetic/Basic.lean`, `Prologue/Theta/Tate.lean`, `Act1Scene1/QFamilyBridge.lean`, `Act1Scene1/Audit/Models.lean` | `iut`; the derived order ports the `AdmissiblePrimeData.qOrder/qOrder_pos` interface from `refer/iut/Iut/Cor312/ThetaData/AdmissiblePrime.lean:176-181` and the normalized valuation convention from `refer/iut/.lake/packages/tate-curves-theta/TateCurvesTheta/QParameter/NormalizedOrder.lean:154-177`. It is computed as `Int.toNat (-log (Valued.v q))`; the completion norm/order identity is derived from the local valuation expansion. The pair still requires explicit Tate-place support |
| `IUT-COR312-Q-NORM-ORDER` | `TateOrderNormCompatibility`, `TateOrderNormCompatibility.qNorm_log_eq_order_mul`, `TateOrderNormCompatibility.qFactor_log_eq_order_mul`, `TateOrderNormCompatibility.groupedSourceQFactor_log_eq_order_mul`, `Audit.scene_tate_order_compatibility`, `Audit.scene_qNorm_log_eq_order_mul` | `Act1Scene1/QNormTateBridge.lean`, `Act1Scene1/Audit/Models.lean` | `iut`/`tate-curves-theta`; port of `TateParameter.norm_q_eq_pow_orderNat` and `TateParameter.ord_eq_orderZ_mul` from `refer/iut/.lake/packages/tate-curves-theta/TateCurvesTheta/QParameter/NormalizedOrder.lean`; the audit model uses `q = 16` and its derived q-order, while the real uniformizer construction remains an explicit Scene1 compatibility field |
| `IUT-COR312-Q-PILOT-LHS` | `Corollary312QPilotData`, `Corollary312QPilotData.mem_bad`, `mem_tate`, `qOrder_pos`, `logQ`, `absLogQ`, `lhs`, `logQ_nonneg` | `Act1Scene1/QPilotBridge.lean` | `iut`; adapted from `refer/iut/Iut/Cor312/LeftHandSide.lean` (`QPilotData`); the arithmetic normalization follows IUT I Example 3.2(iv) and IUT IV Theorem 1.10. The current finite link-place carrier and weights are explicit Scene1 data and are not claimed to be the paper's `V_p^oss` construction |
| `IUT-COR312-ARITH-WEIGHTS` | `Arithmetic.ramIdx`, `inertDeg`, `localDeg`, `placeWeight`, `placeWeight_pos`, `qPilotWeight`, `qPilotWeight_pos`, `qPilotWeight_sum_le_one_of_localDeg_sum_le` | `Prologue/Arithmetic/Basic.lean` | `iut`; arithmetic definitions adapted from `refer/iut/Iut/Concrete/LocalTheory.lean` (`ramIdx`, `inertDeg`, `localDeg`, `placeWeight`) and the q-pilot coefficient from `refer/iut/Iut/Concrete/ThetaRegion.lean` (`inertDeg / Module.finrank ℚ F`). Both `ramIdx` and `inertDeg` use `ℤ` as the base ring, as required for `[K_w : ℚ_p]`; `placeWeight` retains the local degree `e_w f_w`, while `qPilotWeight` is the distinct q-divisor coefficient `f_w/[F:ℚ]`. The sum bridge uses the elementary `f_w ≤ e_w f_w` step and consumes an explicit local-degree sum bound; the place-to-`primesOver` identity remains a separate construction obligation |
| `IUT-COR312-FINITE-PLACE-DEGREE-SUM` | `Arithmetic.localDeg_sum_le_finrank_of_residueChar_filter`, `Arithmetic.qPilotWeight_sum_le_one_of_residueChar_filter`, `sourcePlacesOver_localDeg_sum_le_finrank`, `sourcePlacesOver_qPilotWeight_sum_le_one` | `Prologue/Arithmetic/Basic.lean`, `Act1Scene1/QFamilyBridge.lean` | `iut`; finite-place sum adapter ported from `refer/iut/Iut/Concrete/CurveArithmeticProved.lean` (`sum_inertDeg_le`) and `refer/iut/Iut/Concrete/LocalTheory.lean` (`sum_localDeg`), with the frozen mathlib `Ideal.sum_ramification_inertia_eq_finrank` subtype sum and `NumberField.RingOfIntegers.rank` used for the current API. The source-place consumers remain an explicit filter and are not identified with `V_p^oss` |
| `IUT-COR312-FINITE-PLACE-BASE-CHANGE` | `Arithmetic.sum_localDeg_liesOver` (with `relRamIdx`, `relInertDeg`, `ramIdx_eq_mul`, `inertDeg_eq_mul`, `localDeg_eq_mul`) | `Prologue/Arithmetic/BaseChange.lean` | `iut`: `refer/iut/Iut/Concrete/ThetaLocalConstruct/Ordp.lean:155-276`, especially `sum_localDeg_liesOver`; adapted to the frozen mathlib finite-place and `Ideal.LiesOver` carriers. The proof uses the current mathlib bridge between `Ideal.ramificationIdx'`/`inertiaDeg'` and the project arithmetic definitions. This is a target-independent finite-place identity; it does not construct `InitialThetaData`, `TateFamily`, `V_p^oss`, q-roots, or theta-volume |
| `IUT-COR312-FINITE-PLACE-FIBER` | `Arithmetic.fiber_finite` | `Prologue/Arithmetic/Basic.lean` | `iut`: `refer/iut/Iut/Concrete/LocalConstruct/Arithmetic.lean:107-122` (`fiber_finite`); injects each finite place with `residueChar = p` into the finite `primesOverFinset (p)` carrier, with an empty-fiber branch when `p` is not prime. This is a target-independent finiteness theorem used by local q-root and residue-characteristic sums; it does not construct `InitialThetaData`, `TateFamily`, `V_p^oss`, or theta-volume |
| `IUT-COR312-FINITE-PLACE-DEGREE-IDENTITY` | `Arithmetic.sum_localDeg` | `Prologue/Arithmetic/BaseChange.lean` | `iut`: `refer/iut/Iut/Concrete/LocalConstruct/Arithmetic.lean:124-164` (`sum_localDeg`); identifies the finite-place fibre at a rational prime with `primesOverFinset` and applies `Ideal.sum_ramification_inertia_eq_finrank`, transporting the ramification/inertia factors through the integer ideal under. This is a target-independent exact degree identity; it does not construct `InitialThetaData`, `TateFamily`, `V_p^oss`, q-roots, or theta-volume |
| `IUT-COR312-PLACE-WEIGHTED-SUM` | `Arithmetic.placeUnder`, `Arithmetic.liesOver_placeUnder`, `Arithmetic.eq_placeUnder_of_liesOver`, `Arithmetic.sum_placeWeight_mul` | `Prologue/Arithmetic/BaseChange.lean` | `iut`: `refer/iut/Iut/Cor312/ThetaData/PlaceUnder.lean:31-52` (`placeUnder`) and `refer/iut/Iut/Concrete/ThetaLocalConstruct/Data.lean:149-220` (`sum_placeWeight_mul`); contracts the finite place canonically and ports the finite-fibre weighted accounting through `sum_localDeg_liesOver`. This is a target-independent arithmetic identity; it does not construct `InitialThetaData`, `TateFamily`, `V_p^oss`, q-roots, or theta-volume |
| `IUT-COR312-FINITE-BAD-SUPPORT` | `Arithmetic.finite_places_norm_gt_one`, `Arithmetic.normGtOneFinset`, `Arithmetic.mem_normGtOneFinset_iff` | `Prologue/Arithmetic/Basic.lean` | `iut`; port of the finite bad-place support argument in `refer/iut/Iut/Concrete/CurveArithmeticProved.lean` (`badAll_finite`), reduced to mathlib `NumberField.FinitePlace.hasFiniteMulSupport`; the zero-element branch is explicit and this carrier is not identified with the paper's `V_p^oss` |
| `IUT-COR312-BAD-PLACES-OVER` | `iutBadPlacesOver`, `finite_places_liesOver`, `iutBadPlacesOver_finite`, `iutBadPlacesOverFinset`, `mem_iutBadPlacesOverFinset_iff`, `IutBaseQPilotSource.ofOverVBad` | `Act1Scene1/IutPlaceSource.lean` | `iut`; ports `badPlacesOver`, the finite-fibre argument, and the q-pilot carrier orientation from `refer/iut/Iut/Cor312/ThetaData/GlobalField.lean`, `PlacesOver.lean`, and `Concrete/LocalTheory.lean`; the carrier is derived from a supplied finite `VBad` by ideal-theoretic `LiesOver`, but Tate parameters, q-orders, `InitialThetaData`, elliptic reduction, and torsion-field witnesses remain explicit inputs |
| `IUT-COR312-NORM-BAD-LOCUS` | `Corollary312NormBadLocus`, `Corollary312NormBadLocus.mem_link_iff`, `Corollary312QPilotData.ofNormBadLocus`, `Corollary312QPilotData.ofNormBadLocus_weight_sum_le_one` | `Act1Scene1/QPilotBridge.lean` | `iut`; combines the finite-support port of `refer/iut/Iut/Concrete/CurveArithmeticProved.lean` (`badAll_finite`) with the q-pilot carrier shape in `refer/iut/Iut/Cor312/LeftHandSide.lean` (`QPilotData`). The measured element and equality between its norm-bad support and the Scene1 link-place carrier remain explicit construction data; the filtered weight bound consumes the ported finite-place sum theorem and this is not identified with `V_p^oss` |
| `IUT-COR312-Q-PILOT-CONCRETE` | `Corollary312QPilotData.ofArithmeticWeights`, `Corollary312QPilotData.ofNormBadLocus` | `Act1Scene1/QPilotBridge.lean` | `iut`; concrete q-pilot assembly adapted from `refer/iut/Iut/Concrete/ThetaRegion.lean` (`QPilotInputs.qPilot`) and `refer/iut/Iut/Cor312/LeftHandSide.lean` (`QPilotData`). It uses `qPilotWeight = inertDeg/[F:ℚ]`; the element-to-link-place support equality and Scene1 link-to-Tate compatibility remain explicit |
| `IUT-COR312-Q-PILOT-SOURCE-FILTER` | `Corollary312QPilotData.filter_eq_sourcePlacesOver` | `Act1Scene1/QPilotBridge.lean` | `iut`; q-pilot finite-place filtering follows `refer/iut/Iut/Concrete/ThetaRegion.lean` (`QPilotData.badFinset`) and the source `(p,w)` filter follows `refer/iut/Iut/Concrete/ThetaLocalConstruct/Data.lean` (`badCharsOf`/place filtering); equality is derived from the explicit `badFinset_spec` and does not identify the carrier with the paper's `V_p^oss` |
| `IUT-COR312-Q-PILOT-SOURCE-NORMALIZATION` | `Corollary312QPilotSourceNormalization`, `Corollary312QPilotData.normalizedLogTerm`, `Corollary312QPilotData.normalizedLogTerm_eq_sourceQFactorLog` | `Act1Scene1/QPilotSourceBridge.lean` | `iut` q-pilot normalization adapted through the local `TateOrderNormCompatibility` port; source q-factor shape from `JoshiTeich: refer/JoshiTeich/index-Arithmetic Teichmuller Spaces 3.md`, `cor:cor312` (3647--3650). The local condition is the weighted equality `-log(norm(uniformizer_w)) = weight(w)·log(residueChar(w))`; no global finite-sum identification is claimed |
| `IUT-COR312-Q-PILOT-SOURCE-INDEX` | `Corollary312SourceQGrouping.ofIutSource`, `Corollary312QPilotSourceIndexBridge`, `Corollary312QPilotSourceIndexBridge.ofGrouping`, `Corollary312QPilotSourceIndexBridge.absLogQ_eq_sourceQLogSum` | `Act1Scene1/QPilotSourceIndexBridge.lean` | `iut` finite q-pilot and place-grouping shapes adapted from `refer/iut/Iut/Cor312/LeftHandSide.lean`, `refer/iut/Iut/Cor312/ThetaData/Places.lean` and `AdmissiblePrime.lean`; target finite `(p,w)` sum from `JoshiTeich: refer/JoshiTeich/index-Arithmetic Teichmuller Spaces 3.md`, `cor:cor312` (3647--3650). `ofIutSource` consumes source-carried q-order coprimality rather than accepting a detached pair proof; `ofGrouping` derives the finite subtype equivalence from the existing q-family equivalences and proves place compatibility. Weight normalization, uniformizer normalization and the real `V_p^oss` construction remain explicit Scene1 obligations |
| `IUT-COR312-Q-PAIR-CONCRETE` | `Corollary312SourceQGrouping.ofPlaceIndex` | `Act1Scene1/QPilotSourceIndexBridge.lean` | `iut`; canonical `(p,w)` labels adapted from `refer/iut/Iut/Cor312/ThetaData/Places.lean` (`residueChar`, `LiesOver`) and `refer/iut/Iut/Cor312/ThetaData/AdmissiblePrime.lean` (`qOrder_coprime`). The target/source index equivalence and q-order coprimality remain explicit Scene1 inputs |
| `IUT-COR312-Q-PILOT-TRANSFER` | `Corollary312TateQFamily.qLogSum_eq_sourceQLogSum`, `Corollary312QPilotTransferLogBound`, `transferLogBound_of_tateQAccounting_qPilot`, `corollary312_of_qPilot_accounting` | `Act1Scene1/QPilotTransferBridge.lean` | q-pilot transfer shape adapted from `iut`: `refer/iut/Iut/Cor312/LeftHandSide.lean` and `refer/iut/Iut/Concrete/ThetaRegion.lean`; packet/hull and target accounting from `JoshiTeich: refer/JoshiTeich/index-Arithmetic Teichmuller Spaces 3.md`, `pr:general-cohomology-set-const` (3261--3271), `th:thetam-construction` (3296--3346), `le:volume-lemma3` (3576--3583), `cor:cor312` (3647--3650). The theorem consumes explicit q-pilot/source index and normalization fields; no q-pilot construction is promoted to Prologue/Core |
| `JT-ATS-AUDIT-TATE` | `auditTateData_laws`, `auditTateData_violation` | `ArithmeticTeichmullerSpaces/Prologue/Audit/TateModels.lean` | compiled `q = 2` model at the genuine `(2)` place and zero-parameter countermodel |
| `JT-ATS-II-THETA-PILOT-SCALING` | `ThetaPilotData.scalingIndex`, `ThetaPilotScalingLaws` | `ArithmeticTeichmullerSpaces/Prologue/Theta/Pilot.lean` and `Interfaces/Carriers.lean` | D-interface for nonzero theta-pilot values and `j^2` norm scaling; II `pr:lift-vals`, lines 820-836; `pr:teichmuller-lift-B`, lines 968-975; III `th:adelic-theta-link`, lines 1139-1166 |
| `JT-ATS-AUDIT-THETA-PILOT` | `auditScalingTheta_laws`, `zeroScalingTheta_violates_laws` | `ArithmeticTeichmullerSpaces/Prologue/Audit/PilotModels.lean` | compiled two-index scaling model with exponents `1, 2` and norms `1/2, 1/16`, plus zero-value countermodel |
| `JT-ATS-III-THETA-SCALING-LINK` | `AdelicThetaLinkData.thetaBase`, `AdelicThetaLink.theta_scaling` | `ArithmeticTeichmullerSpaces/Prologue/Interfaces/Carriers.lean`, `Interfaces/Contracts.lean` | D-integration of III `th:adelic-theta-link`, lines 1139-1166, with the sourced theta-pilot `j^2` law |
| `JT-ATS-III-DATA-001` | `ThetaPilotData`, `PacketHullData`, `AdelicThetaLinkData` | `ArithmeticTeichmullerSpaces/Prologue/Interfaces/Carriers.lean` | D-composition of II `pr:lift-vals`, lines 820-836; II `pr:teichmuller-lift-B`, lines 968-975; III `th:adelic-theta-link`, lines 1139-1166; type-checked data layer. `AdelicThetaLinkData.qParameter` is completion-valued, following the local parameter carrier in `iut` `refer/iut/Iut/Cor312/ThetaData/AdmissiblePrime.lean:144-146` |
| `JT-ATS-III-ARITHMETIC-LINK` | `AdelicThetaLinkData.heightData`, `AdelicThetaLinkData.ramification`, `AdelicThetaLinkData.qNorm`, `AdelicThetaLinkData.height` | `ArithmeticTeichmullerSpaces/Prologue/Interfaces/Carriers.lean` | D-integration of II.5/IV arithmetic profiles; norm and height are sourced projections, not free functions |
| `JT-ATS-III-Q-PARAMETER-LOCAL` | `AdelicThetaLinkData.qParameter`, `FirstAxiom.q_parameter_nonzero`, `AdelicThetaLink.valuation_scaling` | `ArithmeticTeichmullerSpaces/Prologue/Interfaces/Carriers.lean`, `Prologue/Interfaces/Contracts.lean` | `JoshiTeich: refer/JoshiTeich/index-Arithmetic Teichmuller Spaces 3.md`, `pr:admissible-lifts-tate-params` lines 1530-1539 and `th:adelic-theta-link` lines 1139-1166; local `q_w` function over finite places, correcting the earlier global-parameter carrier |
| `JT-ATS-III-Q-PARAMETER-REALIZATION` | `AdelicThetaLinkData.ofTateParameters`, `qNormTateCompatibility_of_tateParameters` | `Prologue/Interfaces/Carriers.lean`, `Act1Scene1/QNormTateBridge.lean` | `JoshiTeich: refer/JoshiTeich/index-Arithmetic Teichmuller Spaces 3.md`, `pr:admissible-lifts-tate-params` lines 1530-1539; D-adapter constructor whose place and parameter equalities are definitional, while the existence of the admissible-lift/Tate family remains an explicit construction obligation |
| `JT-ATS-III-PERFECTOID-BRIDGE` | `PerfectoidPlaceData`, `PerfectoidPlaceLaws`, `PerfectoidBridgeData`, `PerfectoidBridgeLaws` | `ArithmeticTeichmullerSpaces/Prologue/Interfaces/PerfectoidBridge.lean` | D-interface making the number-field place, local `O`, prime `p`, coefficient map and Perfectoid laws explicit |
| `JT-ATS-III-PROLOGUE-INPUT` | `PrologueInputData`, `PrologueInputLaws` | `ArithmeticTeichmullerSpaces/Prologue/Interfaces/Input.lean` | explicit bundle joining adelic link data and one Perfectoid bridge; common input laws remain separate from downstream volume contracts |
| `JT-ATS-III-CONTRACT-001` | `FirstAxiom` | `ArithmeticTeichmullerSpaces/Prologue/Interfaces/Contracts.lean` | conditional proposition interface |
| `JT-ATS-III-CONTRACT-002` | `AdelicThetaLink` | `ArithmeticTeichmullerSpaces/Prologue/Interfaces/Contracts.lean` | conditional proposition interface including explicit theta-pilot scaling, period mapping, and normalization; no independent Frobenius norm-square law |
| `JT-ATS-III-CONTRACT-003` | `ThetaLiftLog` | `ArithmeticTeichmullerSpaces/Prologue/Interfaces/Contracts.lean` | conditional proposition interface |
| `JT-SCENE1-THETA-LOG-NORM-SCALING` | `thetaPilotLogNormScaling` | `ArithmeticTeichmullerSpaces/Act1Scene1/ThetaPilotLogNormScaling.lean` | derives the real-log form of the `j^2` norm scaling from `ThetaPilotScalingLaws.norm_scaling` and positivity; Joshi III `th:adelic-theta-link` lines 1139--1166; consumed by the Scene1 log-sign audit |
| `JT-ATS-III-CONTRACT-004` | `PacketCollationHull` | `ArithmeticTeichmullerSpaces/Prologue/Interfaces/Contracts.lean` | conditional proposition interface |
| `JT-ATS-III-CONTRACT-005` | `VolumeTransfer` | `ArithmeticTeichmullerSpaces/Prologue/Interfaces/Contracts.lean` | conditional proposition interface |
| `JT-ATS-AUDIT-MODEL-001` | `rationalTwoPlace`, `auditData` | `ArithmeticTeichmullerSpaces/Prologue/Audit/Models.lean` | compiled non-degenerate model data |
| `JT-ATS-AUDIT-MODEL-002` | satisfying and violating model theorems | `ArithmeticTeichmullerSpaces/Prologue/Audit/Models.lean` | compiled audit witnesses |
| `JT-ATS-AUDIT-ARITH-001` | `auditHeight`, `auditConductor`, `auditRamificationProfile` | `ArithmeticTeichmullerSpaces/Prologue/Audit/Models.lean` | compiled arithmetic model data and positivity witnesses |
| `JT-ATS-AUDIT-PERFECTOID-BRIDGE` | `padicTwoPlaceData`, `padicTwoBridgeData`, `padicTwo_bridge_model`, `zero_bridge_violates_laws` | `ArithmeticTeichmullerSpaces/Prologue/Audit/PerfectoidBridgeModels.lean` | compiled `(2)`-place/`ℤ_[2]` bridge model and bundled-law violation witness |
| `JT-ATS-AUDIT-PROLOGUE-INPUT` | `padicTwoInputData`, `padicTwo_input_laws`, `badInputData`, `badInput_violates_laws` | `ArithmeticTeichmullerSpaces/Prologue/Audit/InputModels.lean` | compiled common-law input bundle and nonzero-parameter violation witness |
| `JT-ATS-AUDIT-IMPORT` | public Prologue import audit and declaration checks | `ArithmeticTeichmullerSpaces/Prologue/Audit/ImportAudit.lean` | D-audit entry point; imports public Prologue modules and checks carriers, contracts, and model witnesses; excludes `Obligations` |
| `JT-ATS-V1-SCENE1-BOUNDARY` | `Act1Scene1.Scene1Input`, `Scene1Input.ofExplicit` | `ArithmeticTeichmullerSpaces/Act1Scene1/Boundary.lean` | D-boundary declaration; all Prologue data and contracts remain explicit parameters; no Corollary 3.12 statement or proof |
| `JT-ATS-V1-SCENE1-CONTRACT-AUDIT` | `AdelicThetaLinkData`, `AdelicThetaLink`, `Scene1Input`, `Corollary312Data`, `Corollary312` dependency separation | `Prologue/Interfaces/Carriers.lean`, `Prologue/Interfaces/Contracts.lean`, `Act1Scene1/Boundary.lean`, `Act1Scene1/Corollary312.lean` | static contract audit: the pre-target link/input structures contain no `Corollary312` field; the target is introduced only in Scene1/Derived, and public Scene1 proof entrypoints expose their mathematical data through fields or explicit parameters. This audit does not construct a real `InitialThetaData` or `TateFamily` witness |
| `JT-ATS-III-COR312-TARGET` | `Act1Scene1.Corollary312Data`, `Corollary312`, `Corollary312SideConditions` | `ArithmeticTeichmullerSpaces/Act1Scene1/Corollary312.lean` | `JoshiTeich: refer/JoshiTeich/index-Arithmetic Teichmuller Spaces 3.md`, `ss:theta-data-fixing2` lines 1023-1031, `th:moccor-Mochizuki-form2` lines 3617-3632 and `cor:cor312` lines 3647-3650; exact inequality shape with explicit Scene1 realization slots, plus the source conditions `ell ≥ 5` and `ellStar = (ell - 1) / 2`; target specification, not a proof |
| `JT-ATS-III-COR312-RAW-TARGET` | `Corollary312RawSourceQLogSum`, `Corollary312RawTargetSpecification`, `Corollary312RawTarget`, `Corollary312RawTargetSpecification.ofTateQFamily`, `corollary312_iff_rawTarget` | `ArithmeticTeichmullerSpaces/Act1Scene1/RawTargetSpecification.lean` | `JoshiTeich: refer/JoshiTeich/index-Arithmetic Teichmuller Spaces 3.md`, `cor:cor312` lines 3647-3650; proves finite-index equivalence for the current completion-norm q-factor. S1.133 established that this norm gives `|pi| = p^(-f_w)`, while the paper explicitly chooses `|pi|_{C_p} = p^(-1)` at lines 1748-1754 and 2086-2095. Therefore this declaration alone does not identify its factor with the paper's literal local q-term. `ofTateQFamily` derives q-log equalities from existing grouping/place compatibility; the carrier is not identified with `V_p^oss` |
| `JT-ATS-III-COR312-PAPER-Q-NORMALIZATION` | `Corollary312PaperNormalizedSourceQFactor`, `paperNormalizedSourceQFactor_log_eq_raw_div_residueDegree`, `paperNormalizedSourceQFactor_log_eq_qOrder_mul_log_residueChar`, `qPilotNormalizedLogTerm_eq_weightedPaperNormalizedSourceQFactorLog` | `ArithmeticTeichmullerSpaces/Act1Scene1/PaperQNormalizationBridge.lean` | `JoshiTeich: refer/JoshiTeich/index-Arithmetic Teichmuller Spaces 3.md`, `th:moccor-Mochizuki-form2` lines 3617-3632, `cor:cor312` lines 3647-3650, and the explicit `C_p` normalization at lines 1748-1754 and 2086-2095; completion norm law adapted from `iut`: `refer/iut/Iut/Concrete/ThetaLocalConstruct/Ordp.lean`, `norm_eq_zpow_of_valued` and `valued_eq_of_isUniformizer`. Identifies the paper-normalized local q-factor as the completion-norm factor raised to `1/inertDeg(w)` and proves the IUT local contribution is `qPilotWeight(w)` times this paper-normalized term. The theorem is conditional on the existing raw completion norm/order certificate; it does not construct the paper's `L'` representative or `V_p^oss`, and it does not identify the unweighted global paper sum with `iut`'s `absLogQ` |
| `IUT-COR312-Q-PILOT-PAPER-NORMALIZED-ACCOUNTING` | `absLogQ_eq_weightedPaperNormalizedSourceQFactorLogSum` | `ArithmeticTeichmullerSpaces/Act1Scene1/PaperQNormalizationBridge.lean` | `iut`: `refer/iut/Iut/Cor312/LeftHandSide.lean` (`QPilotData.logQ`, `QPilotData.absLogQ`); target local factor and normalization: `JoshiTeich: refer/JoshiTeich/index-Arithmetic Teichmuller Spaces 3.md`, `cor:cor312` lines 3647-3650, with the explicit `C_p` normalization at lines 1748-1754 and 2086-2095. Conditionally sums the established local identity over the q-pilot bad-place carrier, under `TateOrderNormCompatibility`, raw norm degree normalization, and `0 < ell`. It closes only the weighted q-pilot sum of paper-normalized factors; it does not identify the carrier with `V_p^oss`, remove the arithmetic weights, or construct the paper's `L'` representatives |
| `IUT-COR312-Q-PILOT-PAPER-NORMALIZED-INDEX` | `Corollary312WeightedPaperNormalizedSourceQLogSum`, `Corollary312QPilotSourceIndexBridge.absLogQ_eq_weightedPaperNormalizedSourceQLogSum` | `ArithmeticTeichmullerSpaces/Act1Scene1/PaperQAccountingBridge.lean` | `iut`: finite q-pilot source carrier and `QPilotData.absLogQ` from `refer/iut/Iut/Cor312/LeftHandSide.lean`; target `(p,w)` grouping from `JoshiTeich: refer/JoshiTeich/index-Arithmetic Teichmuller Spaces 3.md`, `cor:cor312` (3647-3650). Transports the established q-pilot weighted paper-normalized sum through the explicit finite source-index equivalence. It remains conditional on `TateOrderNormCompatibility`, raw norm degree normalization, and `0 < ell`; it does not remove `qPilotWeight`, identify the carrier with `V_p^oss`, or construct the paper's `L'` representatives |
| `JT-ATS-III-SCENE1-VOLUME-BRIDGE` | `Corollary312VolumeData`, `Corollary312VolumeBound`, `corollary312_of_volume_lower_bound` | `ArithmeticTeichmullerSpaces/Act1Scene1/VolumeBridge.lean` | `JoshiTeich: refer/JoshiTeich/index-Arithmetic Teichmuller Spaces 3.md`, `th:moccor-Mochizuki-form2` lines 3617-3632 and `cor:cor312` lines 3647-3650; complete logarithmic bridge from an explicit multiplicative theta-volume lower bound to the target inequality; the lower bound remains an explicit Scene1 input |
| `JT-ATS-III-SCENE1-Q-FAMILY` | `Corollary312SourceQIndex`, `Corollary312SourceQPair`, `Corollary312SourceQPair.rationalPrime_eq_residueChar`, `Corollary312SourceQGrouping`, `Corollary312GroupedSourceQFactor`, `Corollary312SourceQFactor`, `Corollary312QFamily`, `volumeBound_of_qFamily`, `corollary312_of_q_family_lower_bound` | `ArithmeticTeichmullerSpaces/Act1Scene1/QFamilyBridge.lean` | `JoshiTeich: refer/JoshiTeich/index-Arithmetic Teichmuller Spaces 3.md`, `th:moccor-Mochizuki-form2` lines 3617-3632 and `cor:cor312` lines 3647-3650; explicit finite-place index equivalence, `(p,w)` pair/grouping carrier, rational-prime label bound to `Arithmetic.residueChar`, and `qNorm^(1/(2*ell))` normalization; the actual paper-side identification remains a Scene1 construction obligation |
| `JT-ATS-III-SCENE1-QNORM-TATE` | `QNormTateCompatibility`, `qNorm_pos_lt_one_of_tate`, `Corollary312QFamily.ofTateCompatibility`, `Corollary312TateQFamily`, `Corollary312TateQFamily.toQFamily` | `ArithmeticTeichmullerSpaces/Act1Scene1/QNormTateBridge.lean` | `JoshiTeich: refer/JoshiTeich/index-Arithmetic Teichmuller Spaces 2.md`, `th:tate-parameter-as-a-function` lines 609-630; supplementary `JoshiTeich: refer/JoshiTeich/index-Arithmetic Teichmuller Spaces 3.md`, `pr:admissible-lifts-tate-params` lines 1530-1539; explicit q-norm/Tate compatibility, with strict q-norm range derived from `TateParameterLaws`; the public Scene1 assembly stores compatibility instead of accepting `qNorm ≤ 1` as an unrelated field |
| `JT-ATS-III-SCENE1-VOLUME-NORMALIZATION` | `Corollary312VolumeNormalization`, `logVolume_nonneg_of_scene1`, `thetaVolume_pos_of_normalization`, `thetaVolume_le_one_of_normalization`, `corollary312_of_q_family_normalized_lower_bound` | `ArithmeticTeichmullerSpaces/Act1Scene1/VolumeNormalizationBridge.lean` | `JoshiTeich: refer/JoshiTeich/index-Arithmetic Teichmuller Spaces 3.md`, `le:volume-lemma3` lines 3576-3583, `th:moccor-Mochizuki-form2` lines 3617-3632 and `cor:cor312` lines 3647-3650; local exponential sign normalization and nonnegativity transfer from explicit `VolumeTransfer` |
| `JT-ATS-III-SCENE1-TRANSFER-Q-LOWER` | `Corollary312TransferLogBound`, `logVolume_upper_bound_of_transfer_log_bound`, `thetaVolume_lower_bound_of_transfer_log_bound`, `corollary312_of_transfer_log_bound` | `ArithmeticTeichmullerSpaces/Act1Scene1/TransferQLowerBound.lean` | `JoshiTeich: refer/JoshiTeich/index-Arithmetic Teichmuller Spaces 3.md`, `le:volume-lemma3` lines 3576-3583, `th:moccor-Mochizuki-form2` lines 3617-3632 and `cor:cor312` lines 3647-3650; conditional finite-sum-to-product conversion. `transfer_log_bound` is equivalent to the target inequality under volume transfer, nonnegativity, normalization, and positive `ellStar`; deriving that core packet/hull estimate from the source construction remains open. |
| `JT-ATS-III-SCENE1-TRANSFER-Q-ACCOUNTING` | `Corollary312PacketSourceQLogSum`, `Corollary312HullSourceQLogSum`, `Corollary312SourceQLogSum`, `Corollary312TateQAccounting`, `Corollary312TateQAccounting.toAccounting`, `Corollary312TransferQAccounting`, `transferLogBound_of_qAccounting`, `corollary312_of_transfer_q_accounting` | `ArithmeticTeichmullerSpaces/Act1Scene1/TransferQAccounting.lean` | `JoshiTeich: refer/JoshiTeich/index-Arithmetic Teichmuller Spaces 3.md`, `pr:general-cohomology-set-const` lines 3261-3271, `th:thetam-construction` lines 3296-3346, `le:volume-lemma3` lines 3576-3583 and `cor:cor312` lines 3647-3650; packet/hull weights are first bounded against source Tate q terms, whose finite conservation equality is then converted to the existing q-log accounting contract |
| `JT-ATS-III-SCENE1-ADELIC-THETA-BRIDGE` | `Corollary312Scene1Data`, `cor312_of_scene1_data` | `ArithmeticTeichmullerSpaces/Act1Scene1/AdelicThetaLinkBridge.lean` | `JoshiTeich: refer/JoshiTeich/index-Arithmetic Teichmuller Spaces 3.md`, `th:adelic-theta-link` lines 1139-1166, `pr:general-cohomology-set-const` lines 3261-3271, `th:thetam-construction` lines 3296-3346, `le:volume-lemma3` lines 3576-3583 and `cor:cor312` lines 3647-3650; conditional Scene1 assembly of independently supplied target data; the theorem does not derive the target from `AdelicThetaLink` alone |
| `JT-ATS-III-SCENE1-ADELIC-THETA-QPILOT` | `Corollary312Scene1QPilotData`, `Corollary312Scene1QPilotData.qPilot`, `Corollary312Scene1QPilotData.sourceIndexBridge`, `cor312_of_scene1_qPilot_data` | `ArithmeticTeichmullerSpaces/Act1Scene1/AdelicThetaLinkBridge.lean` | q-pilot assembly adapted from `iut`: `refer/iut/Iut/Cor312/LeftHandSide.lean`, `refer/iut/Iut/Concrete/ThetaRegion.lean`, and `refer/iut/Iut/Cor312/ThetaData/Places.lean`; target assembly remains sourced from `JoshiTeich: refer/JoshiTeich/index-Arithmetic Teichmuller Spaces 3.md`, `th:adelic-theta-link` lines 1139-1166, `pr:general-cohomology-set-const` lines 3261-3271, `th:thetam-construction` lines 3296-3346, `le:volume-lemma3` lines 3576-3583 and `cor:cor312` lines 3647-3650; `Corollary312Scene1QPilotData` requires an `IutQPilotSource` and derives its q-pilot, source normalization, and canonical source-index bridge from the existing q-family grouping; the bridge is no longer a detached structure field. The source `orderCompatibility` and the real source-to-`V_p^oss` identification remain explicit Scene1 obligations; the current `ℚ,(2)` result is only a consistency witness, while a model sourced from real `InitialThetaData/TateFamily` remains open |
| `JT-ATS-AUDIT-ARITHMETIC-QPILOT` | `rationalTwoPlace_residueChar`, `rationalTwoPlace_inertDeg`, `rationalTwoPlace_two` | `ArithmeticTeichmullerSpaces/Act1Scene1/Audit/Models.lean` | component-level `ℚ,(2)` arithmetic facts only. `residueChar = 2`, `inertDeg = 1`, and the norm `|(2)|_(2) = 1/2` are proved with mathlib ideal/valuation APIs. The previous synthetic q-pilot satisfying witness and its `Corollary312` theorem were retired because they did not come from real `InitialThetaData/TateFamily`; no q-pilot satisfying model is claimed by this entry |
| `JT-ATS-AUDIT-ADELIC-LINK-NOGO` | `scene_adelicThetaLink_only_countermodel` | `ArithmeticTeichmullerSpaces/Act1Scene1/Audit/Models.lean` | compiled countermodel: the complete `sceneInput` and its `AdelicThetaLink` are unchanged, while `thetaVolume := exp (4 * sceneQTerm)` makes `Corollary312` false; this is a non-derivability witness, not a 3.12 model |
| `IUT-COR312-Q-PILOT-ADAPTER` | `IutQPilotSource`, `IutQPilotSource.qOrder`, `IutQPilotSource.qOrder_pos`, `IutQPilotSource.qOrder_eq_link`, `IutQPilotSource.badFinset_eq_link_places`, `IutQPilotSource.mem_badPlacesOver_iff_link`, `IutQPilotSource.qOrder_coprime_link`, `IutQPilotSource.toSceneQPilot`, `IutQPilotSource.source_norm_eq_uniformizer_pow_order`, `IutQPilotSource.uniformizerNorm_eq_chosenNorm`, `IutQPilotSource.uniformizerNorm_eq_completionNorm`, `IutQPilotSource.toSceneQPilot_rawQNormDegreeNormalization`, `IutQPilotSource.toSceneQPilot_weight_eq_arithmetic` | `ArithmeticTeichmullerSpaces/Act1Scene1/IutQPilotAdapter.lean` | field shape ported from `iut` `QPilotData`, `InitialThetaData.badPlacesOver`, `TateFamily`/`AdmissiblePrimeData.qOrder`, `AdmissiblePrimeData.q_order_coprime`, `AdmissiblePrimeData.unif`/`unif_isUniformizer`, and `QPilotInputs.qPilot`; `qOrder` is now derived as `Arithmetic.completionQOrder w (tateParameter w)`, and positivity and equality to the local Tate order follow from the explicit parameter/link and carrier laws. The adapter still requires `badPlacesOver` finiteness, a nonzero Tate parameter, coprimality of the valuation-derived order, equality to the local link parameter, `orderCompatibility`, a chosen completion element at each bad place, its `IsCompletionUniformizer` certificate, and equality of its raw norm with `uniformizerNorm`. The former free q-order, separate positivity field, and q-order/link equality field were removed; the coprimality proof remains an explicit source field. `qOrder_coprime_link` transports that proof to the local Tate carrier; the raw norm degree normalization theorem derives the residue-degree logarithm law for the separate degree-normalized q-factor bridge. Raw q-pilot source normalization remains an explicit `Corollary312Scene1QPilotData.sourceNormalization` field. This adapter does not construct `InitialThetaData`, `TateFamily`, or a real source instance |
| `IUT-COR312-Q-PILOT-COMPLETION-ADAPTER` | `IutQPilotSource.badFinset_mem_badPlacesOver`, `IutQPilotSource.toBaseQPilotSource`, `IutQPilotSource.completionParameter_norm_eq_chosenUniformizer_pow_order`, `IutQPilotSource.toCompletionTateValuation`, `IutQPilotSource.toCompletionTateValuation_order_eq_qOrder`, `iutCompletionUniformizerQOrder_eq_of_norm_eq` | `ArithmeticTeichmullerSpaces/Act1Scene1/IutQPilotCompletionAdapter.lean`, `IutTateValuation.lean` | `iut`: `refer/iut/Iut/Cor312/ThetaData/AdmissiblePrime.lean` (`localCompletion`, `tate`, `unif`, `unif_isUniformizer`, `q_order_coprime`, `qOrder`) and `refer/iut/.lake/packages/tate-curves-theta/TateCurvesTheta/QParameter/NormalizedOrder.lean`; carries the source Tate parameter directly in its local completion, then proves its chosen-uniformizer order equals the source q-order and transports coprimality. It consumes the current source's parameter/link and order-compatibility fields; it does not construct `InitialThetaData/TateFamily` or close a 3.12 source obligation |
| `IUT-COR312-Q-PILOT-COMPLETION-SOURCE` | `IutQPilotSource.ofBaseCompletionSource` | `ArithmeticTeichmullerSpaces/Act1Scene1/IutQPilotCompletionSource.lean` | `iut`: `refer/iut/Iut/Cor312/ThetaData/AdmissiblePrime.lean` (`tate`, `unif`, `unif_isUniformizer`, `q_order_coprime`, `qOrder`) and `refer/iut/Iut/Concrete/ThetaRegion.lean` (`QPilotInputs.qPilot`); combines an already built base completion source and its completion valuation with explicit bad-place and local-parameter identifications. It derives the completion order/link order equality from `IutCompletionTateValuation.completionQOrder_eq_orderNat`, derives q-order norm compatibility, and transports coprimality; callers no longer supply a separate `hOrder` equality. The local parameter identification is direct, with no extra global-to-local embedding equality; it still must be proved from the real source and does not close the source-model obligation |
| `IUT-COR312-FIELD-ORIENTATION` | `IutBaseQPilotSource`, `IutTorsionQRootSource`, `IutFieldOrientationAudit`, `IutFieldOrientationAudit.qroot_pow_eq_target_completion` | `ArithmeticTeichmullerSpaces/Act1Scene1/FieldOrientationAudit.lean` | `iut`: `refer/iut/Iut/Cor312/ThetaData/Basic.lean`, `AdmissiblePrime.lean`, `TateFamily.lean`, `Concrete/ThetaRegion.lean`, `Concrete/ThetaLocalConstruct/Data.lean`; records that q-pilot weights are on base-field places `F`, while Tate-family/q-root data are on torsion-field places `K_t` and completions. The audit requires the torsion carrier to equal the local Scene1 link carrier and requires the completion comparison map plus equality to the target's local Tate parameter. It does not construct `InitialThetaData`, identify `V_p^oss`, or identify the target local parameter from the real source |
| `IUT-COR312-TORSION-CARRIER` | `IutBaseQPilotSource.badPlaces_finite`, `IutTorsionQRootSource.basePlaceOf`, `IutTorsionQRootSource.basePlaceOf_liesOver`, `IutTorsionQRootSource.ofOverBaseBad` | `ArithmeticTeichmullerSpaces/Act1Scene1/IutPlaceSource.lean` | `iut`: `refer/iut/Iut/Cor312/ThetaData/GlobalField.lean`, `PlaceUnder.lean`, `PlacesOver.lean`, and `Concrete/ThetaLocalConstruct/Data.lean`; the torsion finite carrier is the finite over-locus of the base q-pilot carrier, and each torsion place receives a base-place witness from its `LiesOver` evidence. The constructor does not manufacture q-roots, completion maps, q-root power equations, `InitialThetaData`, or the paper's `V_p^oss` identification |
| `IUT-COR312-PLACE-UNDER` | `iutPlaceUnder`, `iutPlaceUnder_maximalIdeal`, `iutPlaceUnder_liesOver`, `iutPlaceUnder_eq_of_liesOver`, `IutTorsionQRootSource.basePlaceOf_eq_placeUnder` | `ArithmeticTeichmullerSpaces/Act1Scene1/IutPlaceSource.lean` | `iut`: `refer/iut/Iut/Cor312/ThetaData/PlaceUnder.lean`; direct port of the prime contraction `placeUnder` layer to the local `NumberField.FinitePlace` carrier. The contraction is canonical and any `LiesOver` base place equals it. This fixes witness semantics only; it does not construct `InitialThetaData`, `TateFamily`, `V_p^oss`, q-roots, completion maps, or theta-volume |
| `IUT-COR312-COMPLETION-MAP` | `iutCompletionMapPow`, `iutAdicCompletionMapPow`, `iutEmbedCompletion`, `iutEmbedCompletion_embedding`, `iutValuedEmbedCompletion`, `iutEmbedCompletion_norm_lt_one_iff`, `IutTorsionQRootSource.ofOverBaseBadWithCanonicalCompletionMap` | `ArithmeticTeichmullerSpaces/Act1Scene1/IutCompletionSource.lean` | `iut`: `refer/iut/Iut/Concrete/ThetaLocalConstruct/EmbedCompletion.lean` and `refer/iut/Iut/Cor312/ThetaData/ValuationTransfer.lean`; direct valuation-power extension of the field embedding to adic completions, adapted to `Ideal.LiesOver` and frozen mathlib. The canonical map removes an arbitrary completion-map field, while q-roots, their power equation, `InitialThetaData`, `TateFamily`, `V_p^oss`, and theta-volume remain explicit source obligations |
| `IUT-COR312-QROOT-VALUATION-TRANSFER` | `IutTorsionQRootSource.canonical_qroot_valued_pow_eq` | `ArithmeticTeichmullerSpaces/Act1Scene1/IutCompletionSource.lean` | `iut`: `refer/iut/Iut/Concrete/ThetaLocalConstruct/Data.lean:261-281` (`qrootOf_pow`, `ordp_qrootOf`); applies the canonical completion map's valuation scaling to an explicitly supplied q-root power equation. This closes only the valuation transfer `v(qroot)^(2*ell) = v(tateParameter)^e`; it does not construct q-root existence, `InitialThetaData`, `TateFamily`, `V_p^oss`, or theta-volume |
| `IUT-COR312-QROOT-NONZERO` | `IutTorsionQRootSource.canonical_qroot_ne_zero`, `IutTorsionQRootSource.ofOverBaseBadWithCanonicalCompletionMap` | `ArithmeticTeichmullerSpaces/Act1Scene1/IutCompletionSource.lean` | `iut`: `refer/iut/Iut/Concrete/ThetaLocalConstruct/Data.lean:271-279` (`qrootOf_ne_zero`); for the canonical completion map, positive `ell`, the explicit q-root power equation, and `tateParameter_ne_zero`, the image of the Tate parameter is nonzero and `zero_pow` contradicts a zero q-root. The canonical constructor now derives the structure's `qroot_ne_zero` field instead of accepting it as an unrelated input. It still does not construct q-root existence, `InitialThetaData`, `TateFamily`, `V_p^oss`, or theta-volume |
| `IUT-COR312-QROOT-EXISTENCE-COMBINATION` | `IutQRootExistence.exists_two_mul_add_mul_eq_one`, `IutQRootExistence.exists_pow_two_mul_eq`, `IutQRootExistence.exists_pow_two_mul_eq_of_nonzero`, `IutTorsionQRootSource.qrootOfSquareAndEllRoot`, `IutTorsionQRootSource.qrootOfSquareAndEllRoot_pow_eq`, `IutTorsionQRootSource.ofOverBaseBadWithCanonicalCompletionMap_ofRoots` | `ArithmeticTeichmullerSpaces/Act1Scene1/IutQRootExistence.lean` | `iut`: `refer/iut/Iut/Concrete/ThetaLocalConstruct/Roots.lean:44-68` (`exists_two_mul_add_mul_eq_one`, `exists_pow_two_mul_eq`); ports the Bezout combination of an explicit square root and an explicit `ell`-th root into a `2*ell`-th root, with nonzero root witnesses derived from the nonzero canonical Tate-parameter image. The constructor still requires the two root equations and `Odd ell`; it does not derive those roots from torsion cardinality, `InitialThetaData`, `TateFamily`, `V_p^oss`, or theta-volume |
| `IUT-COR312-QROOT-ROOT-CLASS-CORRECTION` | `IutQRootExistence.exists_pow_eq_of_root_class`, `IutTorsionQRootSource.ellRootOfRootClass`, `IutTorsionQRootSource.ellRootOfRootClass_pow_eq`, `IutTorsionQRootSource.ofOverBaseBadWithCanonicalCompletionMap_ofRootClassAndSquareRoot` | `ArithmeticTeichmullerSpaces/Act1Scene1/IutQRootExistence.lean` | `iut`: `refer/iut/Iut/Concrete/ThetaLocalConstruct/Roots.lean` (root-class correction pattern, adapted to the frozen local completion carrier). Given an explicit root-class witness `u^ell = q^(1 + ell*m)`, constructs the corrected root `(u * q^(-m))` and proves its `ell`-th power is `q`; the result then feeds the existing square-root/ell-root Bezout combination. This closes only the exponent correction. Root-class witnesses, the square root, torsion-cardinality input, `InitialThetaData`, `TateFamily`, `V_p^oss`, and theta-volume accounting remain explicit Scene1 obligations |
| `IUT-COR312-QROOT-ROOT-CLASS-CARDINALITY` | `IutQRootExistence.exists_root_class_of_card` | `ArithmeticTeichmullerSpaces/Act1Scene1/IutQRootExistence.lean` | `iut`: `refer/iut/Iut/Anabelian/TateTorsion.lean:226-239` (`exists_root_class`) and `refer/iut/Iut/Concrete/ThetaLocalConstruct/Roots.lean:36-42` (`exists_pow_eq_q_of_card`); ports the finite residue-homomorphism argument. Given an additive residue map `T →+ ZMod ell`, a kernel-cardinality upper bound, `ell^2 ≤ Nat.card T`, and explicit representatives/exponents, the range is forced to be all of `ZMod ell`, yielding `u^ell = q^(1 + ell*m)`. The theorem does not construct the residue map, its kernel bound, a Tate structure, torsion cardinality from `InitialThetaData`, `TateFamily`, `V_p^oss`, or theta-volume |
| `IUT-COR312-TATE-TORSION-RESIDUE` | `IutTateQuotientUniformization`, `IutTateQuotientUniformization.resid`, `resid_eq_zero_iff`, `card_torsion_eq`, `exists_root_class_of_torsion_card`, `IutTorsionQRootSource.exists_root_class_at_place_of_tate_uniformization`, `rootClass`, `rootClassExponent`, `rootClass_pow_eq`, `ofOverBaseBadWithCanonicalCompletionMap_ofTateUniformizationAndSquareRoot` | `ArithmeticTeichmullerSpaces/Act1Scene1/IutTateTorsionResidue.lean` | `iut`: `refer/iut/Iut/Cor312/ThetaData/TateStructure.lean:57-105,110-122` and `refer/iut/Iut/Anabelian/TateTorsion.lean:181-236`; ports the quotient `kˣ/q^ℤ` group isomorphism, the `ell`-torsion residue homomorphism, graph-line kernel identification, kernel/range cardinality product, and the resulting root-class witness. The local abstraction omits elliptic-curve coordinate pinning and `TateCurvesTheta`. Callers must still provide a real quotient uniformization, the `ell²` torsion-cardinality lower bound, equality of the uniformization parameter with the canonical completion image, and (for the final q-root constructor) a square root; it does not construct `InitialThetaData`, `TateFamily`, `V_p^oss`, or their models |
| `IUT-COR312-TORSION-CARDINALITY-TRANSFER` | `IutGlobalTorsionBasis`, `IutGlobalTorsionBasis.card_eq_pow_two`, `IutGlobalTorsionBasis.card_eq_mul`, `IutTorsionLocalMap.image_le_localTorsion`, `IutTorsionLocalMap.card_localTorsion_lower_bound`, `IutTorsionQRootSource.ofOverBaseBadWithCanonicalCompletionMap_ofGlobalTorsionBasisAndSquareRoot` | `ArithmeticTeichmullerSpaces/Act1Scene1/IutTorsionCardinality.lean` | `iut`: `refer/iut/Iut/Anabelian/Torsion.lean:94-109` (`torsionEquiv`, `basisK`, `card_TK`) and `refer/iut/Iut/Anabelian/LocalInputs.lean:53-101` (`toLocal`, `imageTK`, `card_imageTK`, `sq_le_card_torsion`); ports the rank-two `ZMod ell` cardinality and injective localization argument to additive groups. Torsion preservation is derived from the global subgroup's explicit inclusion in `ell`-torsion and the additive local map; the local lower bound uses finiteness from the supplied Tate quotient uniformization. A caller must still provide the real global basis and local point maps; no elliptic-curve model, `AdmissiblePrimeData`, `InitialThetaData`, or `TateFamily` is constructed |
| `IUT-COR312-WEIERSTRASS-LOCALIZATION` | `iutWeierstrassPointMap`, `iutWeierstrassPointMap_injective`, `iutWeierstrassTorsionLocalMap`, `iutWeierstrass_local_torsion_card_lower_bound` | `ArithmeticTeichmullerSpaces/Act1Scene1/IutWeierstrassLocalization.lean` | `iut` at reference commit `d9465c111ec4073709f67e9fccec7e3eb374a816`: `refer/iut/Iut/Cor312/ThetaData/PointMap.lean:29-44` and `refer/iut/Iut/Anabelian/LocalInputs.lean:53-101`; specializes Mathlib's functorial `Affine.Point.map` to a Weierstrass curve over a field and a field homomorphism, then instantiates the rank-two local torsion-cardinality theorem. The target is the actual base-changed Weierstrass point group, but callers must still supply the global rank-two torsion basis and local Tate quotient uniformization; no `AdmissiblePrimeData`, torsion-field rationality proof, finite-place completion instance, or `TateFamily` is constructed |
| `IUT-COR312-WEIERSTRASS-TWO-TORSION-QROOT` | `iutWeierstrass_local_torsion_card_lower_bound_of_global_card`, `iutWeierstrass_exists_square_root_of_global_two_torsion` | `ArithmeticTeichmullerSpaces/Act1Scene1/IutWeierstrassLocalization.lean` | `iut` at reference commit `d9465c111ec4073709f67e9fccec7e3eb374a816`: `refer/iut/Iut/Concrete/ThetaLocalConstruct/Data.lean:97-138` (`four_le_card_torsion_two`, `exists_qroot`), with root-class correction from `IutQRootExistence.exists_pow_eq_of_root_class`. This compatibility path transfers an explicit global lower bound on `E[2]` through the injective Weierstrass point map and derives a corrected square root from the Tate quotient residue argument. The newer `IUT-COR312-SIX-TORSION-TWO-TORSION` entry derives the needed local bound from `SixTorsionRational` and is used by the q-root source constructor; no global `Nat.card E[2]` finiteness is asserted here |
| `IUT-COR312-SIX-TORSION-TWO-TORSION` | `IutSixTorsionRational`, `iutWeierstrass_four_global_two_torsion_points_of_six_torsion_rational`, `iutWeierstrass_local_two_torsion_card_lower_bound_of_six_torsion_rational`, `iutWeierstrass_exists_square_root_of_six_torsion_rational` | `ArithmeticTeichmullerSpaces/Act1Scene1/IutWeierstrassLocalization.lean` | Direct port of the source contract from `iut` at reference commit `d9465c111ec4073709f67e9fccec7e3eb374a816`: `refer/iut/Iut/Cor312/ThetaData/GlobalField.lean:144-146` (`SixTorsionRational`) and `refer/iut/Iut/Concrete/ThetaLocalConstruct/Data.lean:235-239` (`TwoTorsionRational`), plus `Data.lean:97-138` (`four_le_card_torsion_two`, `exists_qroot`). Over an algebraic closure, the Weierstrass 2-torsion cubic has three distinct roots; their affine points and the point at infinity give four distinct geometric 2-torsion points. Six-torsion rationality descends those points to the base field. Their injective images lie in each local 2-torsion subgroup; finiteness supplied by the local Tate quotient gives cardinality at least four, then the existing residue/root-class argument gives a square root. It does not assert global `Nat.card E[2]` finiteness or construct `InitialThetaData`, `TateFamily`, `V_p^oss`, or a q-root family |
| `IUT-COR312-WEIERSTRASS-QROOT-SOURCE` | `IutTorsionQRootSource.ofOverBaseBadWithCanonicalCompletionMap_ofWeierstrassTorsion` | `ArithmeticTeichmullerSpaces/Act1Scene1/IutWeierstrassLocalization.lean` | `iut` at reference commit `d9465c111ec4073709f67e9fccec7e3eb374a816`: `refer/iut/Iut/Concrete/ThetaLocalConstruct/Data.lean:97-138` (`four_le_card_torsion_two`, `exists_qroot`), `refer/iut/Iut/Cor312/ThetaData/GlobalField.lean:144-146` (`SixTorsionRational`), and `refer/iut/Iut/Concrete/ThetaLocalConstruct/Roots.lean`; assembles the rank-two `ell`-torsion localization, six-torsion-to-four-points derivation, local Tate quotient root-class construction, square-root correction, and `2*ell` q-root source. Given `SixTorsionRational`, a rank-two `ell`-torsion basis over `Kt`, a Tate quotient uniformization at each bad-place completion, odd positive `ell`, and equality of each local Tate parameter with the canonical completion image, it derives local `ell²` bounds and square roots before calling the q-root assembler. It removes the independent global `E[2]` cardinality-bound input from this constructor. It still does not construct the rationality premise from `InitialThetaData`, the torsion basis, quotient uniformizations, `TateFamily`, `V_p^oss`, or a 3.12 model |
| `IUT-COR312-TORSION-RATIONALITY` | `iutGaloisPointMap`, `iutGaloisTorsionEquiv`, `iutGaloisTorsionLinearAction`, `iutTorsionBasisLinearEquiv`, `iutTorsionRepresentationOfBasis`, `iutTorsionRepresentationOfBasis_spec`, `IutTorsionRepresentationData.ofBasis`, `IutTorsionRepresentationData.representation`, `IutTorsionRepresentationData.representation_spec`, `IutTorsionRepresentationData.galoisPoint_eq_of_mem_kernel`, `exists_baseChangeToClosure_eq`, `torsionEquiv`, `basisOverTorsionField`, `card_torsionOverTorsionField`, `toGlobalTorsionBasis` | `ArithmeticTeichmullerSpaces/Act1Scene1/IutTorsionRationality.lean` | `iut`: `refer/iut/Iut/Anabelian/Torsion.lean:55-108` and `refer/iut/Iut/Cor312/ThetaData/AdmissiblePrime.lean:110-140`; derives the additive and `ZMod ell`-linear Galois action on Weierstrass torsion points, conjugates it through the chosen rank-two basis to a `GL₂(ZMod ell)` representation, and proves its action law. The local data structure now takes only the algebraic closure and torsion basis; the representation and its characterizing law are derived. The basis remains explicit. The fixed-field descent does not construct full `AdmissiblePrimeData` or a real `InitialThetaData`/`TateFamily` instance |
| `IUT-COR312-TORSION-FIELD-FINITE` | `IutTorsionRepresentationData.isGalois_torsionField`, `finiteDimensional_torsionField`, `numberField_torsionField` | `ArithmeticTeichmullerSpaces/Act1Scene1/IutTorsionRationality.lean` | `iut`: `refer/iut/Iut/Anabelian/Torsion.lean:114-115` and `refer/iut/Iut/Cor312/ThetaData/LocalConditions.lean:68-105`; adapts the fixed-field Galois/finite-extension argument. The finite-extension and number-field theorems now consume openness derived by `representation_ker_isOpen` from the genuine action on an algebraic torsion basis, instead of requiring an external `ker_isOpen`; they still do not construct full `AdmissiblePrimeData`/`InitialThetaData` |
| `IUT-COR312-TORSION-KERNEL-OPEN` | `IutTorsionRepresentationData.representation_ker_isOpen` | `ArithmeticTeichmullerSpaces/Act1Scene1/IutTorsionRationality.lean` | `iut`: `refer/iut/Iut/Cor312/ThetaData/AdmissiblePrime.lean:43-45,127-139` records kernel openness as the continuity condition on the representation; the reference structure takes that condition as a field. The local proof derives it from the explicit torsion basis and the now-derived genuine action law: the four coordinates of two basis points generate a finite extension, its open fixing subgroup fixes both basis points, and the representation law makes each matrix column standard. Uses Mathlib Krull-topology stabilizer openness and finite-adjoin results. This does not construct the actual torsion basis, `AdmissiblePrimeData`, or its prime/local fields |
| `IUT-COR312-ADMISSIBLE-PRIME-QROOT-SOURCE` | `IutAdmissiblePrimeTorsionData`, `representationData`, `ofAdmissiblePrimeData`, `representation_eq_admissiblePrime`, `torsionField_eq_admissiblePrime`, `ell_pos`, `ell_odd`, `torsionField`, `toGlobalTorsionBasis`, `IutTorsionQRootSource.ofOverBaseBadWithCanonicalCompletionMap_ofAdmissiblePrimeAndSixTorsion` | `ArithmeticTeichmullerSpaces/Act1Scene1/IutTorsionRationality.lean` | Exact projection of `iut`: `refer/iut/Iut/Cor312/ThetaData/AdmissiblePrime.lean:110-140` (`ell_prime`, `five_le`, `torsionBasis`, `rep`, `rep_spec`, and the fixed `torsionField`) and `GlobalField.lean:144-146,166-175` (`SixTorsionRational`, global-data field); reuses the local fixed-field descent adapted from `refer/iut/Iut/Anabelian/Torsion.lean`. `ofAdmissiblePrimeData` projects the actual prime and chosen basis, and takes the algebraic closure explicitly (available from `InitialThetaData`). `representation_eq_admissiblePrime` proves the basis-derived matrix action equals IUT's characterized `rep` by evaluating on the inverse images of standard basis vectors; `torsionField_eq_admissiblePrime` then identifies their fixed fields. The q-root assembler no longer accepts an unrelated torsion field or detached global basis. `SixTorsionRational`, each completion's Tate quotient, and equality of the local Tate parameter with the canonical completion image remain explicit. This projection does not construct full `InitialThetaData`, `TateFamily`, `V_p^oss`, or a 3.12 model |
| `IUT-COR312-QROOT-ORDP` | `IutTorsionQRootSource.canonical_qroot_ordp_eq` | `ArithmeticTeichmullerSpaces/Act1Scene1/IutCompletionSource.lean` | `iut`: `refer/iut/Iut/Concrete/ThetaLocalConstruct/Data.lean:281-302` (`ordp_qrootOf`) together with `Concrete/ThetaLocalConstruct/Ordp.lean:106-131`; consumes an explicit Tate valuation law `v(t_w)=exp(-qOrder(w))`, the canonical completion map, and the q-root power equation to derive `ordp(q_v)=qOrder(w)/(2*ell*ramIdx(w))`. The Tate valuation law, q-root, and real IUT carriers remain explicit Scene1 inputs |
| `IUT-COR312-QROOT-WEIGHTED-ACCOUNTING` | `IutTorsionQRootSource.canonical_qroot_weighted_sum` | `ArithmeticTeichmullerSpaces/Act1Scene1/IutQRootAccounting.lean` | `iut`: `refer/iut/Iut/Concrete/ThetaLocalConstruct/Data.lean:339-376` (`sum_weight_ordp_qroot`); extends the canonical q-root order function by zero away from the over-locus and consumes `Arithmetic.sum_placeWeight_mul`. The base support, q-order coefficient law, Tate valuation law, q-root power equation, and finite carrier remain explicit; the theorem does not identify the carrier with `V_p^oss` or construct theta-volume |
| `IUT-COR312-TATE-VALUATION` | `iutCompletionOrderZ`, `iutCompletionOrderZ_norm_eq`, `iutCompletionOrderZ_pos`, `iutCompletionUniformizerQOrder`, `iutCompletionUniformizerQOrder_norm_eq`, `iutCompletionQOrder`, `iutCompletionQOrder_pos`, `iutCompletionQOrder_valued`, `iutCompletionNorm_eq_uniformizer_pow_qOrder`, `iutCompletionQOrder_eq_of_norm_eq_uniformizer_pow`, `IutBaseQPilotSource.qOrder`, `IutBaseQPilotSource.uniformizerQOrder`, `IutCompletionTateValuation.orderedQOrder`, `IutCompletionTateValuation.completionQOrder_eq_orderNat`, `IutCompletionTateValuation.ofIutNormalizedOrder`, `IutCompletionTateValuation.ofIutNormalizedOrder_order_eq`, `IutCompletionTateValuation.qOrder_coprime`, `IutCompletionTateValuation.norm_eq_pow_order`, `IutCompletionTateValuation.valued_tateParameter_eq_exp_neg_order`, `IutTorsionQRootSource.canonical_qroot_ordp_eq_of_tateValuation`, `IutTorsionQRootSource.canonical_qroot_weighted_sum_of_tateValuation` | `ArithmeticTeichmullerSpaces/Act1Scene1/FieldOrientationAudit.lean`, `IutTateValuation.lean` | `iut`: `refer/iut/Iut/Cor312/ThetaData/AdmissiblePrime.lean:161-181` (`q_order_coprime`, `qOrder`, `qOrder_pos`), `refer/iut/Iut/Concrete/ThetaLocalConstruct/Ordp.lean:286-355` (`valued_eq_of_isUniformizer`, `valued_tateParameter_q`), `refer/iut/.lake/packages/tate-curves-theta/TateCurvesTheta/QParameter/Basic.lean:50-79` (`TateParameter.norm_lt_one`, positive norm/order), and `QParameter/NormalizedOrder.lean:98-177` (`orderZ`, `toOrdered`, `norm_q_eq_pow_orderNat`, `PrimeToOrder`); local valuation/norm laws use `Prologue/Arithmetic/Basic.lean`. This ports IUT's `orderZ` choice from the uniformizer generation property and its positive conversion to `orderNat`; the natural-power norm law is now derived rather than stored as a source field. The S1.113 constructor accepts the source `orderNat` with its norm power law and `q_order_coprime` certificate, proves it equals the valuation-derived `IutBaseQPilotSource.qOrder`, and transfers coprimality to that derived order. `IutQPilotSource.toCompletionTateValuation` now delegates to this constructor instead of duplicating the order-equality and coprimality proof. A real source must still identify `AdmissiblePrimeData.tate` with `B.tateParameter` in the same completion and instantiate the `toOrdered` norm law and `q_order_coprime` certificate from the actual admissible-prime data. No real `InitialThetaData`, `TateFamily`, q-root family, `V_p^oss`, or theta-volume model is constructed |
| `IUT-COR312-Q-PILOT-DEGREE-NORMALIZATION` | `Corollary312DegreeNormalizedSourceQFactor`, `Corollary312RawQNormDegreeNormalization`, `degreeNormalizedSourceQFactor_log_eq_raw_div_degree`, `Corollary312QPilotData.normalizedLogTerm_eq_degreeNormalizedSourceQFactorLog` | `ArithmeticTeichmullerSpaces/Act1Scene1/QNormDegreeBridge.lean` | candidate Scene1/Derived adapter: proves the raw-q-factor logarithm is divided by `[K:ℚ]` and converts the q-pilot term under the explicit raw uniformizer/residue-degree law; the raw uniformizer law and a real `InitialThetaData/TateFamily` instance remain open, and the adapter does not replace the current target q-factor |
| `IUT-COR312-Q-PILOT-DEGREE-ACCOUNTING` | `Corollary312DegreeNormalizedGroupedSourceQFactor`, `Corollary312DegreeNormalizedSourceQLogSum`, `Corollary312QPilotSourceIndexBridge.absLogQ_eq_degreeNormalizedSourceQLogSum` | `ArithmeticTeichmullerSpaces/Act1Scene1/QPilotDegreeAccountingBridge.lean` | Scene1/Derived global finite-sum consumer for the degree adapter; transports `iut`'s `QPilotData.absLogQ` through the existing source-index equivalence to the degree-normalized grouped q-family. It leaves the raw target sum unchanged; the uniformizer law, real source model, and final raw/normalized target choice remain open |
| `IUT-COR312-Q-PILOT-NORMALIZATION-AUDIT` | `Corollary312QPilotNormalizationAudit.finrank_eq_one_of_raw_and_weighted_normalization`, `Corollary312QPilotNormalizationAudit.weighted_normalization_of_raw_normalization_of_finrank_eq_one` | `ArithmeticTeichmullerSpaces/Act1Scene1/QPilotNormalizationAudit.lean` | Scene1/Derived incompatibility audit. Combining the raw completion norm law `-log(norm(π_w)) = inertDeg(w) * log(residueChar(w))` with the weighted q-pilot law and `qPilotWeight = inertDeg(w)/[K:ℚ]` forces `Module.finrank ℚ K = 1` at any bad place. Conversely, under the explicit degree-one condition, the raw law constructs the weighted normalization contract. These theorems add no Prologue/Core assumption and isolate the only degree in which both contracts can be consumed; the general degree-normalized route and raw target remain separate pending statement freeze |
| `IUT-COR312-INITIAL-THETA-TATEJ-IDENTIFICATION` | `IutQPilotSource.initialThetaParameter_eq_of_tateJ`, `IutQPilotSource.ofInitialThetaData` | `ArithmeticTeichmullerSpaces/Act1Scene1/IutAdmissiblePrimeSource.lean` | `iut`: `refer/iut/Iut/Cor312/ThetaData/AdmissiblePrime.lean:150-152` provides `AdmissiblePrimeData.tateJ_eq`; `refer/iut/.lake/packages/tate-curves-theta/TateCurvesTheta/QParameter/JParametrization.lean:376` provides `TateParameter.tateJ_injective`. Given the explicit link-side condition that its Tate parameter has `j` equal to the embedded `D.E.j`, the theorem derives equality with the actual `D.prime.tate` q-parameter. The link-side `j` identity, `hPlaces`, `hEll`, and `QNormTateCompatibility` remain explicit source obligations; this does not construct a real q-pilot model or close the 3.12 statement |
| `IUT-COR312-TATE-FAMILY-QROOT-ADAPTER` | `IutTateQuotientUniformization.ofTateStructure`, `IutTorsionQRootSource.ofTateFamily`, `iutInitialThetaTateFamily_badPlace`, `iutInitialThetaTateFamily_q_eq_baseParameter`, `IutTorsionQRootSource.ofInitialThetaData`, `IutTorsionQRootSource.ofInitialThetaDataOfQPilotBadPlaceFiniteness` | `ArithmeticTeichmullerSpaces/Act1Scene1/IutTateFamilyQRootAdapter.lean` | `iut`: `refer/iut/Iut/Cor312/ThetaData/Basic.lean`, `GlobalField.lean`, `AdmissiblePrime.lean`, `TateStructure.lean`, and `TateFamily.lean`; the completion comparison proof is ported from `refer/iut/Iut/Concrete/ThetaLocalConstruct/TateCompat.lean` and `EmbedCompletion.lean`. Projects the actual Tate q parameter, quotient uniformization, six-torsion rationality, admissible prime and torsion basis. The canonical constructor uses the `bad_finite` field type of IUT `QPilotInputs` and proves local Tate-family q equals the embedded admissible-prime q using the IUT `tateJ_eq` identity, naturality of the Tate curve j-invariant under completion embedding, and injectivity of the Tate-parameter j map. The generic constructor still accepts a q-parameter equality explicitly. Link-place carrier equality and link-side j identity remain explicit; this does not construct the other `InitialThetaData` sources, `V_p^oss`, or a 3.12 model |
| `IUT-COR312-INITIAL-THETA-QROOT-ACCOUNTING` | `IutCompletionTateValuation.ofInitialThetaData`, `IutCompletionTateValuation.ofInitialThetaData_order_eq`, `IutCompletionTateValuation.base_qOrder_eq_initialTheta_qOrder`, `IutCompletionTateValuation.completion_qOrder_eq_initialTheta_qOrder`, `IutTorsionQRootSource.ofInitialThetaDataFromGlobal`, `IutTorsionQRootSource.canonical_qroot_weighted_sum_of_initialThetaData` | `ArithmeticTeichmullerSpaces/Act1Scene1/IutInitialThetaQRootAccounting.lean` | `iut`: `refer/iut/Iut/Concrete/ThetaLocalConstruct/Data.lean:318-372` (`thetaLocalData`, `sum_weight_ordp_qroot`) and `refer/iut/Iut/Cor312/ThetaData/AdmissiblePrime.lean:157-181` (`unif`, `unif_isUniformizer`, `q_order_coprime`, `qOrder`). From actual `InitialThetaData.prime`, constructs the completion valuation using its chosen uniformizer and normalized q-order, proves the order agrees with the project's completion-derived order, and exposes the completion q-order equals the actual admissible-prime q-order at every actual bad place. It also constructs the real q-root source using the finiteness theorem derived from that `InitialThetaData`. The weighted accounting theorem no longer takes a separate bad-place finiteness input; it still takes a finite-place carrier equal to the IUT bad-place set and a residue-prime fiber. It does not identify that carrier with Scene1 link places or `V_p^oss`, settle raw versus degree-normalized q-factors, or construct theta-volume/3.12 data |
| `IUT-COR312-INITIAL-THETA-BAD-SUPPORT` | `IutOddMultiplicativeSupport`, `IutOddMultiplicativeModSupport`, `iutInitialThetaHasMultiplicativeReduction_iff_not_jValLEOne`, `mem_iutOddMultiplicativeModSupport_of_mem_support`, `iutInitialThetaVBad_subset_oddMultiplicativeModSupport`, `iutOddMultiplicativeSupport_eq_badPlacesOver_modSupport`, `iutBadPlacesOver_subset_oddMultiplicativeSupport` | `ArithmeticTeichmullerSpaces/Act1Scene1/IutInitialThetaBadSupport.lean` | `iut`: `refer/iut/Iut/Cor312/ThetaData/GlobalField.lean` (`badPlacesOver`, `bad_odd`, `bad_multiplicative`), `PlaceUnder.lean` (`placeUnder`, `liesOver_placeUnder`), `PlacesOver.lean` (`FinitePlace.exists_liesOver`), `Tripod/CyclicTorsion.lean` (`EllipticCurveData.VBadOdd`); valuation transfer uses current Mathlib `NumberTheory/RamificationInertia/Valuation.lean`. Ports the canonical odd multiplicative support to the field of moduli, proves its pullback to `F` is exactly the odd multiplicative places, and proves actual `InitialThetaData.VBad` lies in it. It does not prove `VBad` is the full support, select the paper's representatives in `L'`, or identify the support with the Scene1 link carrier or `V_p^oss` from JoshiTeich, *Arithmetic Teichmuller Spaces III*, §§ `ss:theta-data-fixing` and `ss:val-sets-defn` |
| `IUT-COR312-VBAD-ODD-SUPPORT-PORT` | `iutVBadOddModSupportPort`, `iutInitialThetaOddMultiplicativeModSupport_eq_VBadOdd`, `iutInitialThetaVBad_subset_VBadOdd` | `ArithmeticTeichmullerSpaces/Act1Scene1/IutInitialThetaVBadOddPort.lean` | Definition-level port of `iut`: `refer/iut/Iut/Tripod/CyclicTorsion.lean`, `EllipticCurveData.VBadOdd`. The port uses the source's `residueChar ≠ 2` condition and proves it equivalent to the project's `Odd` formulation for prime residue characteristics; actual `InitialThetaData.VBad` is a subset by its `bad_odd` and `bad_multiplicative` fields. Direct import of `Iut.Tripod.CyclicTorsion` is avoided because its current dependency graph contains Mathlib API incompatibilities in `ValuationTransfer`, `GalCompletion`, and `TateStructureTransport`, as well as existing `LogVolume` errors. This does not construct the `L'` representatives or identify `V_p^oss`/the Scene1 link carrier |
| `IUT-COR312-INITIAL-THETA-PLACE-SECTION` | `iutInitialThetaFinitePlaceSection`, `iutInitialThetaFinitePlaceSection_liesOver`, `iutInitialThetaFinitePlaceSection_injective`, `iutInitialThetaOddMultiplicativeSelectedPlaces`, `iutInitialThetaOddMultiplicativeSelectedPlaces_subset_overSupport` | `ArithmeticTeichmullerSpaces/Act1Scene1/IutInitialThetaPlaceSection.lean` | `iut`: `refer/iut/Iut/Cor312/ThetaData/LocalConditions.lean` (`ValuationSection.sectFin`, `sectFin_liesOver`) and `ThetaData/Basic.lean` (`InitialThetaData.localData`); injectivity uses `PlaceUnder.lean` (`placeUnder`, `liesOver_placeUnder`). The actual section maps finite places of `F_mod` into the fixed-field torsion extension `L' = D.prime.torsionField`; its image of the full odd multiplicative support is included in the corresponding over-place carrier. This is the real IUT representative selection, not a proof that its support image equals Joshi–Teich's full `underline V^oss`, the selected `VBad`, or the Scene1 link/q-sum carrier |
| `IUT-COR312-INITIAL-THETA-ODD-SUPPORT-Q-PARAMETER` | `iutInitialThetaOddSupport_j_norm_gt_one`, `iutInitialThetaOddModSupport_finite`, `iutInitialThetaOddSupportOverTorsion_finite`, `iutInitialThetaOddSupportBaseTateParameter`, `iutInitialThetaOddSupportBaseTateParameter_tateJ_eq`, `iutInitialThetaFinitePlaceSection_liesOver_moduli`, `iutInitialThetaOddSupportSelected_q_eq_baseParameter`, `iutInitialThetaOddSupport_q_eq_baseParameter_of_liesOver` | `ArithmeticTeichmullerSpaces/Act1Scene1/IutInitialThetaOddSupportQParameter.lean` | `iut`: `refer/iut/Iut/Tripod/CyclicTorsion.lean` (`EllipticCurveData.VBadOdd`), `refer/iut/Iut/Cor312/ThetaData/PlaceUnder.lean` (`one_lt_valuation_j_of_mult`), and `refer/iut/Iut/Cor312/ThetaData/TateFamilyOfTorsion.lean` (`tateFamilyOfTorsion`); finite support also uses Mathlib `NumberField.FinitePlace.hasFiniteMulSupport`; `TateCurvesTheta` at fixed commit `ca6c2279d3cea0690cdb01328e727118d5485d68`, `TateCurvesTheta/QParameter/JParametrization.lean` (`TateParameter.exists_tateParameter_tateJ_eq`, `TateParameter.tateJ_injective`). For every place in the full odd multiplicative moduli support, constructs a Tate parameter over the base completion from the actual `InitialThetaData` curve's `j`-invariant, proves the support finite, and proves that the Tate-family q parameter at every torsion-field place above it is its completion image, including residue characteristic `ell`. The finiteness theorem transfers only a finite carrier; IUT's `q_order_coprime` remains available only on its selected `VBad`. This is local source data only: it does not identify the section image with paper `underline V^oss`, the Scene1 link/q-sum carrier, or establish global weighted-to-unweighted accounting, theta-volume, or 3.12 |
| `IUT-COR312-INITIAL-THETA-ODD-SUPPORT-QROOT` | `iutInitialThetaOddSupportBase_j_norm_gt_one`, `iutInitialThetaOddMultiplicativeSupport_finite`, `iutInitialThetaOddSupportBaseQPilotSource`, `iutInitialThetaOddSupportBaseQPilotSource_tateJ_eq`, `iutInitialThetaOddSupportBaseTateParameter_eq_admissiblePrime`, `iutInitialThetaOddSupportBaseQPilotSource_tateParameter_eq_admissiblePrime`, `iutInitialThetaOddSupportBaseQPilotSource_qOrder_eq_admissiblePrime`, `iutInitialThetaOddSupportBaseQPilotSource_qOrder_coprime_on_vbad`, `iutInitialThetaOddSupportTateFamily_q_eq_baseParameter`, `iutInitialThetaOddSupportTorsionQRootSource`, `iutInitialThetaOddSupportTorsionQRootSource_qroot_pow_eq_admissiblePrime` | `ArithmeticTeichmullerSpaces/Act1Scene1/IutInitialThetaOddSupportQRoot.lean` | `iut`: `refer/iut/Iut/Tripod/CyclicTorsion.lean` (`EllipticCurveData.VBadOdd`); `Iut/Cor312/ThetaData/AdmissiblePrime.lean` (`tate`, `tateJ_eq`, `unif`, `unif_isUniformizer`, `q_order_coprime`, `qOrder`); `Iut/Cor312/ThetaData/TateFamilyOfTorsion.lean` (`tateFamilyOfTorsion`); `Iut/Concrete/ThetaLocalConstruct/TateCompat.lean` (`TateStructure.t_q_eq_embedCompletion`); the q-root construction pattern in `Iut/Concrete/ThetaLocalConstruct/TateTorsion.lean`; and the project's `TateParameter.tateJ_injective`, completion q-order, and `IutTorsionQRootSource.ofTateFamily`. Constructs a finite base q-pilot carrier on the actual curve's complete odd multiplicative support and assembles its torsion-field q-root source from actual `InitialThetaData`. On the subset `badPlacesOver F E VBad`, proves the selected base Tate parameter equals `AdmissiblePrimeData.tate`, its completion-derived q-order equals the IUT normalized `qOrder`, and `q_order_coprime` transfers to that source. Over a torsion-field place whose chosen base place lies in this subset, identifies the q-root power with the image of the actual admissible-prime q parameter. Coprimality is not extended beyond `VBad`; this does not identify the full support or section image with paper `underline V^oss` or the Scene1 link/q-sum carrier, or establish weighted-to-unweighted accounting, theta-volume, or 3.12 |
| `IUT-COR312-INITIAL-THETA-SELECTED-QROOT` | `iutInitialThetaOddSupportSelectedQRootPlace`, `iutInitialThetaOddSupportSelectedQRootPlace_qroot_pow_eq_sectionTate`, `iutInitialThetaOddSupportSelectedQRootPlace_ordp_eq_baseQOrder` | `ArithmeticTeichmullerSpaces/Act1Scene1/IutInitialThetaSelectedQRoot.lean` | `iut` at reference commit `d9465c111ec4073709f67e9fccec7e3eb374a816`: `refer/iut/Iut/Cor312/ThetaData/LocalConditions.lean` (`ValuationSection.sectFin`, `sectFin_liesOver`), `refer/iut/Iut/Tripod/CyclicTorsion.lean` (`EllipticCurveData.VBadOdd`), and `refer/iut/Iut/Cor312/ThetaData/TateFamilyOfTorsion.lean` (`tateFamilyOfTorsion`); composes the project's actual `InitialThetaData` section, full-support q-root source, and Tate-family q comparison. The selected representatives' q-root powers equal the actual section Tate parameter; the IUT `canonical_qroot_ordp_eq` is then specialized to express their arithmetic valuation in terms of the contracted base-field q-order and its ramification index. This does not identify the section image with paper `underline V^oss` or the Scene1 link/q-sum carrier, nor derive weighted-to-unweighted accounting or theta-volume/3.12 data |
| `IUT-COR312-INITIAL-THETA-VOSS` | `iutInitialThetaOddTateSectionPlaces`, `iutInitialThetaOddTateSectionPlaces_eq_selectedSupport` | `ArithmeticTeichmullerSpaces/Act1Scene1/IutInitialThetaVoss.lean` | `iut` at reference commit `d9465c111ec4073709f67e9fccec7e3eb374a816`: `refer/iut/Iut/Cor312/ThetaData/LocalConditions.lean` (`ValuationSection.sectFin`, `sectFin_liesOver`), `refer/iut/Iut/Tripod/CyclicTorsion.lean` (`EllipticCurveData.VBadOdd`), and `refer/iut/Iut/Cor312/ThetaData/TateFamilyOfTorsion.lean` (`tateFamilyOfTorsion`); local Tate criterion from JoshiTeich, *Arithmetic Teichmuller Spaces III*, §§ `ss:theta-data-fixing2`, `ss:val-sets-defn`. Identifies the actual section-image places with odd residue characteristic that carry the corresponding local Tate structure as exactly the image of the full odd multiplicative moduli support. This concerns the formal section and its Tate family; it does not identify the image with the paper's independently defined `underline V^oss`, the Scene1 link/q-sum carrier, or prove q-sum accounting |
| `IUT-COR312-INITIAL-THETA-BAD-FINITENESS` | `iutInitialThetaBadPlacesOver_finite`, `IutBaseQPilotSource.ofInitialThetaData` | `ArithmeticTeichmullerSpaces/Act1Scene1/IutInitialThetaBadPlaceFiniteness.lean` | `iut`: the proof pattern is ported from `refer/iut/Iut/Concrete/CurveArithmeticProved.lean` (`EllipticCurveData.badAll_finite`), using `refer/iut/Iut/Cor312/ThetaData/GlobalField.lean` (`badPlacesOver`, `bad_multiplicative`) and `PlaceUnder.lean` (`one_lt_valuation_j_of_mult`); finite `j`-support uses Mathlib `NumberField.FinitePlace.hasFiniteMulSupport`. From actual `InitialThetaData.global.bad_multiplicative`, derives finiteness of IUT `badPlacesOver` and uses it to build the base q-pilot source. This proves finiteness only; it does not identify `VBad` with the complete odd multiplicative support, Scene1 link places, or `V_p^oss` |
| `IUT-COR312-INITIAL-THETA-ADELIC-LINK` | `iutInitialThetaTateParameterData`, `iutInitialThetaTateParameterData_laws`, `iutInitialThetaTateParameterData_places_eq`, `AdelicThetaLinkData.ofInitialThetaData`, `iutInitialThetaLink_places_eq_badPlacesOver`, `iutInitialThetaLink_parameter_eq_prime_tate`, `iutInitialThetaLink_qNormTateCompatibility`, `iutInitialThetaLink_tateParameter_j_eq` | `ArithmeticTeichmullerSpaces/Act1Scene1/IutInitialThetaLinkSource.lean` | `iut`: `refer/iut/Iut/Cor312/ThetaData/Basic.lean` (`InitialThetaData.prime`), `AdmissiblePrime.lean` (`tate`, `tateJ_eq`), and `GlobalField.lean` (`badPlacesOver`, `bad_nonempty`); finiteness and finite-place enumeration use `IUT-COR312-INITIAL-THETA-BAD-FINITENESS`. Builds the link carrier, local Tate parameter, and norm from the actual admissible-prime fields; proves nonempty Tate laws, the exact `badPlacesOver` carrier, and the explicit equality between the canonical link parameter and the actual admissible-prime q parameter. It also proves q-norm/Tate compatibility through `AdelicThetaLinkData.ofTateParameters` and the local Tate `j` identity from `tateJ_eq`. Theta, packet/hull, height, ramification, volume, and all other link fields remain explicit. It does not identify an independently supplied Scene1 link with this canonical IUT-derived link or construct a complete Scene1 model |
| `IUT-COR312-INITIAL-THETA-CANONICAL-QPILOT-PAPER-BRIDGE` | `IutQPilotSource.absLogQ_eq_weightedPaperNormalizedSourceQFactorLogSum_ofCanonicalInitialThetaLink`, `IutQPilotSource.absLogQ_eq_degreeNormalizedSourceQFactorLogSum_ofCanonicalInitialThetaLink`, `IutQPilotSource.qOrder_eq_initialTheta_qOrder_ofCanonicalInitialThetaLink` | `ArithmeticTeichmullerSpaces/Act1Scene1/IutInitialThetaCanonicalQPilotPaperBridge.lean` | Given a Scene1 link equal to the canonical link from actual `InitialThetaData`, transports the source q-order to the actual admissible-prime q-order and keeps the weighted paper-normalized and degree-normalized q-log presentations explicit. The result still requires the canonical link equality and target-side Scene1 accounting; it does not identify the carrier with paper `L'` representatives, remove q-pilot weights, or construct theta-volume/3.12 data |
| `IUT-COR312-INITIAL-THETA-FIELD-ORIENTATION` | `IutFieldOrientationAudit.ofInitialThetaTorsionTateFamily` | `ArithmeticTeichmullerSpaces/Act1Scene1/IutInitialThetaFieldOrientation.lean` | `iut`: `refer/iut/Iut/Cor312/ThetaData/TateFamilyOfTorsion.lean`, `AdmissiblePrime.lean`, and `Concrete/ThetaLocalConstruct/EmbedCompletion.lean`; reconstructs the actual base q-pilot and torsion q-root source at the target `ell`, using the explicit `T.ell = D.prime.ℓ` equality only for the root exponent. For a target link explicitly equal to `AdelicThetaLinkData.ofInitialThetaTorsionTateFamily`, proves the field-orientation audit's torsion carrier and completion-parameter fields from the actual q-root/Tate-family equality. The target link equality and prime-index alignment remain explicit; this does not identify the carrier with paper `V_p^oss`, settle q-factor normalization, or construct theta-volume/3.12 |
| `IUT-COR312-INITIAL-THETA-SELECTED-QROOT-PLACES` | `iutInitialThetaOddSupportSelectedQRootPlaces`, `iutInitialThetaOddSupportSelectedQRootPlace_val_eq_section`, `iutInitialThetaOddSupportSelectedQRootPlaces_eq_oddTateSectionPlaces`, `iutInitialThetaOddSupportSelectedQRootPlaces_finite` | `ArithmeticTeichmullerSpaces/Act1Scene1/IutInitialThetaSelectedQRoot.lean` | `iut` at reference commit `d9465c111ec4073709f67e9fccec7e3eb374a816`: actual section `ValuationSection.sectFin` and odd multiplicative support; Joshi–Teich, *Arithmetic Teichmuller Spaces III*, `ss:theta-data-fixing2` and `ss:val-sets-defn` for the local Tate locus. Identifies the underlying finite-place set of section-selected q-root representatives with `iutInitialThetaOddTateSectionPlaces`, then proves it finite from the finite odd multiplicative support on the moduli field. This is an equality with the actual section/Tate locus only; it does not identify that set with the paper's `underline V^oss` or the Scene1 link/q-sum carrier, nor prove weighted-to-unweighted accounting or 3.12 |
| `JT-ATS-V1-SCENE2-BOUNDARY` | `Act1Scene2.Scene2Input` | `ArithmeticTeichmullerSpaces/Act1Scene2/Boundary.lean` | D-boundary declaration; post-3.12 propositions are explicit slots only; no bridge theorem or `abc` result |
| `JT-ATS-AUDIT-OBLIGATIONS` | `registeredSourceIds`, constructor declaration and axiom checks | `ArithmeticTeichmullerSpaces/Prologue/Obligations/Audit.lean` | D-audit entry point; checks all four named `sorry` constructors and exposes their expected `sorryAx` dependencies without importing them into public interfaces |
| `JT-ATS-AUDIT-FIELD-COVERAGE` | field-level projection checks | `ArithmeticTeichmullerSpaces/Prologue/Audit/FieldCoverage.lean` | D-audit entry point; every public carrier and contract projection is checked against the grouped source mapping below |
| `JT-ATS-AUDIT-MODEL-COVERAGE` | satisfying/violating model matrix and arithmetic model obligations | `ArithmeticTeichmullerSpaces/Prologue/Audit/ModelCoverage.lean` | D-audit entry point; checks ten compiled interface pairs and three explicit Type-level model obligations |
| `JT-ATS-CANDIDATE-FROBENIUS-SQUARE-NORM` | `Candidate.FrobeniusSquareNormLaw` | `ArithmeticTeichmullerSpaces/Prologue/Candidate/FrobeniusSquare.lean` | `JoshiTeich: refer/JoshiTeich/index-Arithmetic Teichmuller Spaces 3.md`, `th:adelic-theta-link` 1139-1166; rejected stronger reinterpretation of the paper's `j^2` valuation scaling |
| `JT-ATS-AUDIT-REJECT-FROBENIUS-SQUARE` | theta norm collapse, zero log-volume consequence, and nonempty packet/hull contradiction under the rejected candidate | `ArithmeticTeichmullerSpaces/Prologue/Audit/JointConsistency.lean` | `mathlib` `Data/Fintype/Lattice.lean` (`Finite.exists_max`, `Finite.exists_min`); contract semantics from `JoshiTeich: refer/JoshiTeich/index-Arithmetic Teichmuller Spaces 3.md`, `th:adelic-theta-link` 1139-1166, `def:additive-theta-pilot-object` 1492-1502, `le:volume-lemma3` 3576-3583, `cor:cor312` 3647-3650; rejection audit only |

| `IUT-COR312-ODD-SUPPORT-TATE-BASE-CHANGE` | `iutInitialThetaOddSupportBaseTateParameter_q_eq_of_liesOver` | `ArithmeticTeichmullerSpaces/Act1Scene1/IutInitialThetaOddSupportBaseChange.lean` | `iut`: `refer/iut/Iut/Tripod/CyclicTorsion.lean` (`VBadOdd`) and `Iut/Cor312/ThetaData/TateFamilyOfTorsion.lean`; completion transport follows `Iut/Concrete/ThetaLocalConstruct/EmbedCompletion.lean` and `TateCompat.lean`, ported in `IutTateParameterCompletion.lean`. `TateParameter.tateJ_injective` is from `TateCurvesTheta` at fixed commit `ca6c2279d3cea0690cdb01328e727118d5485d68`, `TateCurvesTheta/QParameter/JParametrization.lean`. For any moduli place in the full odd multiplicative support and any place of `F` lying over it, proves the q-parameter constructed over the `F`-completion is the completion image of the q-parameter over the moduli-field completion. This aligns local Tate parameters across the field extension; it does not identify their global sums, the IUT-selected `VBad` with full support, the paper's `underline V^oss` with the Scene1 carrier, or prove 3.12 |
| `IUT-COR312-ODD-SUPPORT-Q-ORDER-BASE-CHANGE` | `iutCompletionQOrder_eq_relRamIdx_mul_of_eq_embed`, `iutInitialThetaOddSupportTateFamily_qOrder_eq_relRamIdx_mul` | `ArithmeticTeichmullerSpaces/Act1Scene1/IutInitialThetaOddSupportQOrderBaseChange.lean` | `iut`: completion valuation transport from `refer/iut/Iut/Concrete/ThetaLocalConstruct/EmbedCompletion.lean` (`valued_embedCompletion`) and the local q-order/Tate-family fields from `refer/iut/Iut/Cor312/ThetaData/TateFamilyOfTorsion.lean`; completion order and relative ramification use local ports in `IutCompletionSource.lean` and `IutQSourceContract.lean`. Proves that the completion q-order of the actual Tate-family parameter over a torsion-field place is the base q-order times the relative ramification index. This is a local order scaling formula; it does not identify the paper's selected `L'`-place sum with the weighted sum over `F`-places |
| `IUT-COR312-ODD-SUPPORT-QROOT-ACCOUNTING` | `iutInitialThetaOddSupportWeightedFiber`, `iutInitialThetaOddSupportWeightedFiber_eq_baseQOrder` | `ArithmeticTeichmullerSpaces/Act1Scene1/IutInitialThetaOddSupportQRootAccounting.lean` | `iut`: `refer/iut/Iut/Concrete/ThetaLocalConstruct/Data.lean` (`ThetaLocalData.sum_weight_ordp_qroot`) and `Ordp.lean` (`sum_localDeg_liesOver`, completion valuation normalization). Specializes finite-place weighted q-root accounting to actual `InitialThetaData` on the complete odd multiplicative support, and gives the residue-characteristic fiber as the base `qPilotWeight * qOrder / (2*ell)` sum. It does not identify this complete support with the paper's selected `L'` representatives or `underline V^oss`, and does not remove the weights to obtain the paper's unweighted sum |
| `IUT-COR312-SELECTED-QROOT-PAPER-NORMALIZATION` | `iutInitialThetaOddSupportSelectedQRootPlace_ramIdx_mul_ordp_eq_sectionQOrder` | `ArithmeticTeichmullerSpaces/Act1Scene1/IutInitialThetaSelectedQRoot.lean` | `iut`: actual Initial Theta section, torsion Tate family, q-root power identity, and completion valuation; `JoshiTeich: refer/JoshiTeich/index-Arithmetic Teichmuller Spaces 3.md`, `th:moccor-Mochizuki-form2` (1747-1754) and `cor:cor312` (3647-3650), including `|uniformizer|_{C_p}=p^{-1}`. At each actual section-selected odd-support place, proves that the local q-root's `ordp`, multiplied by the absolute ramification index of the torsion-field place, equals the section Tate q-order divided by `2*ell`. This identifies the local normalization at that representative; it does not identify the representative set with `underline V^oss` or prove the global unweighted sum |
| `IUT-COR312-INITIAL-THETA-SECTION-LINK` | `iutInitialThetaOddTateSectionTateStructure`, `iutInitialThetaOddTateSectionTateParameterData`, `iutInitialThetaOddTateSectionTateParameterData_parameter_eq`, `iutInitialThetaOddTateSectionTateParameterData_laws`, `AdelicThetaLinkData.ofInitialThetaOddTateSection`, `iutInitialThetaOddTateSectionLink_places_eq_oddTateSectionPlaces`, `iutInitialThetaOddTateSectionLink_places_eq_sectionVoss`, `iutInitialThetaOddTateSectionLink_qNormTateCompatibility` | `ArithmeticTeichmullerSpaces/Act1Scene1/IutInitialThetaSectionLink.lean`; `iutInitialThetaSectionRepresentatives`, `iutInitialThetaOddSemistablePlaces`, `iutInitialThetaSectionVoss`, `iutInitialThetaOddTateSectionPlaces_eq_sectionVoss` in `ArithmeticTeichmullerSpaces/Act1Scene1/IutInitialThetaVoss.lean` | `iut` at `refer/iut` commit `d9465c111ec4073709f67e9fccec7e3eb374a816`: `Iut/Cor312/ThetaData/LocalConditions.lean` (`ValuationSection.sectFin`), `Iut/Cor312/ThetaData/TateFamilyOfTorsion.lean` (`tateFamilyOfTorsion`), and actual `InitialThetaData.localData`; Joshi–Teich, *Arithmetic Teichmuller Spaces III*, `ss:theta-data-fixing2`, `ss:val-sets-defn`, `cor:cor312`. Builds Tate-parameter data from the local Tate structures at actual section representatives and proves its link carrier is the section range intersected with odd local Tate places, the formal `underline V^oss` instance for this section choice. Theta, packet/hull, height, ramification, and volume inputs remain explicit. This result is specific to the `InitialThetaData` section and local Tate criterion; it does not identify an independently supplied Scene1 link or arbitrary paper representative choice, and does not prove global q-sum accounting or a complete 3.12 model |
| `IUT-COR312-SELECTED-BASE-PLACE-CONTRACTION` | `iutInitialThetaSectionBasePlace`, `iutInitialThetaSectionBasePlace_liesOver`, `iutInitialThetaSectionBasePlace_injective`, `iutInitialThetaOddSupportSelectedBasePlaces`, `iutInitialThetaOddSupportSelectedBasePlaces_finite`, `iutInitialThetaOddSupportSelectedBasePlaces_subset_baseSupport`, `iutInitialThetaOddSupportSelectedQRootPlace_basePlace_eq_sectionBasePlace`, `iutInitialThetaOddSupportSelectedQRootSourcePlaces`, `iutInitialThetaOddSupportSelectedQRootSourcePlaces_finite`, `iutInitialThetaOddSupportSelectedQRootSourcePlaces_basePlace_image_eq` | `ArithmeticTeichmullerSpaces/Act1Scene1/IutInitialThetaSelectedQRoot.lean` | `iut` at `refer/iut` commit `d9465c111ec4073709f67e9fccec7e3eb374a816`: `Iut/Cor312/ThetaData/LocalConditions.lean` (`ValuationSection.sectFin`, `sectFin_liesOver`) and `Iut/Cor312/ThetaData/PlaceUnder.lean` (`placeUnder`); the ported contraction API is recorded under `IUT-COR312-PLACE-UNDER`. Contracts each actual torsion-field section representative to `D.F`, proves it lies over the represented moduli place and that distinct moduli places have distinct contractions, and proves the finite image of odd multiplicative support is included in the actual base q-pilot support. The selected q-root source is then restricted to a finite subtype whose base-place image is exactly the selected contracted base-place set. The q-root source's base place is this contraction. This is a carrier and index-direction result; it does not prove the paper's selected `L'` multiplicity/residue-degree accounting, identify the image with the Scene1 link or `underline V^oss`, remove q-pilot weights, or prove 3.12 |

| `IUT-COR312-SELECTED-QROOT-SOURCE-BASE-EQUIV` | `iutInitialThetaOddSupportSelectedQRootSourcePlaces_basePlace_injective`, `iutInitialThetaOddSupportSelectedQRootSourcePlaces_basePlaceEquiv` | `ArithmeticTeichmullerSpaces/Act1Scene1/IutInitialThetaSelectedQRoot.lean` | `iut` at reference commit `d9465c111ec4073709f67e9fccec7e3eb374a816`: selected section representatives from `Iut/Cor312/ThetaData/LocalConditions.lean` (`ValuationSection.sectFin`), contraction through `Iut/Cor312/ThetaData/PlaceUnder.lean` (`placeUnder`), and the source/base-place structures ported from the IUT q-root construction. Proves the finite selected q-root source subtype maps injectively to the selected contracted base-place subtype, then packages the exact image equality from `IUT-COR312-SELECTED-BASE-PLACE-CONTRACTION` as a canonical `Equiv`. This supplies an index-level no-duplication interface for later multiplicity accounting; it does not identify the subtype with the paper's `L'` representative set, remove residue-degree or q-pilot weights, or prove the unweighted q-sum or 3.12 |

| `IUT-COR312-SELECTED-QROOT-WEIGHTED-FIBER-ACCOUNTING` | `iutInitialThetaOddSupportSelectedQRootSourcePlaces_qPilotWeighted_baseRamIdx_mul_ordp_fiber_eq` | `ArithmeticTeichmullerSpaces/Act1Scene1/IutInitialThetaSelectedQRootAccounting.lean` | Extends `IUT-COR312-SELECTED-QROOT-WEIGHTED-ACCOUNTING` by filtering both finite subtypes at an arbitrary residue characteristic `p`. The source/base-place `Equiv` preserves the residue characteristic, so the selected q-root sum `qPilotWeight * baseRamIdx * ordp(qroot)` on that fiber equals the selected base-place sum `qPilotWeight * qOrder/(2*ell)`. This is the finite-fibre interface for later `(p,w)` indexing; it does not identify the carrier with paper `L'` representatives or `underline V^oss`, remove q-pilot weights, or establish the unweighted paper q-sum |
| `IUT-COR312-SELECTED-QROOT-UNWEIGHTED-FIBER-ACCOUNTING` | `iutInitialThetaOddSupportSelectedQRootSourcePlaces_baseRamIdx_mul_ordp_fiber_eq_unweighted` | `ArithmeticTeichmullerSpaces/Act1Scene1/IutInitialThetaSelectedQRootAccounting.lean` | Uses the same selected source/base-place `Equiv` and residue-characteristic preservation as the weighted fibre theorem, together with the local `baseRamIdx * ordp(qroot) = qOrder/(2*ell)` formula, to obtain the unweighted selected q-root sum on each rational-prime fibre. It remains an identity for the actual section-selected carrier and does not identify paper `L'` representatives, prove representative multiplicities, or close the global paper sum |
| `IUT-COR312-SELECTED-QROOT-UNWEIGHTED-GROUPED-ACCOUNTING` | `iutInitialThetaOddSupportSelectedQRootSourcePlaces_baseRamIdx_mul_ordp_sum_eq_unweighted_residueChar_grouped` | `ArithmeticTeichmullerSpaces/Act1Scene1/IutInitialThetaSelectedQRootAccounting.lean` | Sums the unweighted fibre identity over the finite residue-characteristic image of the selected contracted base-place carrier. The source-side fibre is grouped by the contracted base place, and the base-side fibre by its own residue characteristic, giving the explicit finite `(p,w)` grouped equality for the actual section-selected carrier. It does not identify paper `L'` representatives, prove representative multiplicity, or close the independently supplied Scene1/global paper q-sum |

| `IUT-COR312-SELECTED-QROOT-SOURCE-VOSS-IMAGE` | `iutInitialThetaOddSupportSelectedQRootSourcePlaces_image_eq_sectionVoss` | `ArithmeticTeichmullerSpaces/Act1Scene1/IutInitialThetaSelectedQRootAccounting.lean` | The underlying finite-place image of the selected q-root source subtype is proved equal to `iutInitialThetaSectionVoss`. The proof factors through the selected q-root place set, the actual section's odd Tate locus, and the section-image/odd-semistable definition of `underline V^oss`. This identifies the carrier produced by the actual `InitialThetaData` section with its concrete section Voss carrier; it does not identify an independently supplied Scene1 link or paper representative choice, and does not yet account for representative multiplicity or remove q-pilot weights |

| `IUT-COR312-SELECTED-QROOT-SOURCE-LINK-IMAGE` | `iutInitialThetaOddSupportSelectedQRootSourcePlaces_image_eq_sectionLinkPlaces` | `ArithmeticTeichmullerSpaces/Act1Scene1/IutInitialThetaSelectedQRootLinkAccounting.lean` | Uses the S1.164 source-image-to-`underline V^oss` equality and `iutInitialThetaOddTateSectionLink_places_eq_sectionVoss` to identify the selected q-root source's underlying finite-place image with the `places` carrier of `AdelicThetaLinkData.ofInitialThetaOddTateSection` built from the same `InitialThetaData` section. This is a direct source equality for the canonical section link; it does not identify an independently supplied Scene1 link, paper `L'` representatives, representative multiplicities, or remove q-pilot/residue-degree weights |

| `IUT-COR312-SELECTED-QROOT-SOURCE-LINK-CARDINALITY` | `iutInitialThetaOddSupportSelectedQRootSourcePlaces_card_eq_sectionLinkPlaces_card` | `ArithmeticTeichmullerSpaces/Act1Scene1/IutInitialThetaSelectedQRootLinkAccounting.lean` | Turns the canonical source-image equality into an explicit finite bijection and cardinality equality between selected q-root source places and canonical section-link places. This supplies the finite carrier cardinality needed by later representative multiplicity accounting; it does not prove the paper's independent `L'` choice or remove q-pilot weights. |

| `IUT-COR312-SELECTED-QROOT-PAPER-Q-SUM` | `iutInitialThetaOddSupportSelectedQRootSourcePlaces_sectionLinkEquiv`, `iutInitialThetaOddSupportSelectedQRootSourcePlaces_paperQLogSum_eq_sectionLink_unGrouped`, `iutInitialThetaOddSupportSelectedQRootSourcePlaces_paperQLogSum_eq_sectionLink` | `ArithmeticTeichmullerSpaces/Act1Scene1/IutInitialThetaSelectedQRootPaperQSum.lean` | Combines the selected source/link place-image equality with the actual section Tate-family q-root order formula. It proves a no-duplication equivalence to the canonical section-link places and transports the absolute-ramification-normalized q-root log sum to the link `qOrder/(2*ell)` sum, first as a direct ungrouped finite sum and then grouped by residue characteristic. The link must be built from the same `InitialThetaData`; independent link equality and the analytic theta-volume/transfer bounds remain open |
| `IUT-COR312-PAPER-REPRESENTATIVE-MULTIPLICITY` | `Corollary312QPilotPaperRepresentativeAccounting`, `Corollary312QPilotPaperRepresentativeAccounting.absLogQ_eq_unweightedRepresentativeSum` | `ArithmeticTeichmullerSpaces/Act1Scene1/PaperQRepresentativeAccounting.lean` | Ports the missing finite accounting layer between the IUT q-pilot carrier and the paper's selected representative carrier. Given an explicit source-to-representative map, local paper-term equality, and a unit total q-pilot weight in every representative fiber, proves the weighted q-pilot `absLogQ` equals the unweighted representative sum. The three fields are a Scene1 source obligation; no claim is made that actual `InitialThetaData` or `L'` representatives already provide them |
| `IUT-COR312-PAPER-REPRESENTATIVE-SELECTED-QROOT-BRIDGE` | `Corollary312PaperRepresentativeSectionLinkAccounting`, `Corollary312PaperRepresentativeSectionLinkAccounting.representativeSum_eq_sectionLinkQLogSum`, `Corollary312PaperRepresentativeSectionLinkAccounting.representativeSum_eq_selectedQRootPaperQLogSum` | `ArithmeticTeichmullerSpaces/Act1Scene1/PaperQRepresentativeSelectedQRootBridge.lean` | Adds the remaining finite transport certificate: an equivalence from the paper representative carrier to the canonical section-link places and a term-by-term equality with `qOrder/(2*ell) * log residueChar`. Finite-sum transport then identifies the unweighted representative sum with the selected q-root paper q-sum. The equivalence and term certificate remain Scene1 source obligations; this module does not construct the paper `L'` representatives or assert an independent Scene1 link equality |

| `IUT-COR312-PAPER-REPRESENTATIVE-SELECTED-QROOT-GLOBAL` | `Corollary312PaperRepresentativeSectionLinkAccounting.absLogQ_eq_selectedQRootPaperQLogSum` | `ArithmeticTeichmullerSpaces/Act1Scene1/PaperQRepresentativeSelectedQRootBridge.lean` | Composes `IUT-COR312-PAPER-REPRESENTATIVE-MULTIPLICITY` with `IUT-COR312-PAPER-REPRESENTATIVE-SELECTED-QROOT-BRIDGE`: under the explicit unit-fiber q-pilot weight, representative-to-section-link equivalence, and local term certificates, transports `P.absLogQ` directly to the unweighted selected q-root paper sum. The theorem is a finite accounting bridge; it does not construct the paper representative certificates from `InitialThetaData`, prove theta-volume or transfer bounds, or close Corollary 3.12. |
| `IUT-COR312-PAPER-REPRESENTATIVE-SELECTED-QROOT-SCENE1-ADAPTER` | `Corollary312Scene1QPilotData.rawNormalization`, `Corollary312Scene1QPilotData.absLogQ_eq_selectedQRootPaperQLogSum` | `ArithmeticTeichmullerSpaces/Act1Scene1/AdelicThetaLinkBridge.lean`, `ArithmeticTeichmullerSpaces/Act1Scene1/PaperQRepresentativeSelectedQRootBridge.lean` | Exposes the raw completion norm normalization derived from the same `IutQPilotSource` carrier and consumes it in a Scene1 bundle wrapper for the selected q-root paper sum. Dependent proof arguments are hidden only behind named projections; the representative equivalence, local term certificate, target data, and the paper source remain explicit obligations. |
| `IUT-COR312-SCENE1-QPILOT-DEGREE-NORMALIZED-BUNDLE` | `Corollary312Scene1QPilotData.absLogQ_eq_degreeNormalizedSourceQLogSum` | `ArithmeticTeichmullerSpaces/Act1Scene1/IutInitialThetaScene1QPilotData.lean` | Applies the existing finite source-index bridge to the Scene1 q-pilot bundle using its named raw normalization and derived source-index bridge. This exposes the degree-normalized finite q-family sum for a bundle carrying the actual IUT source adapter; it does not identify that sum with the raw target q-family or close the normalization freeze. |

| `IUT-COR312-SELECTED-QROOT-RESIDUE-ALIGNMENT` | `iutInitialThetaOddSupportSelectedQRootSourcePlace_residueChar_eq_basePlace`, `iutInitialThetaOddSupportSelectedQRootSourcePlace_residueChar_eq_iff` | `ArithmeticTeichmullerSpaces/Act1Scene1/IutInitialThetaSelectedQRootResidue.lean` | Consumes the selected q-root source's `liesOver` field and `Arithmetic.residueChar_eq_of_liesOver` to show that each source place and its contracted base place have the same residue characteristic, then packages the equality as an equivalent `= p` filter. This is an index-alignment fact for later `(p,w)` accounting; it does not prove paper representative multiplicity, remove q-pilot/residue-degree weights, or identify an independent link |
| `IUT-COR312-INITIAL-THETA-SELECTED-FIELD-ORIENTATION` | `iutInitialThetaOddSupportSelectedQRootFinset`, `iutInitialThetaOddSupportSelectedQRootAt`, `iutInitialThetaOddSupportSelectedQRootQRoot`, `iutInitialThetaOddSupportSelectedQRootQRoot_pow_eq_sectionParameter`, `IutFieldOrientationAudit.ofInitialThetaSelectedTateSection` | `ArithmeticTeichmullerSpaces/Act1Scene1/IutInitialThetaSelectedFieldOrientation.lean` | Restricts the actual full-support torsion q-root source to the finite selected section carrier and proves its finite carrier equals the canonical `AdelicThetaLinkData.ofInitialThetaOddTateSection` places. The constructor keeps the base q-pilot on `D.F`, the q-root and completion map on `D.prime.torsionField`, and the `T.ell = D.prime.ℓ` alignment explicit. The selected q-root power equals the section Tate parameter by a source proof from the actual `InitialThetaData` Tate family, so the field-orientation constructor has no detached parameter certificate. It does not identify an independently supplied Scene1 link, prove paper `L'` multiplicity, remove q-pilot weights, or construct theta-volume/3.12 data |

| `IUT-COR312-CANONICAL-QPILOT-DEGREE-NORMALIZED-SUM` | `IutQPilotSource.absLogQ_eq_degreeNormalizedSourceQFactorLogSum_ofCanonicalInitialThetaLink` | `ArithmeticTeichmullerSpaces/Act1Scene1/IutInitialThetaCanonicalQPilotPaperBridge.lean` | For a canonical `InitialThetaData` link, transports the q-pilot `absLogQ` over its finite bad-place carrier to the explicit degree-normalized source q-factor. The result consumes the raw completion-norm certificate and the proved local degree adapter; it keeps the finite source carrier and canonical-link equality explicit. It does not identify this sum with the raw target q-family, construct paper `L'` representatives, or prove theta-volume, transfer bounds, or Corollary 3.12 |
| `IUT-COR312-INITIAL-THETA-SCENE1-QPILOT-DATA` | `Corollary312Scene1QPilotData.ofCanonicalInitialThetaLink`, `Corollary312Scene1QPilotData.cor312_of_canonicalInitialThetaLink_of_degree_one` | `ArithmeticTeichmullerSpaces/Act1Scene1/IutInitialThetaScene1QPilotData.lean` | Given actual `InitialThetaData`, explicit `T.ell = D.prime.ell`, equality of the supplied Scene1 link with `AdelicThetaLinkData.ofInitialThetaData D`, and `Module.finrank ℚ D.F = 1`, assembles the real admissible-prime q-pilot source and its weighted normalization into `Corollary312Scene1QPilotData`, then feeds the existing Scene1 accounting into `Corollary312`. The target volume, packet/hull accounting, paper `L'` representative multiplicity, unweighted `(p,w)` sum, and independent link equality remain source obligations; this does not construct a complete 3.12 model |
| `IUT-COR312-INITIAL-THETA-SCENE1-DEGREE-NORMALIZED-BUNDLE` | `Corollary312Scene1DegreeNormalizedQPilotData`, `Corollary312Scene1DegreeNormalizedQPilotData.ofCanonicalInitialThetaLink`, `Corollary312Scene1DegreeNormalizedQPilotData.absLogQ_eq_degreeNormalizedSourceQLogSum` | `ArithmeticTeichmullerSpaces/Act1Scene1/IutInitialThetaScene1QPilotData.lean` | Packages the actual `InitialThetaData` q-pilot source with its raw completion-norm certificate for the parallel degree-normalized candidate. It removes the general-number-field degree-one requirement from this candidate path and transports its q-pilot `absLogQ` to the degree-normalized finite source sum through the existing grouping bridge. It remains separate from the raw `Corollary312Scene1QPilotData` target and does not identify the normalized sum with the raw target q-family, construct paper `L'` representative multiplicity, prove theta-volume or packet/hull accounting, or close Corollary 3.12 |

| `IUT-COR312-FINITE-WEIGHTED-AVERAGING` | `IutFiniteWeightedAveraging.sum_bound_eval`, `IutFiniteWeightedAveraging.weighted_sum_le_of_pointwise` | `ArithmeticTeichmullerSpaces/Act1Scene1/IutFiniteWeightedAveraging.lean` | Ports the finite product-weight calculation used by `refer/iut/Iut/Concrete/LocalEstimate.lean` (`sum_bound_eval`) and adds its nonnegative pointwise-bound consumer. The local helper identities follow `refer/iut/Iut/Concrete/Invariants.lean` (`sum_prod_tuple_mul_coord`, `sum_prod_tuple_mul_sum`, `sum_prod_tuple_eq_one`). The result is an abstract finite weighted packet/hull interface: it does not construct `InitialThetaData`, `TateFamily`, theta regions, packet/hull carriers, volume accounting, transfer bounds, paper `L'` representatives, or Corollary 3.12. |

| `IUT-COR312-PACKET-HULL-FINITE-AVERAGING` | `IutFiniteWeightedAveraging.packet_weight_sum_le_of_product_local_bound`, `IutFiniteWeightedAveraging.hull_weight_sum_le_of_product_local_bound` | `ArithmeticTeichmullerSpaces/Act1Scene1/IutFiniteWeightedAveraging.lean` | Consumes `PacketHullData.packetWeight` and `hullWeight` through explicit equivalences to finite tuple carriers, product-weight decompositions, and pointwise local bounds, then applies the finite weighted-average transport from `IUT-COR312-FINITE-WEIGHTED-AVERAGING`. This closes the finite packet/hull summation interface only; the tuple equivalences, weight decompositions, local theta-region estimates, real `InitialThetaData/TateFamily` construction, volume transfer, paper representatives, and Corollary 3.12 remain source obligations. |

### 字段级覆盖审计

`FieldCoverage.lean` 使用 Lean projection 名称逐项检查下列字段。每个字段组的语义
来源沿用对应的 declaration-level source-id；该表不把审计检查误记为数学证明。

| source-id | 字段组 | 文件 | 状态 |
| --- | --- | --- | --- |
| `JT-ATS-III-DATA-001` | `ThetaPilotData.index`, `indexFintype`, `value`, `norm`, `scalingIndex`, `frobenius`, `period`, `liftedLog`; `PacketHullData.packet`, `packetFintype`, `packetToPilot`, `packetWeight`, `hull`, `hullFintype`, `hullToPacket`, `hullWeight` | `Prologue/Interfaces/Carriers.lean` | projection audit passed |
| `JT-ATS-III-ARITHMETIC-LINK` | `AdelicThetaLinkData.places`, `qParameter`, `tate`, `theta`, `thetaBase`, `packetHull`, `heightData`, `ramification`, `logVolume`, `processionLength` | `Prologue/Interfaces/Carriers.lean` | projection audit passed |
| `JT-ATS-II5-ARITH-DIVISOR` | `FinitePlaceDivisor.support`, `exponent`, `exponent_ne_zero`; `HeightData.places`, `weight`, `weight_nonneg`, `value`, `value_eq` | `Prologue/Arithmetic/Basic.lean` | projection audit passed |
| `JT-ATS-IV-RAMIFICATION` | `RamificationProfile.conductor`, `different_log`, `conductor_log`, `different_log_nonneg`, `conductor_log_nonneg` | `Prologue/Arithmetic/Basic.lean` | projection audit passed |
| `JT-ATS-PROLOGUE-PERFECTOID` | `UntiltingLaws.one`, `reduction`, `frobenius_scaling`; `FontaineThetaLaws.teichmuller` | `Prologue/Perfectoid/Untilts.lean` | projection audit passed |
| `JT-ATS-PROLOGUE-PERFECTOID-DATA` | `PerfectoidData.untilt`, `theta`; `PerfectoidLaws.untilting`, `theta_compatibility` | `Prologue/Perfectoid/Data.lean` | projection audit passed |
| `JT-ATS-II-TATE-PARAMETER` | `TateParameterData.places`, `parameter`, `norm`; `TateParameterLaws.places_nonempty`, `parameter_nonzero`, `norm_eq`, `norm_pos`, `norm_lt_one` | `Prologue/Theta/Tate.lean` | projection audit passed |
| `JT-ATS-II-THETA-PILOT-SCALING` | `ThetaPilotScalingLaws.base_scalingIndex`, `value_nonzero`, `norm_positive`, `norm_scaling` | `Prologue/Theta/Pilot.lean` | projection audit passed |
| `JT-ATS-III-PERFECTOID-BRIDGE` | `PerfectoidPlaceData.place`, `data`; `PerfectoidPlaceLaws.perfectoid`; `PerfectoidBridgeData.coefficientMap`; `PerfectoidBridgeLaws.place_supported`, `local_laws` | `Prologue/Interfaces/PerfectoidBridge.lean` | projection audit passed |
| `JT-ATS-III-PROLOGUE-INPUT` | `PrologueInputData.link`, `placeData`, `bridge`; `PrologueInputLaws.first_axiom`, `tate_parameter`, `adelic_theta_link`, `perfectoid_bridge` | `Prologue/Interfaces/Input.lean` | projection audit passed |
| `JT-ATS-III-CONTRACT-001` | `FirstAxiom.places_nonempty`, `q_parameter_nonzero`, `q_norm_positive`, `height_nonnegative`, `theta_norm_positive`, `packet_weight_positive`, `hull_weight_positive` | `Prologue/Interfaces/Contracts.lean` | projection audit passed |
| `JT-ATS-III-CONTRACT-002` | `AdelicThetaLink.valuation_scaling`, `theta_scaling`, `period_map`, `normalization` | `Prologue/Interfaces/Contracts.lean` | projection audit passed; rejected candidate norm-square law is tracked separately |
| `JT-ATS-III-CONTRACT-003` | `ThetaLiftLog.log_shell`, `value_nonzero` | `Prologue/Interfaces/Contracts.lean` | projection audit passed |
| `JT-ATS-III-CONTRACT-004` | `PacketCollationHull.packet_supported`, `hull_supported`, `packet_weights_nonzero`, `hull_weights_nonzero` | `Prologue/Interfaces/Contracts.lean` | projection audit passed |
| `JT-ATS-III-CONTRACT-005` | `VolumeTransfer.transferred_volume` | `Prologue/Interfaces/Contracts.lean` | projection audit passed |

### 模型覆盖矩阵

`ModelCoverage.lean` 检查下列满足/违反 witness。`FinitePlaceDivisor`、`HeightData` 和
`RamificationProfile` 将不变量直接放在 Type 的构造字段中，因此登记为明确的模型义务，
不伪造一个不能 inhabit 这些字段的反模型。

| 接口 | 满足模型 | 违反模型 | 状态 |
| --- | --- | --- | --- |
| `FirstAxiom` | `firstAxiom_model` | `firstAxiom_violation` | compiled pair |
| `AdelicThetaLink` | `adelicThetaLink_model` | `adelicThetaLink_violation` | compiled pair |
| `ThetaLiftLog` | `thetaLiftLog_model` | `thetaLiftLog_violation` | compiled pair |
| `PacketCollationHull` | `packetCollationHull_model` | `packetCollationHull_violation` | compiled pair |
| `VolumeTransfer` | `volumeTransfer_model` | `volumeTransfer_violation` | compiled pair |
| `TateParameterLaws` | `auditTateData_laws` | `auditTateData_violation` | compiled pair |
| `ThetaPilotScalingLaws` | `auditScalingTheta_laws` | `zeroScalingTheta_violates_laws` | compiled pair |
| `PerfectoidLaws` | `padicTwo_perfectoid_model` | `zeroPerfectoidData_violates_laws` | compiled pair |
| `PerfectoidBridgeLaws` | `padicTwo_bridge_model` | `zero_bridge_violates_laws` | compiled pair |
| `PrologueInputLaws` | `padicTwo_input_laws` | `badInput_violates_laws` | compiled pair |
| Type-level arithmetic profiles | `auditHeight`, `auditConductor`, `auditRamificationProfile` | constructor obligations | explicit model obligation |

The Prologue boundary does not declare Corollary 3.12.  Its four construction theorems
are kept in `Prologue/Obligations` and are not imported by `Prologue/Interfaces`.

## IUT reference boundary

| `IUT-COR312-INITIAL-THETA-PRIME-TO-SUPPORT` | `iutInitialThetaVBad_residueChar_ne_ell`, `iutInitialThetaBadPlacesOver_residueChar_ne_ell`, `iutInitialThetaBadPlacesOver_exists_residueChar_ne_two_ell`, `iutInitialThetaBadPlacesOver_subset_primeToOddSupport`, `iutInitialThetaOddMultiplicativeSupport_ne_badPlacesOver_of_multiplicative_at_ell`, `iutInitialThetaBadPlacesOver_primeToOddModSupport_eq`, `iutInitialThetaBadPlacesOver_eq_primeToOddSupport_of_VBad_eq`, `iutInitialThetaOddMultiplicativeSupport_eq_badPlacesOver_iff_no_multiplicative_at_ell` | `ArithmeticTeichmullerSpaces/Act1Scene1/IutInitialThetaPrimeToSupport.lean` | 来源为 `refer/iut/Iut/Concrete/Existence.lean` 的 `VBadOf` 与 `badPlacesOver_VBadOf`，文件原提交 `a36b42b9a221e1baaf434bb76c85b3a0dfbf33a7`，参考快照 `07cb1da58f6d428a670dbb5dd6093d428bcbcdd8`。保留原作者和 Apache-2.0 通知；在本地命名空间重新证明，无参考工程依赖。实际 `InitialThetaData.prime.residueChar_coprime` 无条件排除 q-pilot 支撑中的剩余特征 `ell`；最大 prime-to-ell 模数域支撑拉回后恰为完整 odd support 去掉 `ell` 纤维。仅在显式 `VBad` 来源等式下识别实际 carrier；此时完整支撑等式等价于 `ell` 上不存在乘法约化处。有该类处时，S1.200 的等式假设不成立。属于 `Scene1/Derived`，不改变 Prologue-R5，不解决论文代表重数、去权或体积来源。 |
| `IUT-COR312-INITIAL-THETA-LARGE-PRIME-SUPPORT` | `iutMultiplicativeResidueBound`, `iutMultiplicative_residueChar_le_bound`, `iutMultiplicative_noReduction_of_residueChar_gt_bound`, `iutInitialThetaOddMultiplicativeSupport_eq_badPlacesOver_of_largePrime`, `iutInitialThetaOddSupportWeighted_logSum_eq_reference_absLogQ_of_largePrime` | `ArithmeticTeichmullerSpaces/Act1Scene1/IutInitialThetaLargePrimeSupport.lean` | 适配 `refer/iut/Iut/Concrete/CurveArithmeticProved.lean` 的 `EllipticCurveData.badAll_finite` 证明；原提交 `a2c25b2edbf5a9cbc30588b466a738b49547b443`，Git 作者 Christian Merten，文件作者 The iut contributors，参考快照 `07cb1da58f6d428a670dbb5dd6093d428bcbcdd8`。保留 Apache-2.0 通知，不导入参考工程。由 mathlib `FinitePlace.hasFiniteMulSupport` 和本地乘法约化 j-赋值界构造只依赖基域与曲线的自然数上界；超过上界的剩余特征上无乘法约化处。在显式最大 prime-to-ell `VBad` 来源等式及大素数条件下，消除 S1.202 的 ell 纤维障碍，并由 S1.200 得到完整 odd support 的 weighted log sum 等于实际 q-pilot `absLogQ`。属于 `Scene1/Derived`；不构造 admissible prime、实际 InitialThetaData 或 VBad 来源，不解决论文代表重数、去权、体积或 transfer 来源。 |
| `IUT-COR312-INITIAL-THETA-MAXIMAL-PRIME-DATA` | `IutCurveModEllRepData`, `iutInitialThetaOddSupportQOrderBound`, `iutInitialThetaElementaryPrimeBound`, `iutInitialTheta_exists_largeElementaryPrime`, `iutInitialThetaOddSupportQOrder_coprime_of_largePrime`, `iutInitialThetaModSupport_residueChar_coprime_of_largePrime`, `iutInitialThetaMaximalGlobalData`, `iutInitialThetaMaximalPrimeData` | `ArithmeticTeichmullerSpaces/Act1Scene1/IutInitialThetaMaximalPrimeData.lean` | 移植 `refer/iut/Iut/Concrete/Existence.lean` 的 `ModEllRepData`、`globalData`、`primeData`；原提交 `a36b42b9a221e1baaf434bb76c85b3a0dfbf33a7`，Git 作者 Christian Merten，文件作者 The iut contributors，参考快照 `07cb1da58f6d428a670dbb5dd6093d428bcbcdd8`，保留 Apache-2.0 通知，无参考工程依赖。在已有曲线的完整 odd support 上取 canonical Tate orders 的有限上界，与 S1.203 剩余特征界、相对域次数和 6 合并；Euclid 定理提供任意大的候选素数。由真实模表示、SL2 像条件及超过上界的素数，构造完整支撑上的 global/admissible-prime data；剩余特征、q-order 和域次数互素条件均由上界推出。输入 InitialThetaData 只提供同一曲线及其全局算术，不声称原 VBad 已最大，也不将新素数冒充原 prime。属于 Scene1/Derived；尚不构造模表示、SL2 像条件、orbicurve/local theta data 或完整新 InitialThetaData，亦不闭合去权、theta-volume 或 transfer。 |
| `IUT-COR312-INITIAL-THETA-MODELLREP-CONSTRUCT` | `iutGalTorsionHom`, `iutRepOf`, `iutRepOf_spec`, `iutRepOf_ker_isOpen`, `IutCurveModEllRepData.ofBasis` | `ArithmeticTeichmullerSpaces/Act1Scene1/IutInitialThetaModEllRepConstruct.lean` | 逐文件移植 `refer/iut/Iut/Concrete/ModEllRepConstruct.lean` 的 Galois torsion action、chosen-basis matrix representation、作用公式和开核证明；原提交 `a2c25b2edbf5a9cbc30588b466a738b49547b443`，文件作者 The iut contributors，参考快照 `07cb1da58f6d428a670dbb5dd6093d428bcbcdd8`，保留 Apache-2.0 通知，不导入参考工程。`domRestrict` 适配当前 Mathlib API。由实际 torsion basis 构造 `IutCurveModEllRepData`；`SL₂` 像条件仍是独立输入，未声称由此自动得到。属于 `Scene1/Derived`，不改变 Prologue-R5。 |
| `IUT-COR312-MODELLREP-CYCLIC-SUBGROUP` | `IutCurveModEllRepData.hasCyclicSubgroup_of_stable_line`, `IutCurveModEllRepData.exists_mulVec_ne_smul_of_not_hasCyclicSubgroup`, `IutHasCyclicSubgroup.exists_le_torsionBy` | `ArithmeticTeichmullerSpaces/Act1Scene1/IutModEllRepCyclicSubgroup.lean` | 移植 `refer/iut/Iut/Concrete/CyclicSubgroup.lean` 与 `ModEllRepGalois.lean` 的稳定直线论证到本地 `IutCurveModEllRepData`：在实际几何 `ell`-torsion 上构造 Galois 稳定的阶 `ell` 子群，并由无循环子群条件得到任意非零直线的非稳定元。原提交 `a2c25b2edbf5a9cbc30588b466a738b49547b443`，Git 作者 Christian Merten，文件作者 The iut contributors，参考快照 `07cb1da58f6d428a670dbb5dd6093d428bcbcdd8`，保留 Apache-2.0 通知，不导入参考工程。该模块不构造 fixed field、局部 Tate 约化或 `SL₂` 满像；后者仍需 S1.206 的群论接口和真实局部来源。属于 `Scene1/Derived`，不改变 Prologue-R5。 |
| `IUT-COR312-MODELLREP-FIXED-FIELD` | `IutCurveModEllRepData.torsionField`, `IutCurveModEllRepData.torsionEquiv`, `IutCurveModEllRepData.card_torsionBy_EK`, `IutCurveModEllRepData.rangeEquivGal`, `IutCurveModEllRepData.card_range` | `ArithmeticTeichmullerSpaces/Act1Scene1/IutModEllRepFixedField.lean` | 移植 `refer/iut/Iut/Concrete/ModEllRepGalois.lean` 的 fixed-field 与 Galois-range 部分：由实际表示核定义 torsion field，证明几何 `ell`-torsion 下沉到该域，且表示像与固定域 Galois 群等势并有相同基数。原提交 `a2c25b2edbf5a9cbc30588b466a738b49547b443`，Git 作者 Christian Merten，文件作者 The iut contributors，参考快照 `07cb1da58f6d428a670dbb5dd6093d428bcbcdd8`，保留 Apache-2.0 通知，不导入参考工程。该模块不包含局部 Tate 约化、ramification divisibility 或 `SL₂` 满像；这些仍由后续 Scene1 来源提供。属于 `Scene1/Derived`，不改变 Prologue-R5。 |
| `IUT-COR312-MODELLREP-ADMISSIBLE-ADAPTER` | `IutCurveModEllRepData.ofAdmissiblePrime`, `IutCurveModEllRepData.ofAdmissiblePrime_torsionField`, `IutCurveModEllRepData.ofAdmissiblePrime_sl_le_range`, `iutInitialThetaModEllRepData`, `iutInitialThetaModEllRepData_torsionField`, `iutInitialThetaModEllRepData_sl_le_range` | `ArithmeticTeichmullerSpaces/Act1Scene1/IutModEllRepAdmissibleAdapter.lean` | 将现有 `AdmissiblePrimeData` 的实际 torsion basis、Galois representation、作用公式、开核和 `SL₂` 像字段投影到本地 `IutCurveModEllRepData`，并证明两种 fixed-field 定义相等。原提交 `a2c25b2edbf5a9cbc30588b466a738b49547b443`，Git 作者 Christian Merten，文件作者 The iut contributors，参考快照 `07cb1da58f6d428a670dbb5dd6093d428bcbcdd8`，保留 Apache-2.0 通知，不导入参考工程。该适配器不构造新素数，也不证明新的满像或局部 Tate 来源；它只消除现有 `InitialThetaData.prime` 与 Scene1 表示契约之间的重复字段。属于 `Scene1/Derived`，不改变 Prologue-R5。 |
| `IUT-COR312-SL2-GENERATION` | `IutSL2.sq_eq_zero_of_isNilpotent`, `IutSL2.transvection_of_orderOf`, `IutSL2.toGL_mem_of_transvection` | `ArithmeticTeichmullerSpaces/Act1Scene1/IutSL2Generation.lean` | 逐文件移植 `refer/iut/Iut/Tripod/SL2Generation.lean` 的独立 `GL₂/SL₂` 群论：非平凡 transvection 的判定、含 transvection 且不稳定直线的子群包含 `SL₂`。原提交 `a5937f741e337304b4602631b19a999f9d896c92`，Git 作者 Christian Merten，文件作者 The iut contributors，参考快照 `07cb1da58f6d428a670dbb5dd6093d428bcbcdd8`，保留 Apache-2.0 通知，不导入参考工程。该模块只提供独立群论接口；它不构造真实 mod-ell 表示、不开示 `SL₂` image 条件，也不构造 `InitialThetaData`。属于 `Scene1/Derived`，不改变 Prologue-R5。 |

| `IUT-COR312-INITIAL-THETA-SCENE1-QPILOT-REFERENCE-ADAPTER` | `Corollary312Scene1QPilotData.absLogQ_eq_reference_iutInitialTheta_absLogQ_ofCanonicalInitialThetaLink` | `ArithmeticTeichmullerSpaces/Act1Scene1/IutInitialThetaScene1QPilotData.lean` | Adapts the S1.190 canonical q-pilot/reference `absLogQ` equality to the `Corollary312Scene1QPilotData.ofCanonicalInitialThetaLink` bundle built from actual `InitialThetaData`. The proof keeps the supplied target-side `Corollary312Scene1Data`, canonical link equality, `T.ell = D.prime.ell`, and degree-one normalization explicit, then projects the bundle q-pilot into the finite weighted bridge. It does not construct target volume, packet/hull or q-family data, identify paper `L'` representatives or `V_p^oss`, remove q-pilot weights, or prove Corollary 3.12. |

| `IUT-COR312-INITIAL-THETA-SCENE1-QPILOT-SELECTED-QROOT-ADAPTER` | `Corollary312Scene1QPilotData.reference_absLogQ_eq_selectedQRootPaperQLogSum` | `ArithmeticTeichmullerSpaces/Act1Scene1/IutInitialThetaScene1QPilotData.lean` | Transfers the reference `IutTorsionQRootSource.iutInitialThetaQPilotData.absLogQ` equality to the selected q-root paper-q log sum for a real `InitialThetaData` Scene1 bundle. The theorem consumes explicit reference alignment, representative accounting certificate `A`, and representative-to-canonical-section-link equivalence/local-term certificate `B`; it keeps the selected finite carrier, `ell > 0`, local q-root normalization, and all source inputs visible. It does not prove the `A/B` sources, identify paper `L'` representatives or `V_p^oss`, remove q-pilot or residue-degree weights globally, freeze raw versus degree-normalized normalization, or prove theta-volume, packet/hull, transfer bounds, or Corollary 3.12. |

| `IUT-COR312-INITIAL-THETA-SCENE1-QPILOT-SELECTED-QROOT-GROUPED-ADAPTER` | `Corollary312Scene1QPilotData.reference_absLogQ_eq_selectedQRootPaperQLogSum_grouped` | `ArithmeticTeichmullerSpaces/Act1Scene1/IutInitialThetaScene1QPilotData.lean` | Repackages the S1.192 reference q-pilot/selected q-root equality as a finite residue-characteristic `(p,w)` sum over the actual selected q-root subtype. The residue-characteristic image and filters are defined explicitly, and the proof consumes the same reference alignment plus representative/link certificates `A/B`; it does not identify this carrier with paper `L'` representatives or `V_p^oss`, prove their multiplicities, remove q-pilot or residue-degree weights globally, freeze raw versus degree-normalized normalization, or establish theta-volume, packet/hull, transfer bounds, or Corollary 3.12. |

| `IUT-COR312-INITIAL-THETA-SELECTED-BASE-SUPPORT-COVERAGE` | `iutInitialThetaOddSupportSelectedBasePlaces_eq_fullSupport_iff` | `ArithmeticTeichmullerSpaces/Act1Scene1/IutInitialThetaSelectedBaseSupportCoverage.lean` | Uses the actual `InitialThetaData` finite-place section, `placeUnder` uniqueness, and `IutOddMultiplicativeSupport`/moduli-support identities to characterize equality between the section-selected base carrier and the full odd multiplicative q-pilot support. The reverse inclusion is equivalent to the explicit coverage condition `sectionBasePlace (placeUnder w) = w` for every full-support place. This records the missing source obligation; it does not prove coverage, identify paper `L'` representatives or `V_p^oss`, or provide representative multiplicities and global q-sum accounting. |
| `IUT-COR312-INITIAL-THETA-FULL-SUPPORT-VBAD-COVERAGE` | `iutInitialThetaOddMultiplicativeSupport_eq_badPlacesOver_VBad_iff`, `iutInitialThetaOddMultiplicativeSupport_eq_badPlacesOver_VBad_iff_subset` | `ArithmeticTeichmullerSpaces/Act1Scene1/IutInitialThetaFullSupportVBadCoverage.lean` | Uses `IutInitialThetaBadSupport.lean` and the ported `badPlacesOver` definition to characterize equality between the complete odd multiplicative support and the actual `InitialThetaData.VBad` q-pilot carrier. The reverse inclusion is exposed either as explicit `VBad` over-place coverage for every full-support place or as the corresponding set inclusion; the opposite inclusion is the existing `iutBadPlacesOver_subset_oddMultiplicativeSupport`. This records the missing source obligation and does not prove it, identify paper `L'` representatives or `V_p^oss`, or remove q-pilot weights. |
| `IUT-COR312-INITIAL-THETA-FULL-SUPPORT-CANONICAL-ABSLOGQ` | `iutInitialThetaOddSupportWeighted_logSum_eq_reference_absLogQ_of_support_eq` | `ArithmeticTeichmullerSpaces/Act1Scene1/IutInitialThetaFullSupportCanonicalAbsLogQ.lean` | Under the explicit equality `IutOddMultiplicativeSupport D = badPlacesOver D.F D.E D.VBad`, compares the full-support weighted log sum with the reference `QPilotData.absLogQ`. It uses the canonical `InitialThetaData` q-root weighted-sum theorem and the full-support base q-order theorem, so the independent q-root choices are compared through their common base q-order accounting rather than by a pointwise root-function equality. The support equality remains an explicit source obligation; paper `L'` representatives, `V_p^oss`, multiplicity, global unweighting, normalization freeze, theta-volume, transfer bound and Corollary 3.12 remain open. |
| `IUT-COR312-INITIAL-THETA-SELECTED-SUPPORT-COVERAGE-ACCOUNTING` | `iutInitialThetaOddSupportSelectedQRootSourcePlaces_qPilotWeighted_fiber_eq_fullSupport` | `ArithmeticTeichmullerSpaces/Act1Scene1/IutInitialThetaSelectedBaseSupportCoverageAccounting.lean` | Combines the explicit coverage condition with the selected section/base-place fibre accounting and the full odd-support torsion q-root weighted fibre identity. Under coverage, the selected q-root fibre with `qPilotWeight * ramIdx * ordp(qroot)` equals the complete odd-support weighted fibre at each residue characteristic. The theorem keeps coverage as an explicit input and does not prove it, identify paper `L'` representatives or `V_p^oss`, remove the q-pilot weights, or close the global paper q-sum. |
| `IUT-COR312-INITIAL-THETA-SELECTED-SUPPORT-COVERAGE-LOG-SUM` | `iutInitialThetaOddSupportSelectedQRootSourcePlaces_qPilotWeighted_logSum_eq_fullSupport_on_selectedResidueImage` | `ArithmeticTeichmullerSpaces/Act1Scene1/IutInitialThetaSelectedBaseSupportCoverageAccounting.lean` | Sums the preceding coverage-conditioned fibre equality after multiplying by `Real.log p` over the explicit residue-characteristic image of the selected source carrier. This is a finite logarithmic bridge to the full odd-support weighted fibres; it does not add coverage, identify the image with the canonical q-pilot `VBad` carrier or paper `L'` representatives, and does not remove weights or close Corollary 3.12. |
| `IUT-COR312-INITIAL-THETA-SELECTED-SUPPORT-RESIDUE-IMAGE` | `iutInitialThetaOddSupportSelectedQRootSourcePlaces_residueCharImage_eq_fullSupport` | `ArithmeticTeichmullerSpaces/Act1Scene1/IutInitialThetaSelectedBaseSupportCoverageAccounting.lean` | Under the explicit coverage condition, transports the selected source/base-place equivalence through the equality of selected and full odd multiplicative base support, proving equality of the finite residue-characteristic images. This fixes the finite `(p,w)` summation range for the full-support weighted bridge; it does not prove coverage, identify `VBad` or paper `L'` representatives, or remove q-pilot weights. |
| `IUT-COR312-INITIAL-THETA-FULL-SUPPORT-WEIGHTED-LOG-SUM` | `iutInitialThetaOddSupportWeighted_logSum_eq_baseQOrder_on_fullResidueImage` | `ArithmeticTeichmullerSpaces/Act1Scene1/IutInitialThetaSelectedBaseSupportCoverageAccounting.lean` | Sums the real `InitialThetaData` full odd-support weighted fibre identity over the finite support residue-characteristic image, yielding the base `qPilotWeight * qOrder/(2*ell)` logarithmic sum. It is unconditional for the full-support source, but does not identify that support with `VBad`, paper `L'`, or an independent Scene1 link. |
| `IUT-COR312-INITIAL-THETA-SELECTED-SUPPORT-WEIGHTED-LOG-SUM` | `iutInitialThetaOddSupportSelectedQRootSourcePlaces_qPilotWeighted_logSum_eq_baseQOrder_on_fullResidueImage` | `ArithmeticTeichmullerSpaces/Act1Scene1/IutInitialThetaSelectedBaseSupportCoverageAccounting.lean` | Under explicit section coverage, combines the selected/full fibre bridge, residue-image equality, and unconditional full-support log-sum identity. It gives a selected q-root weighted logarithmic sum equal to the full-support base q-order sum on the same finite `(p,w)` range; it retains q-pilot weights and does not prove paper representative accounting or Corollary 3.12. |

| IUT-COR312-SELECTED-QROOT-WEIGHTED-ACCOUNTING | iutInitialThetaOddSupportSelectedBaseQOrder, iutInitialThetaOddSupportSelectedQRootSourcePlaces_qPilotWeighted_baseRamIdx_mul_ordp_sum_eq | ArithmeticTeichmullerSpaces/Act1Scene1/IutInitialThetaSelectedQRootAccounting.lean | iut finite-place q-root valuation accounting from refer/iut/Iut/Concrete/ThetaLocalConstruct/Data.lean and Ordp.lean, combined with the actual section and contraction ports from Iut/Cor312/ThetaData/LocalConditions.lean and PlaceUnder.lean. On the finite selected carrier, transports qPilotWeight * baseRamIdx * ordp(qroot) across the proved source/base-place equivalence and obtains the selected base q-order sum. The ramification index is the contracted base-place index from the existing ordp formula. This remains weighted accounting for the concrete section choice; it does not identify the carrier with paper L' representatives or underline V^oss, remove q-pilot weights, or prove the unweighted paper sum |

| `IUT-COR312-INITIAL-THETA-QPILOT-REFERENCE-BRIDGE` | `Corollary312QPilotData.absLogQ_eq_reference_iutInitialTheta_absLogQ_ofCanonicalInitialThetaLink` | `ArithmeticTeichmullerSpaces/Act1Scene1/IutInitialThetaQPilotReferenceBridge.lean` | Uses the canonical `InitialThetaData` link carrier equality, the arithmetic q-pilot weight definition, and the S1.189 canonical-to-admissible-prime q-order theorem to identify the canonical Scene1 q-pilot `absLogQ` with `IutTorsionQRootSource.iutInitialThetaQPilotData.absLogQ`. This is a finite weighted accounting bridge for the actual `InitialThetaData` bad-place carrier; it does not identify paper `L'` representatives or `V_p^oss`, remove q-pilot weights, settle raw versus degree-normalized q-factors, or prove theta-volume, packet/hull accounting, transfer bounds, or Corollary 3.12. |

The reference checkout is `refer/iut` at commit `d9465c111ec4073709f67e9fccec7e3eb374a816`.
The current tree does not import `refer/iut` as a Lake dependency. Individual APIs may be
ported after adaptation to the frozen mathlib boundary; each port records its source path,
source commit, license/copyright status, destination path and modification summary in this
ledger. The q-order and Tate-torsion-residue ports above are adapted APIs, not wholesale copies
of the `TateCurvesTheta`-dependent modules.

| `IUT-COR312-TATE-VALUATION-BRIDGE` | `iutValued_eq_of_norm_eq`, `iutValued_embedding`, `iutValued_of_isUniformizer`, `iutValued_q_toOrdered`, `iutValued_q_eq_inv_tateJ` | `ArithmeticTeichmullerSpaces/Act1Scene1/IutTateValuationBridge.lean` | 移植 `refer/iut/Iut/Concrete/SL2Image.lean` 的 `Valued` 局部 Tate 赋值桥接到本地 completion API。使用 `IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation'`、`WithZero.exp/log` 和 `TateParameter.toOrdered`，证明 norm 相等推出 valuation 相等、completion embedding 的 valuation、uniformizer valuation、Tate parameter 的 ordered exponent 公式及 `v(q)=v(j)⁻¹`。原参考提交 `47ef99c97945984ea799ee2333fcf920abecdae4`，参考快照 `07cb1da58f6d428a670dbb5dd6093d428bcbcdd8`，保留 Apache-2.0 文件头，不导入 `refer/iut`。该桥接只处理局部赋值事实，不构造 Tate structure、ramification divisibility、torsion root-class 或 `SL₂` 满像。属于 `Scene1/Derived`，不改变 Prologue-R5。 |

| `IUT-COR312-RAMIFICATION-CARDINALITY` | `IutCurveModEllRepData.finiteDimensional_torsionField`, `IutCurveModEllRepData.numberField_torsionField`, `IutCurveModEllRepData.ramificationIdx_dvd_card_gal` | `ArithmeticTeichmullerSpaces/Act1Scene1/IutModEllRepFixedField.lean`, `ArithmeticTeichmullerSpaces/Act1Scene1/IutRamificationCardinality.lean` | 由表示核开性和 fixed-field fixing subgroup 的开性，适配 `InfiniteGalois.isOpen_iff_finite` 得到 generic representation fixed field 的有限维数域与 `NumberField` 实例；再移植 `refer/iut/Iut/Concrete/SL2Image.lean` 的 `EllipticCurveData.ramificationIdx'_dvd_card_gal`，证明 fixed-field 有限处相对分歧指数整除 `Nat.card (Gal(K/F))`。原参考提交 `47ef99c97945984ea799ee2333fcf920abecdae4`，参考快照 `07cb1da58f6d428a670dbb5dd6093d428bcbcdd8`，保留 Apache-2.0 文件头，不导入 `refer/iut`。该单元不证明 Tate root-class、`ell ∣ e`、Cauchy 元素或 `SL₂` 满像；属于 `Scene1/Derived`，不改变 Prologue-R5。 |

| `IUT-COR312-LOCAL-TORSION-CARDINALITY` | `IutCurveModEllRepData.card_torsion_curveKw_ge` | `ArithmeticTeichmullerSpaces/Act1Scene1/IutLocalTorsionCardinality.lean` | 移植 `refer/iut/Iut/Concrete/SL2Image.lean` 的 `EllipticCurveData.card_torsion_curveKw_ge`，以 fixed-field `TK` 的基数等式和 `pointMap` 单射构造局部 completion Tate `ell`-torsion 的基数下界 `ell²`。适配当前 Mathlib API 使用 `domRestrict`，并显式保持 local `TateStructure` 与 finite torsion 实例。原参考提交 `47ef99c97945984ea799ee2333fcf920abecdae4`，参考快照 `07cb1da58f6d428a670dbb5dd6093d428bcbcdd8`，不导入 `refer/iut`。该单元不构造 Tate structure、root-class、ramification divisibility 或 `SL₂` 满像；属于 `Scene1/Derived`，不改变 Prologue-R5。 |

| `IUT-COR312-ROOTCLASS-RAMIFICATION` | `IutCurveModEllRepData.prime_dvd_ramificationIdx_of_tate` | `ArithmeticTeichmullerSpaces/Act1Scene1/IutRootClassRamification.lean` | 适配 `refer/iut/Iut/Concrete/SL2Image.lean` 的 `EllipticCurveData.prime_dvd_ramificationIdx`：由局部 Tate structure 的 root-class 方程、`ell²` torsion 基数下界、`iutValued_q_toOrdered` 和 `iutValuedEmbedCompletion`，在 `¬ ell ∣ qOrder` 下证明 `ell ∣ e(w'/w)`。当前接口显式接收 `S.t.q = iutEmbedCompletion (t.q)` 的参数对齐证书；不把该证书误记为真实 `InitialThetaData/TateFamily` 来源。原参考提交 `47ef99c97945984ea799ee2333fcf920abecdae4`，参考快照 `07cb1da58f6d428a670dbb5dd6093d428bcbcdd8`，不导入 `refer/iut`。属于 `Scene1/Derived`，不改变 Prologue-R5；不构造 root-class 来源、Cauchy 元素或 `SL₂` 满像。 |
| `IUT-COR312-SL2-IMAGE-BRIDGE` | `IutCurveModEllRepData.prime_dvd_card_range_of_ramification`, `IutCurveModEllRepData.sl_le_range_of_prime_dvd_card`, `IutCurveModEllRepData.sl_le_range_of_ramification` | `ArithmeticTeichmullerSpaces/Act1Scene1/IutSL2ImageBridge.lean` | 移植 `refer/iut/Iut/Concrete/SL2Image.lean` 的最后群论连接：给定每个合适有限处的 `ell` 整除相对分歧指数，结合 fixed-field Galois 基数整除得到 `ell ∣ Nat.card (rep.range)`；Cauchy 定理产生阶 `ell` 元素，S1.206 的 transvection/稳定直线接口随后证明像包含 `SL₂ (ZMod ell)`。`hDvd`、Tate 参数对齐、root-class 来源和实际 admissible-prime 装配仍为显式输入；不识别论文 representatives，也不闭合 Corollary 3.12。原参考提交 `47ef99c97945984ea799ee2333fcf920abecdae4`，参考快照 `07cb1da58f6d428a670dbb5dd6093d428bcbcdd8`，保留 Apache-2.0 文件头，不导入 `refer/iut`。属于 `Scene1/Derived`，不改变 Prologue-R5。 |
| `IUT-COR312-SL2-IMAGE-SOURCE-BRIDGE` | `IutCurveModEllRepData.LocalTateImageSource`, `IutCurveModEllRepData.prime_dvd_card_range_of_local_tate`, `IutCurveModEllRepData.sl_le_range_of_local_tate` | `ArithmeticTeichmullerSpaces/Act1Scene1/IutSL2ImageSourceBridge.lean` | 移植 `refer/iut/Iut/Concrete/SL2Image.lean` 的 `prime_dvd_card_range`/`sl_le_range_of` 装配尾部。`LocalTateImageSource` 现在带显式有限处 `support` 参数，并在该支撑上携带 Tate parameter、uniformizer、Tate structure、`ell²` torsion 基数下界和 `ell` 与 q-order 互素证书；组合 S1.213 的 root-class 分歧桥与 S1.214 的 Cauchy/`SL₂` 生成桥。S1.216 退休了要求所有有限处都有见证的过强边界，实际 `InitialThetaData` 的完整 source 已由 S1.218 在 `VBad` 拉回支撑上实例化；完整 odd support 上的阶互素证书仍需额外来源；它仍不隐藏任何参数对齐义务，原参考提交 `47ef99c97945984ea799ee2333fcf920abecdae4`，Git 作者 Christian Merten，文件作者 The iut contributors，参考快照 `07cb1da58f6d428a670dbb5dd6093d428bcbcdd8`，保留 Apache-2.0 通知，不导入 `refer/iut`。属于 `Scene1/Derived`，不改变 Prologue-R5。 |
| `IUT-COR312-INITIAL-THETA-LOCAL-TATE-IMAGE` | `iutInitialThetaLocalTateImageSource`, `iutInitialThetaPrime_dvd_card_range_of_local_tate` | `ArithmeticTeichmullerSpaces/Act1Scene1/IutInitialThetaLocalTateImage.lean` | 适配 `refer/iut/Iut/Concrete/SL2Image.lean` 的局部 Tate/分歧装配，原提交 `47ef99c97945984ea799ee2333fcf920abecdae4`，Git 作者 Christian Merten，文件作者 The iut contributors，参考快照 `07cb1da58f6d428a670dbb5dd6093d428bcbcdd8`，保留 Apache-2.0 通知。复用本地 `tateStructureOfTorsion`（原路径 `Iut/Cor312/ThetaData/TateFamilyOfTorsion.lean`，提交 `e4777b2238f45be2e58c00b4d0213c0cb83405b9`）、fixed-field torsion descent、完成域比较与 Tate `j` 唯一性，从实际 `InitialThetaData.global/prime` 构造完整 `LocalTateImageSource`，再由 S1.217 见证和 root-class 分歧桥证明像阶被 `ell` 整除。局部结构在表示 fixed field 上重新派生，不要求调用者运输 `D.tate`；不使用 `prime.sl_le_range`，不假定整个 odd support 有互素阶。支撑严格为实际 `badPlacesOver D.F D.E D.VBad`。该结果没有构造 `InitialThetaData`、真实 Scene1 满足模型、论文 `L'`/`V_p^oss`、去权或体积 accounting；属于 `Scene1/Derived`，不改变 `Prologue-R5`。 |

## S1.228：实际 trace 因式分解与 Vélu 加法恒等式

| Source id | 本地声明与路径 | 来源、适配与边界 |
| --- | --- | --- |
| `LOCAL-COR312-VELU-TRACE-FACTORIZATION` | `IutVeluPolynomial.numerator_monic_degree`、`eval_numerator`、`numerator_factorization`、`cosetProduct_eq`、`veluRatio_mul`、`crude_bound`、`IutCyclicCoordinate.pointPairs_ratioNewton`；`ArithmeticTeichmullerSpaces/Act1Scene1/IutVeluTracePolynomial.lean` | 本地独立证明，使用冻结 Mathlib 提交 `389347a7c1cfa76f6bd5be2ca35d4cb621610ad3` 的多项式首一/次数/根 APIs 与 S1.227 成对坐标/trace 恒等式。实际非零子群坐标生成分母；奇阶性保证 Q、−Q 不同，移除这两项后修正项次数小于主项。分子首一且次数等于原子群基数，实际求值为坐标和减标量乘分母。对子群外 R 且 2R 不在 H，余陪集 R+H 的 x 坐标两两不同，真实有限和重索引给出全部根；因式分解得到完整 Vélu 加法恒等式。S1.225 Newton 界经该恒等式成为真实比值粗界，S1.226 同一共同域/子群/点对的消费者控制实际 ratioProduct 与辅助坐标差。无 Heights 代码复制或导入，无新外部依赖。 |

适用于一般数域椭圆曲线，不增加 Legendre 模型或外部加法证书。完整加法恒等式
及模型例外处外粗界已闭合，其他各处估计、辅助坐标差、高度/places 运输、
无循环子群全局上界与完整 Scene1 验收仍开放。
属于 `Scene1/Derived`，`Prologue-R5` 不变；无新增前置数学假设。

## S1.227：实际坐标和的有理 trace 表达

| Source id | 本地声明与路径 | 来源、适配与边界 |
| --- | --- | --- |
| `LOCAL-COR312-VELU-ADDITIVE-TRACE` | `IutVeluTrace.paired_xCoordinates`、`traceFunction_eq`、`translatedSum_eq`、`traceDifference_le`、`IutCyclicCoordinate.pointPairs_traceNewton`；`ArithmeticTeichmullerSpaces/Act1Scene1/IutVeluAdditiveTrace.lean` | 本地独立证明，使用冻结 Mathlib 提交 `389347a7c1cfa76f6bd5be2ca35d4cb621610ad3` 中 `Affine/Formula.lean` 的 `addX_of_X_ne`、`den_duplication_eq` 和 `Affine/Point.lean` 的群律 API。从倍点不变量对称展开证明成对坐标分子，定义实际有理 correction/trace；有限 H 的取负重索引和原点项分拆证明实际坐标和的两倍等于 trace。trace 差接入 S1.225 Newton 界，再以 S1.226 同一共同域/原像子群/规范点对提供实际消费者，奇阶自动排除点落在子群中。参考 Heights 文件仅定位数学 API，无许可证声明，未复制或导入；无新外部依赖。 |

该结果闭合成对坐标与有限子群有理 trace 的来源，适用于一般数域曲线，
不增加 Legendre 模型限制。trace 分子因式分解和实际 Vélu 比值乘积恒等式仍开放；
各处估计、高度/places 运输、无循环子群上界和完整 Scene1 验收仍须独立完成。
属于 `Scene1/Derived`，`Prologue-R5` 不变；没有新增前置数学假设。

## S1.226：原始有限几何子群的共同坐标数域

| Source id | 本地声明与路径 | 来源、适配与边界 |
| --- | --- | --- |
| `IUT-COR312-CYCLIC-COORDINATE-FIELD` | `IutCyclicCoordinate.field`、`numberField_field`、`subgroupEquiv`、`card_subgroup`、`exists_pointPairs`、`algebraMap_veluRatio`、`algebraMap_translatedSum`、`algebraMap_ratioProduct`、`ratioProduct_productFormula_and_Newton`、`ratioProduct_eq_inclusion`；`ArithmeticTeichmullerSpaces/Act1Scene1/IutCyclicCoordinateField.lean` | 复用 S1.223 已适配的有限坐标生成域构造；原路径 `refer/iut/Iut/Tripod/CurveOf.lean`，实际提交 `5c6b5909ffda4af24582dc746e74e43702edc1c2`，Git 作者 Christian Merten，文件作者与版权人为 2026 The iut contributors，Apache-2.0 通知保留，参考快照 `07cb1da58f6d428a670dbb5dd6093d428bcbcdd8`。本轮不新复制参考文件；对子群全坐标扩充、原像加法等价、规范点对提升、实际比值/坐标和重索引、乘积公式与 Newton 组合入口均为本地证明。共同域由实际有限坐标集合生成，子群点逐个有原像，域内子群与原始 H 同基数；点对的四个闭包像等于 S1.224 的同一规范点对。比值积的闭包像等于原始实际比值积，平移坐标和也沿同一映射运输。奇阶时非零比值积满足共同数域的乘积公式与对数等式，坐标和在实际有限模型例外处外满足 S1.225 Newton 界。原基域 Galois 稳定时比值积保留来自较小四挠坐标域的代表。 |

该构造退休原始几何 H 与 Newton 有理子群的共同扩域来源义务；尚未证明 Vélu
加法恒等式或各处高度估计，亦未运输原基域 places 或构造新 InitialThetaData。
JoshiTeich 适配保留一般数域椭圆曲线，不加入 Legendre 限制或外部辅助点假设。
属于 `Scene1/Derived`，`Prologue-R5` 不变；无新 Lake 依赖、外部 IUT 或 Heights 导入。

## S1.225：一般曲线的 Newton 挠点与平移坐标和界

| Source id | 本地声明与路径 | 来源、适配与边界 |
| --- | --- | --- |
| `IUT-COR312-TORSION-NEWTON-BOUND` | `IutTorsionNewton.apply_coeff_ΨSq_le_one`、`apply_x_le`、`apply_xCoordinate_le_completedSquare`、`modelBadPlaces_finite`、`apply_xCoordinate_le_of_notMem_modelBadPlaces`、`translatedSum_le`、`IutFourTorsion.pointPairsBounds_over_field`；`ArithmeticTeichmullerSpaces/Act1Scene1/IutTorsionNewton.lean` | 移植 `refer/iut/Iut/Tripod/TorsionNewton.lean` 首个命名空间的通用整模型证明；实际文件提交 `225164d1a47b377fac3bff58a22e43ec7f9cc676`，Git 作者 Christian Merten，文件作者与版权人为 2026 The iut contributors，保留 Apache-2.0 通知，与参考快照 `07cb1da58f6d428a670dbb5dd6093d428bcbcdd8` 的路径 diff 为空。使用本地 S1.221 的除法多项式根判据，构造实际 w-整子环/模型，证明系数整性，以最高项 n² 得到 Newton 坐标界。其余为本地证明：通过 S1.221 的 completeSquare 和既有 vcEquiv 保持 x/挠关系，以实际完成模型系数定义有限例外处，在其外证明任意数域曲线的 w(n)²*w(x(P))≤1；有限子群平移四挠点后，用缩放坐标差和超度量有限和得到 w(4*card H)²*w(translatedSum H T R)≤1。最终入口消费 S1.223 的实际四挠坐标数域点对，对该域中的有限点子群给出两对点的和界。没有复制参考文件的 Legendre/Heights 缩放段，没有复制或导入无许可证通知的 Heights.VeluProduct。 |

一般数域曲线的结论不要求 Legendre 模型；例外处集合由实际系数确定且有有限性证明。
本轮控制实际平移坐标和，未将其认作 Vélu 比值。最终入口的 H 位于四挠坐标数域
有理点群；原始闭包稳定子群的共同有限有理性扩域及其运输仍须构造。Vélu 加法恒等式、
例外处/graph line/Tate gain、无穷处估计、高度/places 运输和无循环子群上界仍开放。
属于 `Scene1/Derived`，`Prologue-R5` 不变；未增加 Lake 依赖、外部 IUT 或 Heights 导入。

## S1.224：实际四挠坐标域上的比值与乘积公式

| Source id | 本地声明与路径 | 来源、适配与边界 |
| --- | --- | --- |
| `IUT-COR312-FOUR-TORSION-VELU-DESCENT` | `IutFourTorsion.isAlgClosure_field`、`pointPairsInClosure`、`galPointMap_eq_of_four_nsmul`、`ratioProduct_ne_zero`、`ratioProduct_galois`、`exists_algebraMap_eq_ratioProduct`、`exists_nonzero_ratio_productFormula`；`ArithmeticTeichmullerSpaces/Act1Scene1/IutFourTorsionVeluRatio.lean` | 本地连接证明，不新复制参考文件。消费 S1.223 的几何点对和实际四挠坐标域（来源 `Iut/Tripod/CurveOf.lean`，实际提交 `5c6b5909ffda4af24582dc746e74e43702edc1c2`），以及 S1.222 的奇阶比值非零、Galois 重索引和对数乘积公式（来源 `Iut/Tripod/CyclicPoints.lean`、`CyclicIsogeny.lean`，实际提交 `c35ca616ba5ec707d8ef08a781df35fadba16532`）。这些来源的 Git 作者为 Christian Merten，版权与文件作者为 2026 The iut contributors，Apache-2.0 通知留在已移植模块中，参考快照 `07cb1da58f6d428a670dbb5dd6093d428bcbcdd8`。通过坐标在实际 adjoin 域中的成员证明，自同构的 commutes 律固定每个四挠点；限制标量后直接消费原始 F 的子群稳定性。比值积保留原始几何点载体，以无限 Galois 固定判据下降到实际四挠坐标域，证明其非零，并给同一个元素提供该域的乘积公式与有限支撑对数等式。无需外部有理点对、扩域稳定性或 curve/action 运输证书。 |

结果适用于任意数域椭圆曲线及给定奇阶有限原基域 Galois 稳定子群，不要求 Tripod
或 Legendre 模型。实际 `ρ` 的闭包像等于选定几何点对的比值积；不会丢失辅助点
和后续各处估计的联系。`ρ` 和 places 均属于四挠坐标域，原基域高度/places 的运输、
局部 graph line、Vélu 加法恒等式、Newton/无穷处估计及无循环子群上界仍开放。
属于 `Scene1/Derived`，`Prologue-R5` 不变；没有增加 Lake 依赖或参考工程导入。

## S1.223：几何半点与四挠坐标数域

| Source id | 本地声明与路径 | 来源、适配与边界 |
| --- | --- | --- |
| `IUT-COR312-FOUR-TORSION-SOURCE` | `iutGeometricTwoTorsion_hasHalf`、`iutGeometricFourTorsionPointPairs_exists`、`IutFourTorsion.coordinates_finite`、`finiteDimensional_field`、`numberField_field`、`exists_point_over_field`、`pointPairs_over_field`；`ArithmeticTeichmullerSpaces/Act1Scene1/IutFourTorsionSource.lean` | 从 `refer/iut/Iut/Tripod/CurveOf.lean` 提取 `coords`、`torsionCoords_finite` 和 `finiteDimensional_fieldOf'` 的坐标集合及有限生成域步骤，适配为任意数域曲线的几何四挠坐标域。实际提交 `5c6b5909ffda4af24582dc746e74e43702edc1c2`，Git 作者 Christian Merten，文件作者与版权人为 2026 The iut contributors，Apache-2.0 通知保留，与参考快照 `07cb1da58f6d428a670dbb5dd6093d428bcbcdd8` 的路径 diff 为空。其余为本地证明：由 S1.221 的 `E[2]`、`E[4]` 基数 `4`、`16`，控制倍乘 `2` 的核基数不超过 `4`，证明倍乘满射；选取二维二挠基中的两个不同非零点和半点。四挠坐标域通过实际有限坐标集合 adjoin 构造，代数闭包的代数性证明有限维，再构造 NumberField 实例。每个几何四挠点的坐标被实际收入该域，点关系通过 base change 单射运输；没有输入任意有限扩域或外部半点证书。 |

本结果提供 S1.222 所需辅助点的有限数域来源，未声称半点在原始基域中。后续仍须
对齐扩域曲线的 Galois-stable subgroup、Vélu 比值、局部高度与 places，并证明相关
估计。该扩域不被自动登记为新的 `InitialThetaData`，无循环子群上界仍开放。
属于 `Scene1/Derived`，`Prologue-R5` 不变；未增加 Lake 依赖或导入参考工程。

## S1.222：循环子群的 Vélu 比值与乘积公式输入

| Source id | 本地声明与路径 | 来源、适配与边界 |
| --- | --- | --- |
| `IUT-COR312-CYCLIC-VELU-RATIO` | `IutCyclicVelu.veluRatio_ne_zero`、`veluRatio_galois`、`exists_algebraMap_eq_ratio`、`exists_nonzero_ratio_productFormula`、`logProductFormula`、`exists_ratio_logProductFormula`；`ArithmeticTeichmullerSpaces/Act1Scene1/IutCyclicVeluRatio.lean` | 从 `refer/iut/Iut/Tripod/CyclicPoints.lean` 提取奇阶子群无二阶点及比值非零证明；从 `Iut/Tripod/CyclicIsogeny.lean` 提取 Galois 重索引、比值下降和 `Cyclic.main_bound` 中的对数乘积公式步骤。两个文件的实际提交均为 `c35ca616ba5ec707d8ef08a781df35fadba16532`，Git 作者 Christian Merten，文件作者与版权人为 2026 The iut contributors，Apache-2.0 通知保留；与参考快照 `07cb1da58f6d428a670dbb5dd6093d428bcbcdd8` 的路径 diff 为空。坐标判别直接由 Mathlib `Point.X_eq_iff` 证明，下降改用代数闭包上的 `InfiniteGalois.mem_range_algebraMap_iff_fixed`，不要求参考工程的 Tripod provider、Legendre 模型或 torsion-field action。基域中的两对 `T,R` 满足 `T ≠ 0`、`2T = 0`、`2R = T` 时，得到真实非零 `ρ : F`，并由 Mathlib `NumberField.prod_abs_eq_one` 得到乘积公式及任意覆盖有限支撑的有限处集合上的对数等式。未复制或导入 `Heights.VeluProduct`，未增加依赖。 |

本结果适用于一般数域椭圆曲线，但显式要求四个点来自基域。当前 `InitialThetaData`
只保证六挠点有理性，不保证二挠点的半点在基域，故该来源对齐仍开放。局部 graph line、
Vélu 比值的有限处与复嵌入估计、无循环子群上界均未由乘积公式替代。该模块属于
`Scene1/Derived`，`Prologue-R5` 不变；没有新增 Core 或 Candidate 合约。

## S1.221：几何挠群基与候选表示来源

以下来源的 Git 作者均为 Christian Merten，文件作者与版权人为 The iut contributors，
文件版权年份为 2026，许可证为 Apache-2.0。参考快照为
`07cb1da58f6d428a670dbb5dd6093d428bcbcdd8`；各实际文件提交与快照的对应路径 Git diff
均为空。复制文件保留通知，修改命名空间和本地导入；一般曲线适配只提取配方变换所需的
三个声明，不引入参考工程依赖。

| Source id | 原路径与实际文件提交 | 本地路径与范围 |
| --- | --- | --- |
| `IUT-COR312-GEOMETRIC-TORSION-IDENTITIES` | `refer/iut/Iut/Torsion/Identities.lean`，`50329f16cd8ba55a4cad6df780c22a13d4dcc5bd` | `ArithmeticTeichmullerSpaces/Act1Scene1/IutCompat/Torsion/Identities.lean`；复制群律与除法多项式递推所需的纯域恒等式证书。 |
| `IUT-COR312-GEOMETRIC-TORSION-EDS` | `refer/iut/Iut/Torsion/EDS.lean`，`5f406dcd148a6e908c99f790f67cbf865891092f` | `ArithmeticTeichmullerSpaces/Act1Scene1/IutCompat/Torsion/EDS.lean`；复制 `good`、`smul_eq_zero_iff_eds` 等递推证明，将挠点条件接到除法多项式。 |
| `IUT-COR312-GEOMETRIC-TORSION-COUNT` | `refer/iut/Iut/Torsion/Count.lean`，`405008c4c62cf451d297393f7e24611cf44ca55e` | `ArithmeticTeichmullerSpaces/Act1Scene1/IutCompat/Torsion/Count.lean`；复制挠群有限性、纤维多项式计数、`card_torsionBy_eq_sq` 与 `torsionBasis`。原接口要求 `a₁ = a₃ = 0`、特征零、代数闭域及椭圆性。 |
| `IUT-COR312-GEOMETRIC-TORSION-BASIS` | 上述 `Count.lean`；另提取 `refer/iut/Iut/Tower/IntegralTorsion.lean` 的 `completeSquare`、`completeSquare_a₁`、`completeSquare_a₃`，提交 `869a7edc0305e18297c600b7d860f9679791d227` | `ArithmeticTeichmullerSpaces/Act1Scene1/IutGeometricTorsionBasis.lean`；沿已移植的 `Anabelian.vcEquiv` 运输挠群，证明一般椭圆曲线的 `iutGeometricTorsion_card` 与 `iutGeometricTorsionBasis`。`IutCurveModEllRepData.ofGeometricTorsion` 实际消费基存在定理，从曲线构造表示；`iutInitialThetaMaximalPrimeData_of_geometricTorsion` 再消费 S1.220 的局部 Tate/像链。该入口无需外部 torsion basis、表示、开核或 `hsl`，仍要求充分大素数及无循环子群条件。 |

这条代数证明适用于 JoshiTeich 使用的特征零数域曲线及其代数闭包；其陈述不含 theta、
体积或 Corollary 3.12。四个模块属于 `Scene1/Derived`，`Prologue-R5` 不变。
无循环子群来源、新 prime 的完整 theta 数据和真实 Scene1 满足模型仍须独立完成。

## S1.220：候选大素数的完整支撑像条件

| Source id | 本地声明 | 本地路径 | 来源、适配与边界 |
| --- | --- | --- | --- |
| `IUT-COR312-INITIAL-THETA-MAXIMAL-PRIME-IMAGE` | `iutInitialThetaMaximalPrimeLocalTateImageSource`, `iutInitialThetaMaximalPrime_exists_residueChar_ne_two_ell`, `iutInitialThetaMaximalPrime_sl_le_range`, `iutInitialThetaMaximalPrimeData_of_not_hasCyclicSubgroup` | `ArithmeticTeichmullerSpaces/Act1Scene1/IutInitialThetaMaximalPrimeImage.lean` | 适配 `refer/iut/Iut/Concrete/SL2Image.lean` 的 `prime_dvd_card_range`、`sl_le_range_of`，原文件提交 `47ef99c97945984ea799ee2333fcf920abecdae4`，Git 作者 Christian Merten，文件作者 The iut contributors，参考快照 `07cb1da58f6d428a670dbb5dd6093d428bcbcdd8`，保留 2026 版权与 Apache-2.0 通知。消费本地 S1.204 的全支撑 Tate 参数和素数界、S1.207 的循环子群判定、S1.211–215 的局部 Tate/分歧/像桥，并把派生的像条件交给 `iutInitialThetaMaximalPrimeData`（其参考构造为 `Iut/Concrete/Existence.lean` 的 `primeData`，提交 `a36b42b9a221e1baaf434bb76c85b3a0dfbf33a7`，同快照、作者与许可证）。候选 `ell` 与原 `D.prime.ℓ` 无需相同；在候选表示 fixed field 上由挠群基数和乘法约化派生 Tate structure，以 `j` 唯一性对齐完整 odd support 的 q 参数，以大素数界派生阶互素和剩余特征见证，最后在显式无循环子群条件下证明 `SL₂` 包含。新构造器不要求外部 `hsl`，不调用原 `prime.sl_le_range`。实际候选表示及无循环子群条件仍是显式来源；不构造新的 `InitialThetaData`、论文代表、去权或体积模型。属于 `Scene1/Derived`，不改变 `Prologue-R5`。 |

## S1.219：六个 SL2Image 移植文件的来源元数据勘误

日期：2026-10-12。审查范围仅为下面六个文件及其对应的来源登记。
旧值 `a2c25b2edbf5a9cbc30588b466a738b49547b443` 不含
`Iut/Concrete/SL2Image.lean`；正确的文件提交为
`47ef99c97945984ea799ee2333fcf920abecdae4`，Git 作者 Christian Merten。
参考快照仍为 `07cb1da58f6d428a670dbb5dd6093d428bcbcdd8`，文件版权为
2026 The iut contributors，许可证为 Apache-2.0。

权威 Git 证据（均在 `refer/iut` 中执行）：

- `git ls-tree a2c25b2edbf5a9cbc30588b466a738b49547b443 -- Iut/Concrete/SL2Image.lean`
  输出为空，说明旧提交没有该路径。
- `git log -1 --format='%H %an %s' 47ef99c97945984ea799ee2333fcf920abecdae4 -- Iut/Concrete/SL2Image.lean`
  返回正确提交、作者及 `[GenEll] Lemma 3.1(iii)` 的提交说明；
  `git show 47ef99c97945984ea799ee2333fcf920abecdae4:Iut/Concrete/SL2Image.lean`
  给出文件、版权、许可证和下表中的原定理。
- `git diff 47ef99c97945984ea799ee2333fcf920abecdae4 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8 -- Iut/Concrete/SL2Image.lean`
  输出为空，说明该文件与参考快照内容一致。

本地路径均相对于 `ArithmeticTeichmullerSpaces/Act1Scene1/`；原声明均位于
`Iut/Concrete/SL2Image.lean`，除 `Valued` 段外使用 `Iut.EllipticCurveData` 命名空间。

| 本地文件 | 原参考声明与适配范围 |
| --- | --- |
| `IutTateValuationBridge.lean` | `Valued` 段的 `valued_eq_of_norm_eq`、`valued_embedding`、`valued_of_isUniformizer`、`valued_q_toOrdered`、`valued_q_eq_inv_tateJ`；适配本地完成域赋值 API。 |
| `IutRamificationCardinality.lean` | `ramificationIdx'_dvd_card_gal`；适配表示 fixed field 的有限 Galois 基数桥。 |
| `IutLocalTorsionCardinality.lean` | `card_torsion_curveKw_ge`；适配局部挠群单射与基数下界。 |
| `IutRootClassRamification.lean` | `prime_dvd_ramificationIdx`；保持 Tate 参数对齐、structure、基数及互素条件为显式输入。 |
| `IutSL2ImageBridge.lean` | `prime_dvd_card_range`、`sl_le_range_of` 的群论尾部；由 `ell ∣ e(w'/w)` 推出像阶整除和 `SL₂` 包含。 |
| `IutSL2ImageSourceBridge.lean` | `prime_dvd_card_range`、`sl_le_range_of` 的来源装配；局部 Tate 证书限制在显式支撑上。 |

六个 Lean 文件只更正 `original-commit` 注释；声明、证明、导入和许可证通知未改。
对应登记另更正了整除方向，并注明 S1.218 仅在实际 `VBad` 拉回支撑上构造完整
source，完整 odd support 的互素阶仍需来源。旧进度日志保留；其他文件使用的
`a2c25b2...` 元数据不属于本次审查范围。

本次来源审查闭合，没有新增数学声明或边界变更：`Prologue-R5 → Prologue-R5`。
这些局部数论、Tate 和群论事实可供 JoshiTeich 使用；参考工程的完整 Corollary 3.12
及本项目 Scene1 的数学验收仍须独立完成。

## S1.229：局部 Tate/graph-line Vélu 比值增益

| Source id | 本地声明与路径 | 来源、适配与边界 |
| --- | --- | --- |
| `IUT-COR312-CYCLIC-TATE-GAIN` | `IutCyclicGain.exists_zpow_mul_mem_annulus`、`norm_X_le_of_annulus`、`one_le_norm_X`、`norm_X_le_one`、`norm_X_eq`、`node_bounds`、`minus_one_bounds`；`ArithmeticTeichmullerSpaces/Act1Scene1/IutCyclicGain.lean` | 移植 `refer/iut/Iut/Tripod/CyclicGain.lean` 的 Tate 坐标环带、节点和 `-1` 范数证明。原文件属于参考工程 Apache-2.0，版权/作者通知保留在本地文件的来源说明中；本地导入改为项目内 `ReferenceIut...TateStructure`，不导入参考工程。证明只使用本地 TateStructure 与 `tate-curves-theta` 的 TateParameter 范数 API，不复制 `Heights.VeluProduct`。 |
| `IUT-COR312-LOCAL-CYCLIC-TATE-RATIO` | `IutCyclicTate.xCoordinate_pointMap`、`map_xCoordinate_eq`、`exists_class`、`ratio_bound`、`ratio_mul_bound`；`ArithmeticTeichmullerSpaces/Act1Scene1/IutVeluTateGain.lean` | 适配 `refer/iut/Iut/Tripod/CyclicTate.lean` 的归一化 Tate class 与局部 graph-line 增益。比值定义替换为本地 S1.228 `IutCyclicVelu.veluRatio`，乘积不等式使用当前 Mathlib 的 `Finset.prod_le_one₀`/`prod_le_prod₀`。没有导入 `Heights.VeluProduct`、`CyclicBound` 或参考 `Iut` 命名空间；没有构造真实 InitialThetaData/TateFamily 来源、无穷处/其他有限处估计、高度/places 运输或全局 cyclic bound。属于 `Scene1/Derived`，`Prologue-R5` 不变。 |

## S1.230：真实 TateFamily graph-line 局部增益消费者

| Source id | 本地声明与路径 | 来源、适配与边界 |
| --- | --- | --- |
| `IUT-COR312-INITIAL-THETA-TATE-GAIN-CONSUMER` | `iutInitialThetaTateFamily_ratio_mul_bound`；`ArithmeticTeichmullerSpaces/Act1Scene1/IutInitialThetaTateGain.lean` | 消费本地 `IutInitialThetaTateFamily.iutInitialThetaTateFamilyOfTorsion` 所使用的 `TateFamily` 接口、`TateFamily.graphLineAt` 和 S1.229 `IutCyclicTate.ratio_mul_bound`。对实际 torsion-field 曲线和完成域 embedding，显式传入有限处、graph-line 子群、奇阶基数及两对二挠点/半点，使用 `BadPlaceNorm` 的 odd-support `‖2‖ = 1` 证书得到 completion-valued 比值界。没有证明原基域 places/范数运输、全局 product formula、高度或无穷处估计；没有导入参考工程或 `Heights.VeluProduct`。属于 `Scene1/Derived`，`Prologue-R5` 不变。 |
| `IUT-COR312-INITIAL-THETA-TATE-GAIN-BASE-CHANGE` | `ratio_mul_bound_of_positive_power_transport`、`iutCompletion_ratio_mul_bound_to_base`、`iutCompletion_ratio_mul_log_bound_to_base`；`ArithmeticTeichmullerSpaces/Act1Scene1/IutInitialThetaTateGainBaseChange.lean` | 消费 `iutEmbedCompletion` 的显式范数幂律证书，沿正的相对分歧指数取消 completion 局部增益中的幂，得到基域 completion-valued 比值界及其对数形式。比值下降等式和三个实际范数幂律仍是调用者来源义务；没有声称真实 `TateFamily` 比值已经下降，也没有构造全局有限处、height/places 或 product formula。属于 `Scene1/Derived`，`Prologue-R5` 不变。 |

## S1.232：单个四挠点 Vélu 比值的坐标域下降

| Source id | 本地声明与路径 | 来源、适配与边界 |
| --- | --- | --- |
| `IUT-COR312-FOUR-TORSION-VELU-SINGLE-RATIO-DESCENT` | `IutFourTorsion.exists_algebraMap_eq_veluRatio_of_four_nsmul`；`ArithmeticTeichmullerSpaces/Act1Scene1/IutFourTorsionVeluRatio.lean` | 在实际四挠坐标域的代数闭包中，消费 `galPointMap_eq_of_four_nsmul` 和 `IutCyclicVelu.veluRatio_galois`，对任意原基域 Galois-stable 有限子群和四挠点参数证明单个 Vélu 比值属于四挠坐标域。该入口不提供 completion 范数幂律、residue-degree 缩放、height/places 运输、无穷处或全局无循环子群界；属于 `Scene1/Derived`，`Prologue-R5` 不变。 |

## S1.233：共同坐标域单个 Vélu 比值的 inclusion 连接

| Source id | 本地声明与路径 | 来源、适配与边界 |
| --- | --- | --- |
| `IUT-COR312-CYCLIC-COORDINATE-SINGLE-RATIO-DESCENT` | `IutCyclicCoordinate.exists_inclusion_eq_veluRatio_of_four_nsmul`；`ArithmeticTeichmullerSpaces/Act1Scene1/IutCyclicCoordinateField.lean` | 对共同坐标域上的四挠点参数，消费 S1.232 的单比值下降和 `algebraMap_veluRatio`，沿四挠坐标域到共同坐标域的 `IntermediateField.inclusion` 得到值域等式。该连接不假设 completion 范数幂律，不处理 residue-degree accounting、height/places 运输、无穷处或全局上界；属于 `Scene1/Derived`，`Prologue-R5` 不变。 |

## S1.234：四挠坐标域代表到 completion embedding 的连接

| Source id | 本地声明与路径 | 来源、适配与边界 |
| --- | --- | --- |
| `IUT-COR312-CYCLIC-COORDINATE-COMPLETION-RATIO-CONNECTION` | `IutCyclicCoordinate.exists_completionEmbedding_eq_ratioProduct`；`ArithmeticTeichmullerSpaces/Act1Scene1/IutCyclicCoordinateField.lean` | 对共同坐标域上方有限处与四挠坐标域有限处的 `Ideal.LiesOver`，消费 `ratioProduct_eq_inclusion` 和 `iutEmbedCompletion_embedding`，把四挠坐标域代表的 completion embedding 等同于共同坐标域 `ratioProduct` 的 embedding。该入口只建立值连接，不提供范数幂律、residue-degree accounting、height/places 运输、无穷处或全局界；属于 `Scene1/Derived`，`Prologue-R5` 不变。 |

## S1.235：ratioProduct completion 值的赋值幂律

| Source id | 本地声明与路径 | 来源、适配与边界 |
| --- | --- | --- |
| `IUT-COR312-CYCLIC-COORDINATE-VALUED-RATIO-POWER` | `IutCyclicCoordinate.exists_valuedEmbedding_eq_ratioProduct_pow`；`ArithmeticTeichmullerSpaces/Act1Scene1/IutCyclicCoordinateField.lean` | 消费 S1.234 的 completion 值连接和 `iutValuedEmbedCompletion`，得到 `ratioProduct` 在共同坐标域上方处的赋值等于四挠坐标域代表赋值的相对分歧指数次幂。该入口明确不吸收 residue degree，不提供 completion 范数局部界、height/places 运输、无穷处或全局上界；属于 `Scene1/Derived`，`Prologue-R5` 不变。 |
| `IUT-COR312-CYCLIC-COORDINATE-NORM-THRESHOLD` | `IutCyclicCoordinate.exists_norm_lt_one_iff_ratioProduct`；`ArithmeticTeichmullerSpaces/Act1Scene1/IutCyclicCoordinateField.lean` | 消费 S1.235 的正相对分歧指数赋值幂律，将共同坐标域 `ratioProduct` completion 范数 `< 1` 与四挠坐标域代表 completion 范数 `< 1` 等价。该入口只闭合严格单位球阈值，不给出完整范数幂律，不吸收 residue degree，也不提供其他有限处或无穷处界、height/places 运输或全局上界；属于 `Scene1/Derived`，`Prologue-R5` 不变。 |

## S1.237：completion 范数完整幂律与 ratioProduct 消费者

| Source id | 本地声明与路径 | 来源、适配与边界 |
| --- | --- | --- |
| `IUT-COR312-COMPLETION-NORM-POWER-LAW` | `iutEmbedCompletion_norm_eq_pow`；`ArithmeticTeichmullerSpaces/Act1Scene1/IutCompletionSource.lean` | 在 IUT completion embedding 与 valuation transfer 上证明完整范数幂律，指数为相对 ramification index 与相对 inertial/residue degree 的乘积。消费 `Arithmetic.completionNorm_eq_residueChar_pow_of_valued`、`Arithmetic.inertDeg_eq_mul`，保留 residue-degree accounting；不构造全局 height/places、无穷处或 product-formula 界。属于 `Scene1/Derived`，`Prologue-R5` 不变。 |
| `IUT-COR312-CYCLIC-COORDINATE-NORM-POWER-LAW` | `IutCyclicCoordinate.exists_norm_eq_ratioProduct_pow`；`ArithmeticTeichmullerSpaces/Act1Scene1/IutCyclicCoordinateField.lean` | 消费 `exists_completionEmbedding_eq_ratioProduct` 与通用 completion 范数幂律，把共同坐标域 `ratioProduct` 的实际 completion 范数写成四挠坐标域代表范数的相对 ramification/residue degree 指数次幂。该入口不声称完成全局 height/places、无穷处估计或 product-formula 全局界；属于 `Scene1/Derived`，`Prologue-R5` 不变。 |

## S1.238：completion 负对数与完整有限处纤维 accounting

| Source id | 本地声明与路径 | 来源、适配与边界 |
| --- | --- | --- |
| `JT-SCENE1-COMPLETION-LOG-FIBER-ACCOUNTING` | `IutCyclicCoordinate.exists_negLog_norm_eq_ratioProduct_mul`（`Act1Scene1/IutCyclicCoordinateField.lean`）；`iutSum_relativeLocalDegree`、`iutNegLog_norm_embedding_sum_liesOver`、`IutCyclicCoordinate.exists_ratioProduct_negLog_fiber_accounting`（`Act1Scene1/IutCompletionLogAccounting.lean`） | 从 S1.237 的实际 completion 范数幂律和既有 Core `Arithmetic.sum_localDeg_liesOver` 推导。局部负对数系数为相对分歧指数与剩余次数的乘积；完整上方纤维的该系数和为扩张次数。实际消费者先选取一个满足 inclusion 等式的下降代表，再对所有完整纤维求和。JoshiTeich 适配范围仅为有限处范数/accounting，不提供论文代表选择、q-pilot 归一化、theta-volume 下界或 Corollary 3.12。证明 owner：Scene1；状态：proved，以本单元窄审计构建验证为准。 |

本轮没有复制新的 IUT 文件。使用本项目已经独立声明和证明的 completion、有限处和
Galois 下降 API；未增加 `refer/iut` 依赖。共同坐标域与四挠坐标域的实际 inclusion
在消费者类型中显式保留。纤维必须满足 `∀ v, v ∈ s ↔ Ideal.LiesOver ...`，因此
定理覆盖全部上方处，不能用于省略或重复上方处的列表。所有纤维使用同一个 `ρ`。
`Prologue-R5 → Prologue-R5`；Scene1 的纤维求和证明负担减少，前置信任负担不变。
真实 `InitialThetaData/TateFamily` 的完整 Scene1 模型、论文处集与归一化、packet/hull
定量体积 accounting 仍开放。

## S1.239：canonical Tate 字段到实际 q-pilot source

| Source id | 本地声明与路径 | 来源、适配与边界 |
| --- | --- | --- |
| `IUT-COR312-CANONICAL-SOURCE-FIELD-AUDIT` | `iutCanonicalBaseSource_tateParameter_eq_link`、`iutCanonicalBaseSource_qOrder_eq_link`、`IutQPilotSource.ofInitialThetaCanonicalTateData`；`Act1Scene1/IutInitialThetaCanonicalSourceAudit.lean` | 本地派生，消费 `IUT-COR312-INITIAL-THETA-BASE-QPILOT`、`IUT-COR312-INITIAL-THETA-ADELIC-LINK` 与 `IutQPilotSource.ofInitialThetaData_of_parameter_eq`。两个实际参数族都投影同一 `D.prime.tate`；q-order 从相同完成域元素的赋值派生。构造器由 `T.link.tate = iutInitialThetaTateParameterData D` 和显式 `QNormTateCompatibility` 推出完整 base carrier 与参数识别，不再单独接收 `hPlaces`、逐处 `hParameter`、`hLinkTateJ` 或完整 link equality。保留 `hEll`、Tate 数据等式和 q-norm 相容性为显式来源条件；不声称已构造完整 Scene1 满足模型。证明 owner：Scene1。 |

JoshiTeich 适配：III `ss:theta-data-fixing2`（TeX 1023–1031）说明初始数据与
代表处选择；`pr:admissible-lifts-tate-params`（1530–1539）说明 admissible lift 的
Tate 参数作用。本单元只识别当前完成域参数与初始椭圆曲线来源，不形式化该命题的
Fargues–Fontaine 商映射、直到域或 theta lift，不能代替其几何构造。上述字段等式
仅覆盖 `badPlacesOver(D.VBad)` 的 base `D.F` carrier；不把它等同于完整 odd support
或论文 torsion-field `L'` 的所选代表处。本轮没有复制新参考文件，没有新增 Lake 依赖。

`Prologue-R5 → Prologue-R5`，Core/Candidate/Obligations 未改。实际消费者是
`ofInitialThetaCanonicalTateData`，它把参数等式交给既有 source 构造器；其实际 q-order、
chosen uniformizer 和互素字段继续来自 `D.prime`。Scene1 在这一路径上无需额外证明
carrier、参数、j 身份三项独立证书；前置数学假设没有增加。完整
`Corollary312Scene1QPilotData`、raw/weighted 归一化和 packet/hull 体积证明仍开放。

S1.239 验证补记（2026-10-13 02:33:51 CST）：上述三个声明及窄审计目标通过，`9118/9118` jobs，退出码 `0`。三个公理输出仅有 `propext`、`Classical.choice`、`Quot.sound`。字段识别定理为 `proved`；实际 source 装配在显式 `hEll`、`hTate`、`hCompat` 下成立，完整真实 Scene1 模型仍 `open`。

## S1.240：实际 TateFamily q-root 的 completion norm certificate

| Source id | 本地声明与路径 | 来源、适配与边界 |
| --- | --- | --- |
| `JT-SCENE1-CANONICAL-QROOT-NORM-CERTIFICATE` | `CanonicalQRootNorm.baseIndex`、`norm_pow_eq_qNorm_pow`、`negLog_norm_eq_rawFactor_log_mul`、`norm_eq_rawFactor_pow`、`paperRootNorm`、`negLog_paperRootNorm_eq_paperFactor_log_mul`；`Act1Scene1/IutInitialThetaCanonicalQRootNorm.lean` | 本地派生；消费实际 `IutTorsionQRootSource.ofInitialThetaDataFromGlobal D` 的 `qroot_pow_eq` 和 canonical completionMap、S1.239 参数来源等式、S1.237 完整 completion 范数幂律、既有 `inertDeg_eq_mul` 及 `PaperQNormalizationBridge`。raw completion root norm 等于同源 base link 的 q-factor 的 `relativeRamification * relativeResidueDegree` 次幂。按两侧绝对剩余次数施行论文范数修正后，负对数系数为相对分歧指数。根方程与范数 certificate 均为 proof term，未接收 detached q-root 或 norm-law 输入。 |

依赖来源：`IUT-COR312-TATE-FAMILY-QROOT-ADAPTER`、`IUT-COR312-INITIAL-THETA-BAD-FINITENESS`、
`IUT-COR312-CANONICAL-SOURCE-FIELD-AUDIT`、`IUT-COR312-COMPLETION-NORM-POWER-LAW`、
`JT-ATS-III-COR312-PAPER-Q-NORMALIZATION`。Joshi III `ss:theta-data-fixing2`
（1023–1031）说明初始数据的 2ell-torsion 与根来源；`th:moccor-Mochizuki-form2`
（3617–3632）、`cor:cor312`（3647–3650）及既有登记的局部范数归一化位置说明转换的
目标作用。本单元不形式化论文全局 theta-values lift 或几何/体积构造。

`Prologue-R5 → Prologue-R5`；证明 owner：Scene1；局部状态以最终窄构建为 proved。
保留 `hTate`、`hCompat`、`hEll` 为显式目标来源条件；其在完整真实模型中的满足仍
open。base/torsion field 区分保留，baseIndex 为实际 contraction，不宣称与论文
独立代表处或最终 qIndex 相等。四个数学定理的实际消费者为 raw 范数/负对数定理间
的推导，以及论文范数修正消费者。窄审计与完整 ImportAudit 分别接入同一模块。
本轮没有复制新参考代码、没有增加 IUT 依赖，Scene1 certificate 输入负担减少而
前置信任负担不变；全局 q-sum、归一化冻结与 theta-volume 证明仍开放。

S1.240 验证补记（2026-10-13 02:57:22 CST）：四个数学定理及窄审计通过，`9130/9130` jobs，退出码 `0`；公理仅有 `propext`、`Classical.choice`、`Quot.sound`。局部范数 certificate 与其消费者状态 `proved`；完整真实来源模型、论文处集和最终归一化仍 `open`。用户要求本单元推送后暂停。

## S1.241：canonical InitialTheta Scene1 input boundary

| Source id | 本地声明与路径 | 来源、适配与边界 |
| --- | --- | --- |
| `IUT-COR312-CANONICAL-SCENE1-INPUT` | `CanonicalInitialThetaScene1Input`、`toScene1Input`、`toData`；`Act1Scene1/IutInitialThetaCanonicalScene1Input.lean` | 消费 `AdelicThetaLinkData.ofInitialThetaData`，将实际 `InitialThetaData.prime.tate` 产生的 canonical link 固定进 Scene1 input 类型。`places`、局部 Tate 参数、q-parameter 与 `j` 来源不再由调用者以独立 link 和 equality certificate 脱钩提供。theta、packet/hull、height、ramification、volume、Perfectoid bridge、Prologue laws、代表重数和 theta-volume accounting 仍是显式数据/义务；构造器不声称真实 `Corollary312Scene1QPilotData` 或最终 Corollary 3.12 已满足。 |

本单元没有修改 Prologue/Core、Candidate 或 `Prologue/Obligations`，`Prologue-R5 → Prologue-R5`。Scene1 的来源负担减少为在 canonical link 上提供剩余的 Perfectoid、theta/packet/hull、volume、q-family 和 accounting 数据；前置信任负担不增加。该类型的目的只是禁止一个独立 Scene1 link 在后续再用等式伪装成 IUT 来源。

窄构建补记（2026-10-13 09:45:57 CST）：

```sh
taskset -c 0-13 env LEAN_NUM_THREADS=10 lake build \
  ArithmeticTeichmullerSpaces.Prologue.Audit.Checks.CanonicalSource \
  ArithmeticTeichmullerSpaces.Act1Scene1.IutInitialThetaCanonicalScene1Input \
  ArithmeticTeichmullerSpaces
```

`9248/9248` jobs 通过，退出码 `0`；监控耗时 `268.315 s`，time 墙钟 `4:28.19`，
进程组 RSS 峰值 `17497636 KiB`（约 `16.69 GiB`），time 最大单进程 RSS `8233984 KiB`，
实际 Lean 并发峰值 `2`，CPU affinity `0-13`，每个 Lean 进程 `-j1`；未触发 `85 GiB`
停止阈值，未发现 Mathlib 编译。该结果只验证 canonical input 边界和其直接消费者；真实
Scene1 满足模型、论文 `V_p^oss`/`L'` 代表 accounting、packet/hull 到 theta-volume 的
定量证明及最终 Corollary 3.12 仍为 `open`。

S1.242 边界收紧补记（2026-10-13 10:23:02 CST）：

`CanonicalInitialThetaScene1Input` 不再接收完整 `inputLaws` 和重复的
`adelicThetaLink` 字段；其中的 Tate 法律改为由真实来源构造。canonical link 的 valuation scaling 由 `qNorm` 的定义与
`norm_pow` 推出，真实 Tate parameter laws 由
`iutInitialThetaTateParameterData_laws D` 投影；`toScene1Input` 内部构造
`PrologueInputLaws`。剩余 theta scaling、period/normalization、Perfectoid bridge、
height、packet/hull、volume 和 q-family obligations 仍显式开放，故没有关闭真实满足模型。

最终源码窄验证 `9248/9248` jobs，退出码 `0`；time 墙钟 `5:20.24`，监控耗时
`320.290 s`，进程组采样峰值 `17523440 KiB`（约 `16.712 GiB`），time 最大单进程 RSS
`8234044 KiB`，实际 Lean 并发峰值 `2`，affinity 修复 `42` 次，未发现 Mathlib 编译。

## S1.243：真实 q-root 到 theta log-shell 的符号审计

| Source id | 本地声明与路径 | 来源、适配与边界 |
| --- | --- | --- |
| `JT-SCENE1-THETA-LOG-SIGN-AUDIT` | `Scene1Input.logVolume_nonneg`、`one_le_thetaBase_norm`、`IutTorsionQRootSource.ofInitialThetaDataFromGlobal_qroot_norm_lt_one`、`Scene1Input.thetaBase_norm_ne_canonical_qroot_norm`；`Act1Scene1/ThetaLogSignAudit.lean` | 本地 proof terms 消费当前 FirstAxiom、theta scaling、period/log-shell、normalization 和 VolumeTransfer。根的严格单位球结论消费实际 `InitialThetaData` q-root 根方程、base Tate norm 和 canonical completion embedding。Joshi III `th:adelic-theta-link` 1139–1154 对照 untilt 估值缩放，3634–3650 的符号说明对照 `logVol` 与绝对值。排除把实际 q-root 范数直接作为当前 theta base norm 的装配；不排除其他来源模型，不构造 untilt、Frobenius、theta lift 或体积下界。 |

`Prologue-R5 → Prologue-R5`；Core、Candidate、Obligations 不改；没有复制 IUT 文件或
新增依赖。证明 owner：Scene1。负面证据消费实际 q-root，而不是合成 arithmetic witness；
它不构成完整真实满足模型。当前的普通 `norm_pow` 字段不证明不同 untilt 之间的估值
比较。已有 canonical input 是条件性装配载体，不能凭其可编译性认为来源义务已经完成。
Scene1 需要审查 theta norm 与正 log-volume 的对应关系；前置假设没有增加，
没有把目标等价界加入接口。最终状态和资源数据在 log4 的 S1.243 条目记录。

S1.243 验证补记（2026-10-13 10:50:42 CST）：一次受保护窄构建完成 `9224/9224`，
time 墙钟 `3:13.37`，监控耗时 `193.841 s`，进程组采样峰值 `25486804 KiB`，
time 最大单进程 RSS `8234244 KiB`，退出码 0。新模块及其直接消费者通过；三项
关键定理公理仅为 `propext`、`Classical.choice`、`Quot.sound`，无 `sorryAx`。
证明状态 proved，真实来源转换义务 open；Mathlib 未重编译。

## S1.244：实际 q-root 的归一化 theta witness 乘积估计

| Source id | 本地声明与路径 | 来源、适配与边界 |
| --- | --- | --- |
| `JT-ATS-III-NORMALIZED-THETA-WITNESS-PRODUCT` | `ThetaWitnessProduct.scale_mem_unitInterval`、`product_bounds`、`negLog_product_eq`、`negLog_product_bounds`、`ellStar_pos`、`paperRootNorm_pos_lt_one`、`canonical_qroot_witness_bounds`；`Act1Scene1/ThetaWitnessProduct.lean` | Joshi III 的 `th:moccor-Mochizuki-form1` 证明（3460–3486）明确使用 `j²/ellStar²`，`le:volume-lemma2`（3531–3543）与 `le:volume-lemma3`（3576–3583）给出加权乘积，3634–3650 区分 log-volume 符号。用本工程实际 canonical q-root 的 `paperRootNorm` 作为基准半径，`ellStar=(D.prime.ℓ-1)/2` 来自真实 prime。证明 `a^ellStar ≤ ∏j a^(γj*((j+1)/ellStar)^2)` 及 `0 ≤ -log(product) ≤ ellStar*(-log a)`。 |

权重仅要求 `[0,1]`，包含论文 `(0,1]` 情形；尚未构造 reciprocal local-field
degree 权重的来源，也未将这些实数半径实现为不同 untilt 的 theta/cohomology
值。完成的只是论文乘积估计的实数部分；Haar measure、张量 cross-norm、Bloch–Kato
logarithm、真实 hull 包含和 thetaVolume 识别仍开放。没有用 reciprocal root
替换原始 root，没有改变既有 Core、Scene1Input 或最终目标。

`Prologue-R5 → Prologue-R5`，owner Scene1。本地派生复用
`JT-SCENE1-THETA-LOG-SIGN-AUDIT`、`JT-SCENE1-CANONICAL-QROOT-NORM-CERTIFICATE`
与 Mathlib real power/log/product API；没有复制参考工程文件或增加依赖。
根的非零性与范数严格小于 1 来自实际源，未接受 detached norm certificate。
实际消费者为 `canonical_qroot_witness_bounds`；其 remaining weights 为显式参数。
最终验证与资源数据记入 log4。

S1.244 验证补记（2026-10-13 11:04:17 CST）：首次编译失败的两项实现问题已
集中修正；最终窄重试 `9225/9225` 通过，time 墙钟 `3:14.93`，监控耗时
`195.248 s`，组 RSS 采样峰值 `25594196 KiB`，time 单进程最大 RSS `8234560 KiB`。
`canonical_qroot_witness_bounds` 公理依赖仅含 Lean 标准三项；无 `sorryAx`。
实际 root 的数值 estimate proved；untilt/theta/hull/volume 来源仍 open，
Mathlib 未重编译。

## S1.245：实际 torsion completion 中的局部 p-adic 对数见证

| Source id | 本地声明与路径 | 来源、适配与边界 |
| --- | --- | --- |
| `JT-SCENE1-LOCAL-PADIC-LOG-WITNESS` | `LocalPadicLog` 的整数范数、对数级数收敛、余项估计、`norm_padicLog_one_add`、`normalizedLog_mem_logShell`、`norm_normalizedLog`；`Act1Scene1/LocalPadicLog.lean` | 独立移植 `refer/iut/Iut/Concrete/LocalConstruct/PadicLog.lean` 的选定证明段：快照中第 49–157、161–243、425–494 行。原始提交 `bc1c6e6c7ac4bcf0c363b9b1bbe9b6d7bc35bf9c`；参考快照 `07cb1da58f6d428a670dbb5dd6093d428bcbcdd8`；Git 作者 Christian Merten，文件作者 The iut contributors。复制前核查文件头及双方 LICENSE，保留 Apache-2.0 版权和许可证通知。改为独立 `JoshiTeich` 命名空间、精确 Mathlib 导入，新增小球范数等式及归一化见证证明。 |
| `JT-SCENE1-INITIAL-THETA-LOCAL-LOG-WITNESS` | `InitialThetaLogWitness.norm_residueChar_lt_one`、`value`、`value_mem_logShell`、`norm_value_eq_qroot_norm`、`value_ne_zero`；`Act1Scene1/IutInitialThetaLogWitness.lean` | 消费实际 `InitialThetaData` canonical q-root 来源及其非零、范数小于 1 的证明。Joshi III `le:elem-lemma` 和 `th:moccor-Mochizuki-form1` 证明中的 `eq:multiplicative-coh-class` 指示局部 logarithm 及后续 Bloch–Kato 识别的位置。本轮实现普通局部 logarithm；不声称证明该 cohomology 识别。 |

设实际完成域为 `k`，处的 residue prime 为 `p`，实际根为 `y`。构造主单位
`u=1+2*p*y` 以及 `z=(2*p)⁻¹*padicLog u`。证明 `‖u-1‖<1`、
`z∈logShell p`、`‖z‖=‖y‖` 和 `z≠0`。泛型证明要求显式的 rank-one
离散赋值、CharZero、CompleteSpace、`p.Prime`、`‖p‖<1` 和 `‖y‖≤1`；
消费者从 number-field completion 和 canonical root 派生这些条件，不接收脱钩的
范数证书。本轮未移植同态、满射、紧性或张量 packet 代码，不导入参考工程，
不增加 Lake 依赖。

`Prologue-R5 → Prologue-R5`，operation `derive`，owner Scene1。实际消费者为
`InitialThetaLogWitness` 的来源定理及 SceneBounds 审计。局部对数的收敛和小球
范数义务由 proof terms 承担，前置信任不增加；Bloch–Kato crystalline 类、不同
untilt/Frobenius、论文代表处与权重、真实 tensor/hull/volume 和 Corollary 3.12
满足模型仍 open。构建结果与动态边界记录见 log4 的 S1.245 条目。

S1.245 验证补记（2026-10-13 11:24:04 CST）：最终窄重试 `9227/9227` jobs
通过，time 墙钟 `3:22.27`，监控耗时 `202.476 s`，进程组 RSS 采样峰值
`25579300 KiB`（`24.394 GiB`），time 最大单进程 RSS `8235396 KiB`，退出码 0。
新来源定理及局部解析 proof terms 为 proved；两个新增最终消费者的公理仅为
`propext`、`Classical.choice`、`Quot.sound`。Mathlib 未重编译，完整真实
Scene1 模型与 Corollary 3.12 仍 open。

## S1.246：局部对数满射与实际来源整格球

| Source id | 本地声明与路径 | 来源、适配与边界 |
| --- | --- | --- |
| `JT-SCENE1-LOCAL-LOG-BALL` | `LocalPadicLog.exists_padicLog_eq`、`exists_normalizedLog_eq`、`normalizedLog_image_closedBall`、`closedBall_subset_logShell`、`mul_image_closedBall`；`Act1Scene1/LocalPadicLogBall.lean` | 独立移植 `refer/iut/Iut/Concrete/LocalConstruct/PadicLog.lean` 的 496–529 行：通过 `a ↦ y-logRem a` 的 Banach 不动点证明小球对数满射。原始提交 `bc1c6e6c7ac4bcf0c363b9b1bbe9b6d7bc35bf9c`，参考快照 `07cb1da58f6d428a670dbb5dd6093d428bcbcdd8`；Git 作者 Christian Merten，文件作者 The iut contributors。复制前核查该文件头与双方 LICENSE，保留 Apache-2.0 通知；独立命名空间及精确导入。新增归一化映满单位球、单位球包含于 log-shell 和标量球等式的本地证明。 |
| `JT-SCENE1-INITIAL-THETA-LOG-BALL` | `InitialThetaLogWitness.integralBall`、`integralBall_eq_closedBall`、`value_mem_integralBall`、`integralBall_subset_logShell`、`integralBall_subset_closedBall_iff`；`Act1Scene1/IutInitialThetaLogBall.lean` | 消费 S1.245 的实际 canonical q-root logarithm 见证。Joshi III `le:volume-lemma2`（3531–3543）使用 `lambda*O_E` 的标量整格。这里构造实际完成域中 `value D v * {x : ‖x‖≤1}`，证明它等于半径为实际 q-root 范数的闭球，包含实际见证并位于普通 log-shell；还证明包含见证的任一零中心范数球包含该整格球。 |

泛型满射证明以 CharZero、CompleteSpace、rank-one 离散赋值、`p.Prime` 和
`‖p‖<1` 为显式条件；实际消费者从完成域嵌入和 canonical source 派生这些条件。
在上述完成域设置中，标量球等式额外只要求标量非零，实际见证的非零性已有 proof term。该集合是实际
局部标量整格，未声称它等于论文 tensor hull、不同 untilt 的 theta locus，或
现有 `PacketHullData` 中的完整来源 hull。Haar measure、加权体积、Bloch–Kato
识别和全局 normalization 仍为 open。

`Prologue-R5 → Prologue-R5`，operation `derive`，owner Scene1。实际来源消费者
使用泛型单位球包含和标量球定理；SceneBounds 审计消费四项来源定理。没有新增
Lake 依赖、参考工程导入或 Core 契约。Scene1 的单位球来源与局部区域构造义务
减少，前置信任负担不增加。最终 proof status 和资源记录见 log4 的 S1.246 条目。

S1.246 验证补记（2026-10-13 11:33:16 CST）：一次受保护窄构建通过
`9229/9229` jobs，退出码 0；time 墙钟 `3:53.85`，监控耗时 `234.263 s`，
进程组采样 RSS 峰值 `25665416 KiB`（`24.476 GiB`），time 单进程最大 RSS
`8235812 KiB`。新定理及实际来源消费者为 proved，两个新增最终公理报告只有
`propext`、`Classical.choice`、`Quot.sound`；没有 Mathlib 编译或源码重试。

## S1.247：实际完成域的局部紧致与 Haar 整格球测度

| Source id | 本地声明与路径 | 来源、适配与边界 |
| --- | --- | --- |
| `JT-SCENE1-LOCAL-COMPLETION-PADIC-ALGEBRA` | `LocalCompletion.padicEmb`、`padicEmb_ratCast`、`continuous_padicEmb`、`finite_padicAlgebra`；`Act1Scene1/LocalCompletionPadicAlgebra.lean` | 独立移植参考 `Packet.lean` 选定段。原始提交 `4d2b6e926089b949109c69c28f13c7f878249c5d`，参考快照 `07cb1da58f6d428a670dbb5dd6093d428bcbcdd8`，Git 作者 Christian Merten，文件作者 The iut contributors。保留 Apache-2.0 文件头及许可证通知；只复制 residue characteristic、`ℚ_p` embedding、有限维性证明，不复制 packet/factor/tensor/archimedean 构造。 |
| `JT-SCENE1-LOCAL-COMPLETION-HAAR` | `exists_isCompact_closedBall_subset`、`instProperSpaceCompletionAt`、`integralUnitBall`、`normalizedHaar`、`normalizedHaar_unitBall`、`normalizedHaar_scalarBall`；`Act1Scene1/LocalCompletionHaar.lean` | 独立移植 `Integral.lean` 提交 `b76207ab8955e68a7408d5d2a770b75a30c3bebf` 和 `LogShell.lean` 提交 `fe96f99cae5c6d48d25113163f1b9b388fc35814` 的局部紧致/ProperSpace 段。用 Mathlib `Measure.addHaarMeasure` 归一化完成域单位闭球，标量球测度表达为 `distribHaarChar`，不把该特征自动识别成 completion norm。 |
| `JT-SCENE1-INITIAL-THETA-LOG-BALL-HAAR` | `integralBall_isCompact`、`integralBall_isOpen`、`integralBall_haar_eq`、`integralBall_haar_pos_lt_top`；`Act1Scene1/IutInitialThetaLogBallHaar.lean` | 消费实际 canonical q-root 对数整格球。证明实际球紧、开，且归一化 Haar 测度严格在 `(0,∞)`，测度等于见证标量的 `distribHaarChar`。论文 `le:volume-lemma1` 要求的有限正局部区域已构造；论文范数等式、不同 untilt、tensor product 和全局加权体积仍未证明。 |

完成域有限维性使实际 local field 获得 ProperSpace；单位闭球成为
`PositiveCompacts`，并据此定义归一化 Haar measure。实际整格球仍是
`value D v * {x | ‖x‖≤1}`，前轮已证明其为 q-root 范数闭球。当前测度结论
精确到 `distribHaarChar`，没有把缺失的范数-测度缩放恒等式伪装成完成结果。

`Prologue-R5 → Prologue-R5`，operation `derive`，owner Scene1。未修改 Core、
Candidate 或 Obligations；不增加 Lake 依赖，不导入参考工程。局部完成域的
有限维、紧致性、Haar 归一化和实际球正有限测度义务已减少，前置信任负担不增加。
Haar 特征与论文 completion norm 的识别、Bloch–Kato、不同 untilt、tensor
hull/volume 和最终 Corollary 3.12 仍 open。构建证据见 log4 的 S1.247。

S1.247 验证补记（2026-10-13 11:53:39 CST）：最终窄构建通过 `9232/9232`
jobs，time 墙钟 `5:41.23`，监控耗时 `341.739 s`，进程组 RSS 峰值
`25610140 KiB`（`24.424 GiB`），time 最大单进程 RSS `8236908 KiB`，退出码 0。
五个新增最终公理报告只有 `propext`、`Classical.choice`、`Quot.sound`；Mathlib
未重编译，完整真实 Scene1 模型与 Corollary 3.12 仍 open。

## S1.248：局部主理想指数与实际整格球 Haar 测度

| Source id | 本地声明与路径 | 来源、适配与边界 |
| --- | --- | --- |
| `JT-SCENE1-LOCAL-HAAR-PRINCIPAL-INDEX` | `LocalCompletion.integerRing`、`integerHaar`、`principalIndex`、`principalIdeal_isOpen`、`principalIndex_pos`、`principalIdeal_image`、`normalizedHaar_scalarBall_eq_inv_index`；`Act1Scene1/LocalCompletionHaarIndex.lean` | 本地 proof terms，消费冻结 Mathlib `AddSubgroup.index_mul_measure`、compact/open subgroup 的有限商定理及 valuation integer principal ideal API。Joshi III `le:volume-lemma1`（3505–3518）给出后续局部标量整格体积识别的位置。本轮将实际测度落实为有限加法指数倒数；不假设指数与 norm 的等式。 |
| `JT-SCENE1-INITIAL-THETA-LOG-BALL-INDEX` | `InitialThetaLogWitness.integralValue`、`integralValue_ne_zero`、`integralBall_index_pos`、`integralBall_haar_eq_inv_index`、`integralBall_haar_le_one`；`Act1Scene1/IutInitialThetaLogBallIndex.lean` | 实际 `InitialThetaData` canonical q-root 对数见证打包为整数环元素，非零性与整性从现有实际来源定理派生。实际整格球 Haar 测度等于主理想指数倒数，并证明测度不超过 1。 |

记实际完成域为 `k`，整数环为 `O=Valued.v.integer`，非零整元素为 `z`。
`(z)` 是 `O` 的紧致开加法子群，因此商群有限；`principalIndex w z`
是其加法指数。把归一化 Haar 沿整数环包含映射 comap 后，总测度为 1，
有限陪集分解给出 `index*(measure (z))=1`。主理想在完成域中的像正是
`z*{x | ‖x‖≤1}`，故其实际测度为指数倒数。实际消费者固定
`z=integralValue D v`，不接受脱钩的测度或范数证书。

本轮没有复制新的参考工程代码或增加依赖。`Prologue-R5 → Prologue-R5`，
operation `derive`，owner Scene1，Core/Candidate/Obligations 不改。
Scene1 局部 Haar 缩放因子的有限商计数义务减少；前置信任不增加。
`principalIndex` 与处范数/剩余域基数的识别、paper norm 修正、different untilt、
Bloch–Kato、tensor hull/global volume 及完整 Corollary 3.12 仍 open。
最终构建结果与失败记录见 log4 的 S1.248。

S1.248 验证补记（2026-10-13 14:52:20 CST）：最终窄构建 `9234/9234` jobs
通过，time 墙钟 `3:27.02`，监控耗时 `207.442 s`，组 RSS 峰值
`25603652 KiB`（`24.418 GiB`），time 最大单进程 RSS `8237320 KiB`，rc 0。
实际指数测度消费者与通用证明为 proved；新增最终公理报告仅含 Lean 标准三项。
Mathlib 未重编译，完整数学/审计目标仍 open。

## S1.249：实际局部主理想商同构与 Haar/norm 识别

| Source id | 本地声明与路径 | 来源、适配与边界 |
| --- | --- | --- |
| `JT-SCENE1-LOCAL-HAAR-NORM` | `LocalCompletion.globalIntegerMap`、`exists_globalInteger_norm_sub_lt`、`principalQuotientMap_surjective`、`principalQuotientMap_ker`、`principalQuotientEquiv`、`principalIndex_eq_absNorm_pow`、`normalizedHaar_scalarBall_toReal_eq_norm`；`Act1Scene1/LocalCompletionHaarNorm.lean` | 本地 proof terms；使用冻结 Mathlib 全局整数近似、完成域稠密性、第一同构定理、理想绝对范数幂律和现有 completion valuation norm 公式。Joshi III `le:volume-lemma1` 使用单位整数环归一化 Haar measure 与标量绝对值。本轮通过实际商同构计算完成域主理想的商基数，不再接受未知缩放因子作为范数证书。 |
| `JT-SCENE1-INITIAL-THETA-LOG-BALL-NORM` | `integralBall_index_eq_absNorm_pow`、`integralBall_haar_toReal_eq_qroot_norm`、`integralBall_haar_eq_qroot_norm`；`Act1Scene1/IutInitialThetaLogBallNorm.lean` | 消费实际 `InitialThetaData` canonical q-root 对数见证的整性、非零性、范数等式和 completionQOrder。证明实际整格球的归一化 Haar measure 等于 `ENNReal.ofReal ‖qroot‖`。这里是 raw completion norm，不自动等于已定义的 paperRootNorm。 |

对实际 `w : FinitePlace K`，若非零整元素 `z` 的估值为 `exp(-n)`，全局整数到
`integerRing w ⧸ (z)` 的映射满射，核为 `w.maximalIdeal.asIdeal^n`。满射由
先逼近一个域元素、再用 Mathlib 全局整数近似产生，未将 residue-field 对齐
作为显式假设。商同构计算加法指数 `absNorm(w)^n`，进而由 S1.248 的测度公式
得到标量整数球的实值测度等于其 completion norm。实际 logarithm 见证的 `n`
从其 completion valuation 派生。

`Prologue-R5 → Prologue-R5`，operation `derive`，owner Scene1。不复制新的
参考工程代码，不增加依赖，不改 Core/Candidate/Obligations。Scene1 的局部
有限商基数和 raw Haar/norm 识别义务减少，前置信任不增加。不同 untilt 的
normalized theta 值、Bloch–Kato、论文代表处与权重、paper norm 修正、tensor
hull/volume 和完整 Corollary 3.12 仍 open。最终验证状态和资源记录见 log4。

S1.249 验证补记（2026-10-13 15:09:43 CST）：修正两轮 API 表示错误后，
最终窄构建 `9236/9236` jobs 通过，rc 0；time 墙钟 `2:45.12`，监控耗时
`165.233 s`，组 RSS 峰值 `25613508 KiB`（`24.427 GiB`），time 最大单进程
RSS `8237712 KiB`。真实主理想商同构、raw Haar/norm 以及实际来源消费者为
proved；两个新增公理报告只有 Lean 标准三项。Mathlib 未重编译；完整真实
Scene1 模型、paper normalization 与 theta/tensor/hull/global volume 仍 open。

## S1.250：实际完成域张量整格与非零对数见证

| Source id | 本地声明与路径 | 来源、适配与边界 |
| --- | --- | --- |
| `JT-SCENE1-LOCAL-COMPLETION-TENSOR-LATTICE` | `LocalCompletion.Packet`、`Tensor`、`pure`、`pure_ne_zero`、`lattice`、`pure_mem_lattice`、`lattice_mono`、`unitLattice`、`tensorLogShell`、`unitLattice_le_tensorLogShell`；`Act1Scene1/LocalCompletionTensor.lean` | Joshi III `ss:weighted-vol`、`le:volume-lemma2`（3531–3543）、`le:volume-lemma3`（3576–3583）使用实际局部域 tensor product 与 integral lattices。参考 `LocalConstruct/Integral.lean` 与 `LogShell.lean` 的 integral-generator 模式作为 API 指引；没有复制新证明段或引入参考工程依赖。载体为有限元组实际完成域的 Mathlib `PiTensorProduct ℚ_[p]`，不是 Cartesian product。 |
| `JT-SCENE1-INITIAL-THETA-TENSOR-WITNESS` | `InitialThetaTensorWitness.packet`、`value`、`region`、`value_ne_zero`、`value_mem_region`、`region_le_unitLattice`、`region_le_tensorLogShell`、`value_mem_tensorLogShell`；`Act1Scene1/IutInitialThetaTensorWitness.lean` | 显式实际 canonical q-root 处元组 `c` 和共同 residue prime 条件 `hc`，在 torsionField 的真实完成域中形成 logarithm 值的纯张量。区域是各实际 integralBall 的纯张量的 `ℤ_p` 线性 span。证明见证非零、位于区域及 tensor log-shell，区域包含在 unitLattice 及 tensorLogShell 中。 |

每个完成域的 `ℚ_p` 结构由 S1.247 的连续 embedding 实现，有限维性由同一
实际来源链派生。张量的 `ℤ_p` 模结构从 `ℤ_p → ℚ_p` 限制标量。
非零性用各因子有限基的非零坐标及纯张量坐标乘积证明，没有接受张量非零证书。
单位球到普通 log-shell 的满射结果 S1.246 被实际 lattice containment 消费。
actual logarithm 见证与 integralBall 的来源均来自 S1.245–S1.246。

`Prologue-R5 → Prologue-R5`，operation `derive`，owner Scene1。Core、Candidate、
Obligations 不改，不新增依赖。Scene1 的实际张量载体、纯张量非零性及局部整格
区域到 tensor log-shell 的包含义务减少，前置信任不增加。元组 `c` 的论文
representatives/重数身份、不同 untilt theta 值、Bloch–Kato identification、
最大整序、hull、张量 Haar/weighted volume 和最终 thetaVolume 仍 open。
本轮不使用任意体积字段，也不把局部 lattice 宣称为论文完整 theta hull。

S1.250 验证补记（2026-10-13 15:28:22 CST）：修正两项 API 问题后，
最终窄构建 `9238/9238` jobs 通过，rc 0；time 墙钟 `3:28.38`，监控耗时
`208.528 s`，组 RSS 峰值 `25593264 KiB`（`24.408 GiB`），time 最大单进程
RSS `8238136 KiB`。九个数学定理及真实 tensor carrier 为 proved；两个新
来源消费者公理仅含 Lean 标准三项。Mathlib 未重编译，真实 theta realization、
tensor hull/volume、论文代表与全局 normalization 仍 open。

## S1.251：实际张量整格的紧致开放性与正有限 Haar 测度

| Source id | 本地声明与路径 | 来源、适配与边界 |
| --- | --- | --- |
| `JT-SCENE1-LOCAL-TENSOR-LATTICE-TOPOLOGY` | `Packet.tensorBasis`、张量 norm/ProperSpace/Borel 实例、`unitLattice_isBounded`、`exists_closedBall_subset_lattice`、`lattice_balls_isOpen`、`lattice_balls_isCompact`、`haar`、`lattice_balls_haar_pos_lt_top`；`Act1Scene1/LocalCompletionTensorTopology.lean` | 适配参考 `Packet.lean` 提交 `4d2b6e926089b949109c69c28f13c7f878249c5d` 的基坐标拓扑和 `Integral.lean` 提交 `b76207ab8955e68a7408d5d2a770b75a30c3bebf` 的有界 span、缩放基开放性路线；参考快照 `07cb1da58f6d428a670dbb5dd6093d428bcbcdd8`，Git 作者 Christian Merten，文件作者 The iut contributors。文件头保留 Apache-2.0 通知，移植前核查文件及双方 LICENSE。改为实际 completion factors 与任意正半径，省去 factor quotient、archimedean、maximal order 和 hull。 |
| `JT-SCENE1-INITIAL-THETA-TENSOR-REGION-TOPOLOGY` | `region_eq_ballLattice`、`region_isOpen`、`region_isCompact`、`region_haar_pos_lt_top`；`Act1Scene1/IutInitialThetaTensorRegion.lean` | 消费 S1.250 真实 q-root logarithm tensor region。各 factor radius 由实际 root norm 提供，正性和≤1均已由 canonical source 证明。Joshi III `le:volume-lemma2` 和 `le:volume-lemma3` 需要的 actual local tensor region 已具有紧致、开放及正有限 Haar 测度；未计算其定量体积。 |

有限维张量使用基坐标诱导的 normed topology；此拓扑是有限维 `ℚ_p` module
拓扑，但该范数不声称为 tensor cross-norm。因子整环球的紧致性与坐标连续性
给出 unitLattice 生成元有界性，ultrametric 和 `ℤ_p` scalar norm≤1 将有界性
提升到 integral span。缩放因子基进入指定正半径球，再重组 tensor basis，
证明 integral tensor lattice 包含一个零邻域，从而开、闭；半径≤1时有界，
因此紧致。实际 tensor Haar 来自 Mathlib `Measure.addHaar`，正有限性使用
开放与紧致，不接受体积 certificate。

`Prologue-R5 → Prologue-R5`，operation `derive`，owner Scene1。Core/Candidate/
Obligations 不改，不新增 Lake 依赖或参考模块导入。本轮减少实际 tensor region
的拓扑和正有限测度证明义务，前置信任不增加。张量测度归一化/定量缩放、
cross-norm、maximal order/hull、不同 untilt/Bloch–Kato、论文代表及权重和
最终 thetaVolume 仍 open。源码适配范围和最终验证证据见 log4 的 S1.251。

S1.251 验证补记（2026-10-13 15:47:06 CST）：修正实例重名、API 与精确模块
路径后，最终窄构建 `9240/9240` jobs 通过，rc0；time墙钟 `2:45.89`，监控
耗时 `166.253 s`，组RSS峰值 `25616836 KiB`（`24.430 GiB`），time单进程
最大RSS `8238872 KiB`。实际tensor region的紧致/开放/正有限Haar measure为
proved；两个新增最终消费者公理只有Lean标准三项。Mathlib未重编译。四次
尝试的失败与成功资源分别保存在log4；定量weighted tensor volume、hull与
完整Scene1仍open。

## S1.252：真实张量缩放像与整格归一化 Haar 公式

| Source id | 本地声明与路径 | 来源、适配与边界 |
| --- | --- | --- |
| `JT-SCENE1-LOCAL-TENSOR-SCALAR-IMAGE` | `Packet.factorScale`、`scale`、`continuousScale`、`scalarLattice`、`unitLattice_map_scale`、`unitLattice_image_scale`、`normalizedHaar`、`normalizedHaar_unitLattice`、`normalizedHaar_scalarLattice`；`Act1Scene1/LocalCompletionTensorScale.lean` | 本地 proof terms，Mathlib `PiTensorProduct.congr`、span map 与有限维连续线性自同构。Joshi III `le:volume-lemma2/3` 的标量整格形式；证明逐因子乘非零标量的实际自同构映单位整格到标量整格，再将单位整格测度归一为1，得到标量整格测度等于自同构 Haar 分布特征。 |
| `JT-SCENE1-INITIAL-THETA-TENSOR-SCALAR-IMAGE` | `InitialThetaTensorWitness.scale`、`region_eq_scaledUnitLattice`、`region_normalizedHaar_eq`、`region_normalizedHaar_pos_le_one`；`Act1Scene1/IutInitialThetaTensorScale.lean` | 所有标量是实际 canonical q-root ordinary logarithm 值，非零性由 S1.245 提供。实际 S1.250 tensor region 恰为该连续自同构的单位整格像，其单位整格归一化 Haar 测度严格正且≤1，并精确等于实际自同构的 `distribHaarChar`。 |

张量自同构在 pure tensors 上作用为 `⊗a_i ↦ ⊗(z_i*a_i)`，每个因子逆映射
是乘 `z_i⁻¹`，不假设 region/image 证书。`ℚ_p` 线性映射限制为 `ℤ_p` 线性
映射，span map 给出完整整格像等式，不只映一个见证。Haar normalization
选用实际 unitLattice 的 compact-open 证据，测度计算使用自同构的实际求值作用。

`Prologue-R5 → Prologue-R5`，operation `derive`，owner Scene1。没有新参考
代码移植、Lake依赖或Core/Candidate/Obligations变更。Scene1 的真实区域缩放
像与tensor基准测度归一化义务减少，前置信任不增加。当前精确结果仍含
`distribHaarChar`，尚未计算为逐factor norm及degree/weight的数值乘积；
unitLattice并非已识别的maximal order，论文hull、不同untilt/Bloch–Kato、
representatives、cross-norm和最终thetaVolume仍open。验证结果见log4。

S1.252 验证补记（2026-10-13 16:00:53 CST）：最终窄构建 `9242/9242` jobs
通过，rc0；time墙钟3:29.51，监控耗时209.869s，组RSS峰值25626112KiB
（24.439GiB），time最大单进程RSS8239432KiB。真实tensor scale/image、整格
Haar归一化和三个实际来源定理为proved；两项新增公理报告只有Lean标准三项。
Mathlib未重编译。character数值评价、maximal-order/hull及完整Scene1仍open。

## S1.253：真实张量整格有限指数与归一化 Haar 测度

| Source id | 本地声明与路径 | 来源、适配与边界 |
| --- | --- | --- |
| `JT-SCENE1-LOCAL-TENSOR-INTEGRAL-INDEX` | `Packet.unitHaar`、`scalarSubgroup`、`scalarIndex`、`scalarSubgroup_finiteIndex`、`scalarIndex_pos`、`normalizedHaar_scalarLattice_eq_inv_index`；`Act1Scene1/LocalCompletionTensorIndex.lean` | 本地 proof terms；Joshi III `le:volume-lemma2/3` 的实际张量整格，Mathlib `AddSubgroup.index_mul_measure`。单位张量整格紧致，非零逐factor缩放得到开标量整格；comap到单位整格后其加法商有限，从实际陪集计数证明测度等于指数倒数。 |
| `JT-SCENE1-INITIAL-THETA-TENSOR-INTEGRAL-INDEX` | `InitialThetaTensorWitness.regionIndex`、`regionIndex_pos`、`region_normalizedHaar_eq_inv_index`、`regionIndex_haar_product_eq_one`；`Act1Scene1/IutInitialThetaTensorIndex.lean` | 实际canonical logarithm标量固定了真实tensor region和加法子群商，非零性与norm≤1由q-root来源证明。归一化Haar区域测度等于实际`regionIndex`倒数，并证明指数乘测度为1。 |

`scalarSubgroup` 是实际标量整格在真实unitLattice中的comap加法子群，
不是自由指定的有限商。factor norm≤1证明完整标量整格包含于unitLattice，
因此子群的完成域像等于整个目标区域。测度沿包含映射comap到紧致unitLattice，
其总测度为1；有限陪集计数给出index*measure=1。这里的index尚未计算为
factor norm与degree的乘积；它与S1.252的Haar character是两个同一真实测度
的表达，不宣称完整定量乘积公式已经证明。

`Prologue-R5 → Prologue-R5`，operation `derive`，owner Scene1。没有新参考
代码复制、依赖或Core/Candidate/Obligations修订。Scene1的实际tensor区域测度
到有限加法指数的证明义务减少，前置信任不增加。指数的逐因子norm/degree
分解、论文weight/normalization、maximal-order/hull、不同untilt/Bloch–Kato和
最终thetaVolume仍open。资源与验证见log4的S1.253。

S1.253 验证补记（2026-10-13 16:18:31 CST）：两轮API表示错误修正后，最终
窄构建`9244/9244` jobs通过，rc0；time墙钟2:20.89，监控耗时141.088s，组RSS
峰值25613308KiB（24.427GiB），time最大单进程RSS8239788KiB。actual tensor
region的normalizedHaar有限指数公式和三个实际来源定理为proved；新增消费者
公理只有Lean标准三项。Mathlib未重编译。factor norm/degree指数计算与hull、
weighted global volume及完整Scene1仍open。

## S1.254：实际张量整格有限生成

| Source id | 本地声明与路径 | 来源、适配与边界 |
| --- | --- | --- |
| `JT-SCENE1-LOCAL-TENSOR-INTEGRAL-BASIS` | `Packet.bounded_module_finite`、`lattice_balls_span_eq_top`、`lattice_balls_isLattice`、`unitLattice_module_finite`、`lattice_balls_module_free`；`Act1Scene1/LocalCompletionTensorIntegralBasis.lean` | 本地 proof terms，消费 Mathlib 有限坐标模 Noetherian 性、有限无挠 PID 模自由性与 `Submodule.IsLattice`。S1.251 已证明的 actual integral tensor boundedness/scaled-basis 零邻域提供前提；这些通用定理通过窄构建，但本轮实际消费者只使用有限生成定理。 |
| `JT-SCENE1-INITIAL-THETA-TENSOR-INTEGRAL-BASIS` | `region_module_finite`；`Act1Scene1/IutInitialThetaTensorIntegralBasis.lean` | actual canonical q-root logarithm tensor region 的有限生成由实际 radius≤1 有界性和通用坐标注入定理派生。region 的 free module、满秩 span、整数基和 rational basis 仍是后续义务，未作为本轮结果记录。 |

任意有界 `ℤ_p` 子模块在基坐标中可统一乘 `p^m` 缩小到 `ℤ_p^N`；所得线性
坐标映射单射，因此由目标 Noetherian 有限模推出源有限生成。通用文件还证明
正半径整格的满秩与自由性，但实际 region 的 scalar-tower/`IsLattice` 实例
合成仍未稳定，故本轮只发布并消费 `region_module_finite`。

`Prologue-R5 → Prologue-R5`，operation `derive`，owner Scene1；没有新参考代码
复制、依赖或 Core/Candidate/Obligations 改动。Scene1 actual tensor region 的
有限生成义务减少，前置信任不增加。free module、满秩 span、integral/rational
basis、有限商 index 的 factor norm/degree 乘积评价、论文 weighted volume、
maximal-order/hull、untilt/Bloch–Kato 和最终 Corollary 3.12 仍 open；本轮不
宣称完整整数基或 index 公式已完成。验证结果见 log4。

## S1.255：实际张量整格自由模

| Source id | 本地声明与路径 | 来源、适配与边界 |
| --- | --- | --- |
| `JT-SCENE1-INITIAL-THETA-TENSOR-FREE` | `region_module_free`；`Act1Scene1/IutInitialThetaTensorIntegralBasis.lean` | 消费 S1.254 的 actual `region_module_finite` 与通用 tensor ambient `Module.IsTorsionFree`，调用 Mathlib 有限生成无挠 PID 模自由定理。实际 canonical q-root logarithm tensor region 因而为有限生成自由 `ℤ_[p]` 模；没有引入 detached basis、index 或 volume certificate。 |

`region_module_free` 只使用实际 region 的 boundedness（经 S1.254 finite-generation
证明）和 `ℚ_[p]` tensor 空间的无挠性。实际 `IsLattice`/scalar-tower 声明、满秩
rational span、integral/rational basis、factor norm/degree index 公式、论文
weighted volume、maximal-order/hull、untilt/Bloch–Kato 和最终 Corollary 3.12 仍 open。

`Prologue-R5 → Prologue-R5`，operation `derive`，owner Scene1；没有新参考代码复制、
依赖或 Core/Candidate/Obligations 改动。Scene1 actual tensor region 的 free-module
义务减少，前置信任不增加。验证结果见 `docs/开发计划.V1Act1log4.md` 的 S1.255。

## S1.256：实际张量整格的满秩 span

| Source id | 本地声明与路径 | 来源、适配与边界 |
| --- | --- | --- |
| `JT-SCENE1-INITIAL-THETA-TENSOR-FULL-SPAN` | `region_span_eq_top`；`Act1Scene1/IutInitialThetaTensorIntegralBasis.lean` | 将实际 q-root norm 正半径代入通用 `lattice_balls_span_eq_top`，证明 `ℚ_[p]` 张量空间中实际 region 的 span 为 top。半径正性来自实际 q-root 非零性；没有使用 volume、index、basis 或 hull 假设。 |

该声明只闭合 actual region 的 rational full-span。实际 `IsLattice` 结构的
scalar-tower 参数、具体 integral/rational basis、factor norm/degree index 公式、
论文 weighted volume、maximal-order/hull、untilt/Bloch–Kato 和最终 Corollary 3.12
仍 open。

`Prologue-R5 → Prologue-R5`，operation `derive`，owner Scene1；没有新参考代码复制、
依赖或 Core/Candidate/Obligations 改动。Scene1 actual tensor region 的 full-span
义务减少，前置信任不增加。验证结果见 `docs/开发计划.V1Act1log4.md` 的 S1.256。

## S1.257：实际张量整格 `IsLattice`

| Source id | 本地声明与路径 | 来源、适配与边界 |
| --- | --- | --- |
| `JT-SCENE1-INITIAL-THETA-TENSOR-ISLATTICE` | `region_isLattice`；`Act1Scene1/IutInitialThetaTensorIntegralBasis.lean` | 以实际 q-root 半径的正性和≤1性，将通用 `lattice_balls_isLattice` 实例化到 actual tensor region。声明显式固定 `ℤ_[p]`、`ℚ_[p]`、actual tensor carrier、module 实例和两个 scalar-tower 参数，避免隐式实例合成掩盖载体。 |

`region_isLattice` 闭合 actual tensor region 的有限生成、`ℚ_[p]` full span 与
`Submodule.IsLattice` 结构接口，但不构造具体 `Module.Basis`、不计算 factor
norm/degree index，也不识别 maximal order 或 hull。weighted volume、untilt/
Bloch–Kato 和最终 Corollary 3.12 仍 open。

`Prologue-R5 → Prologue-R5`，operation `derive`，owner Scene1；没有新参考代码复制、
依赖或 Core/Candidate/Obligations 改动。Scene1 actual tensor lattice 的结构性
前提减少，前置信任不增加。验证结果见 `docs/开发计划.V1Act1log4.md` 的 S1.257。

## S1.258：实际张量整格的 canonical free basis

| Source id | 本地声明与路径 | 来源、适配与边界 |
| --- | --- | --- |
| `JT-SCENE1-INITIAL-THETA-TENSOR-FREE-BASIS` | `regionFreeBasis`；`Act1Scene1/IutInitialThetaTensorIntegralBasis.lean` | 在定义体内安装实际 `region_module_free`，调用 Mathlib `Module.Free.chooseBasis`，得到索引为 `Module.Free.ChooseBasisIndex ℤ_[p] (region D p c hc)` 的实际 `Module.Basis`。该 basis 来自 actual region 的证明，不是外部输入；其索引有限性和 `Fin n` 重标号仍待后续单元。 |

该声明闭合 actual region 的 canonical free basis 选择，但不把 `ChooseBasisIndex`
误称为有限 `Fin n`，也不计算 basis index 的 factor norm/degree 公式。论文
weighted volume、maximal-order/hull、untilt/Bloch–Kato 和最终 Corollary 3.12 仍 open。

`Prologue-R5 → Prologue-R5`，operation `derive`，owner Scene1；没有新参考代码复制、
依赖或 Core/Candidate/Obligations 改动。Scene1 actual tensor integral-basis
前提减少，前置信任不增加。验证结果见 `docs/开发计划.V1Act1log4.md` 的 S1.258。

## S1.259：实际张量整格有限秩 `Fin` 基

| Source id | 本地声明与路径 | 来源、适配与边界 |
| --- | --- | --- |
| `JT-SCENE1-INITIAL-THETA-TENSOR-FIN-BASIS` | `regionFinBasis`；`Act1Scene1/IutInitialThetaTensorIntegralBasis.lean` | 在定义体内安装实际 `region_module_free` 和 `region_module_finite`，调用 Mathlib `Module.finBasis ℤ_[p]`，得到 `Module.Basis (Fin (Module.finrank ℤ_[p] (region D p c hc))) ℤ_[p] (region D p c hc)`。该基由 actual region 的证明生成，没有外部 basis 或 cardinal 输入。 |

该声明闭合 actual region 的有限秩整数基选择，并保留 `Module.finrank` 作为实际
秩；尚未把该秩计算为 tensor factor degree/norm 乘积，也未接入 finite-index Haar
公式、paper weighted volume、maximal-order/hull、untilt/Bloch–Kato 或最终
Corollary 3.12。

`Prologue-R5 → Prologue-R5`，operation `derive`，owner Scene1；没有新参考代码复制、
依赖或 Core/Candidate/Obligations 改动。Scene1 actual tensor integral-basis
接口进一步闭合，前置信任不增加。验证结果见 `docs/开发计划.V1Act1log4.md` 的 S1.259。

## S1.260：实际张量整格秩等式

| Source id | 本地声明与路径 | 来源、适配与边界 |
| --- | --- | --- |
| `JT-SCENE1-INITIAL-THETA-TENSOR-FINRANK` | `region_finrank_eq_tensor_finrank`；`Act1Scene1/IutInitialThetaTensorIntegralBasis.lean` | 显式使用 actual `region_isLattice`、`IsFractionRing ℤ_[p] ℚ_[p]` 和 `Submodule.IsLattice.rank'`，再将 rank 等式转换为 finrank 等式，得到 `Module.finrank ℤ_[p] (region D p c hc) = Module.finrank ℚ_[p] (packet D p c hc).Tensor`。factor finite-dimensional instances来自实际 completion factors。 |

该声明把实际有限基的秩连接到 ambient completion tensor 的维数，但没有把 ambient
finrank 展开为 factor degree 乘积，也没有计算 actual finite-index Haar、weighted
volume、maximal-order/hull、untilt/Bloch–Kato 或最终 Corollary 3.12。

`Prologue-R5 → Prologue-R5`，operation `derive`，owner Scene1；没有新参考代码复制、
依赖或 Core/Candidate/Obligations 改动。Scene1 actual tensor lattice 的秩会计义务
减少，前置信任不增加。验证结果见 `docs/开发计划.V1Act1log4.md` 的 S1.260。

## S1.261：张量维数乘积与实际整格秩

| Source id | 本地声明与路径 | 来源、适配与边界 |
| --- | --- | --- |
| `JT-SCENE1-LOCAL-TENSOR-FACTOR-FINRANK` | `Packet.tensor_finrank_eq_factor_prod`；`Act1Scene1/LocalCompletionTensorIntegralBasis.lean` | Mathlib `Module.finrank_eq_card_basis` 与 `Fintype.card_pi`；本地实际 completion tensor 的 `tensorBasis` 索引为 `∀ i, Fin (Module.finrank ℚ_[p] (P.Factor i))`。得到 `Module.finrank ℚ_[p] P.Tensor = ∏ i, Module.finrank ℚ_[p] (P.Factor i)`，不接收维数乘积证书。 |
| `JT-SCENE1-INITIAL-THETA-TENSOR-FACTOR-FINRANK` | `region_finrank_eq_factor_prod`；`Act1Scene1/IutInitialThetaTensorIntegralBasis.lean` | 消费通用张量维数公式和 S1.260 实际整格/ambient 秩等式。实际 canonical q-root region 的 `ℤ_[p]` 秩等于 tuple 中各实际完成域的 `ℚ_[p]` 维数之积。每个 factor 的 module 明确使用 `LocalCompletion.padicAlgebra (P.residueChar_eq i)`，其中 `P = packet D p c hc`。 |

本轮闭合实际 tuple 的张量维数乘积及整格秩公式，服务于 Joshi III
`le:volume-lemma2/3` 后续张量测度缩放的维数计数。局部维数尚未识别为论文
local-degree/residue-degree 表达，tuple 尚未识别为论文 representatives；该公式
也未评价缩放 determinant、`regionIndex` 或 weighted Haar volume。

`Prologue-R5 → Prologue-R5`，operation `derive`，owner Scene1。没有新参考代码
复制、Lake 依赖或 Core/Candidate/Obligations 改动；两个声明有实际生产者/消费者
关系。Scene1 的局部维数计数义务减少，前置信任不增加。rational basis extension、
factor norm/degree 指数公式、maximal-order/hull、不同 untilt/Bloch–Kato、论文
处集权重和最终 Corollary 3.12 仍 open。验证与资源见 log4 的 S1.261。

## S1.262：实际整数基的有理扩张与整格恢复

| Source id | 本地声明与路径 | 来源、适配与边界 |
| --- | --- | --- |
| `JT-SCENE1-INITIAL-THETA-TENSOR-RATIONAL-BASIS` | `regionRationalBasis`、`regionRationalBasis_apply`、`regionRationalBasis_integral_span`；`Act1Scene1/IutInitialThetaTensorIntegralBasis.lean` | 消费实际 `regionFinBasis`、`region_isLattice` 和 `IsFractionRing ℤ_[p] ℚ_[p]`，调用 Mathlib `Module.Basis.extendOfIsLattice`，把同一组向量扩张为整个实际 `ℚ_[p]` tensor 空间的基；其索引保持 `Fin (Module.finrank ℤ_[p] (region D p c hc))`。`Submodule.map_span` 证明扩张基的 `ℤ_[p]` span 恰为原 region。 |

新基没有自由给定的向量、matrix 或 normalization 字段。向量求值定理识别每个
rational basis vector 为实际 integral basis vector 的 subtype inclusion，整格
恢复定理将生产者输出接回真实 canonical q-root region。该接口服务于 Joshi III
`le:volume-lemma2/3` 后续区域缩放矩阵/determinant 计算，并未评价 determinant、
factor norm 或 `regionIndex`，也不识别论文 representatives/maximal-order/hull。

`Prologue-R5 → Prologue-R5`，operation `derive`，owner Scene1。没有新参考代码
移植、Lake 依赖或 Core/Candidate/Obligations 改动。actual rational-basis extension
及 integral-span 恢复义务减少，前置信任不增加。局部维数到 degree 的识别、
scaled-index 数值评价、论文权重、不同 untilt/Bloch–Kato、真实 q-pilot 满足模型、
thetaVolume 与最终 Corollary 3.12 仍 open。验证状态和资源见 log4 的 S1.262。

## S1.263：实际张量缩放矩阵与基无关行列式

| Source id | 本地声明与路径 | 来源、适配与边界 |
| --- | --- | --- |
| `JT-SCENE1-LOCAL-TENSOR-SCALE-MATRIX` | `Packet.scaleMatrix`、`scaleMatrix_apply`、`scaleMatrix_det_eq`、`scaleMatrix_det_ne_zero`；`Act1Scene1/LocalCompletionTensorScaleMatrix.lean` | 使用实际 factor tensor basis 与 `PiTensorProduct.congr` 缩放，矩阵每项为各 factor 的 `Module.finBasis` 坐标之积。Mathlib `LinearMap.toMatrix_apply`、`Basis.piTensorProduct_repr_tprod_apply`、`LinearMap.det_toMatrix` 和 `LinearEquiv.isUnit_det` 证明该矩阵行列式等于实际缩放自同构行列式且非零。 |
| `JT-SCENE1-INITIAL-THETA-TENSOR-SCALE-MATRIX` | `InitialThetaTensorWitness.scaleMatrix`、`scaleMatrix_det_eq`、`scaleMatrix_det_ne_zero`、`scaleMatrix_det_eq_regionBasis`；`Act1Scene1/IutInitialThetaTensorScaleMatrix.lean` | 标量全部是 actual canonical logarithm 值，非零性由实际 q-root source 提供。消费 generic matrix，并证明其行列式等于 S1.262 的 actual region rational basis 下同一缩放的行列式；不接收 detached matrix 或 determinant 字段。 |

本地 proof terms，无新的 IUT 代码复制或参考工程导入。为 Joshi III
`le:volume-lemma2/3` 后续缩放测度会计提供实际矩阵/行列式接口；当前只展开
矩阵项，尚未将 determinant 评价为逐 factor field-norm/degree 乘积，也未将
其范数连接到 `distribHaarChar`、`regionIndex` 或 paper weighted volume。

`Prologue-R5 → Prologue-R5`，operation `derive`，owner Scene1。两个新叶子模块
不改 Core/Candidate/Obligations 或 Lake 依赖，generic producer 被实际消费者
使用，实际 region basis 参与最终行列式等式。Scene1 的矩阵连接义务减少，
前置信任不增加。local/residue degree、论文 representatives/权重、
maximal-order/hull、不同 untilt/Bloch–Kato、真实 q-pilot/thetaVolume 和最终
Corollary 3.12 仍 open。验证与资源见 log4 的 S1.263。

## S1.264：实际 factor 乘法矩阵与域范数

| Source id | 本地声明与路径 | 来源、适配与边界 |
| --- | --- | --- |
| `JT-SCENE1-LOCAL-TENSOR-FACTOR-NORM` | `Packet.factorMulMatrix`、`factorMulMatrix_apply`、`factorMulMatrix_det_eq_norm`、`factorMulMatrix_det_ne_zero`、`factorMulMatrix_det_algebraMap`、`scaleMatrix_eq_factorMul_prod`；`Act1Scene1/LocalCompletionTensorScaleMatrix.lean` | 用实际 completion 的有限 `Module.finBasis` 构造 `Algebra.leftMulMatrix`，由 Mathlib `norm_eq_matrix_det` 识别 determinant 为 `Algebra.norm ℚ_[p]`。非零标量的 unit 经 norm hom 给出非零 determinant；基域标量的 norm 为 `a ^ Module.finrank`。S1.263 tensor coordinate 公式给出 tensor matrix 项是这些 factor matrix 项之积。 |
| `JT-SCENE1-INITIAL-THETA-TENSOR-FACTOR-NORM` | `factorLogMulMatrix`、`factorLogNorm`、`factorLogMulMatrix_det_eq_norm`、`factorLogMulMatrix_det_ne_zero`、`scaleMatrix_eq_factorLogMul_prod`；`Act1Scene1/IutInitialThetaTensorScaleMatrix.lean` | 将实际 canonical logarithm scalar 代入 generic multiplication matrix，证明 determinant 等于 source completion 的实际 algebraic norm 且非零，actual tensor scaleMatrix 逐项是 factor matrices 的乘积。`factorLogNorm` 明确使用 `LocalCompletion.padicAlgebra (P.residueChar_eq i)`，`P = packet D p c hc`；不接收 detached norm/determinant certificate。 |

`Algebra.norm` 的值位于 `ℚ_[p]`，它是域扩张范数，与 completion 的实数范数
`‖x‖`、paper-normalized norm 和 Haar character 的关系尚须证明；本轮不将这些
量混同。tensor determinant 的 factor-norm 幂乘积也尚未闭合，当前只识别各
factor determinant，并把 factor matrices 接入同一 actual tensor matrix。

本地 proof terms，无新 IUT 代码复制或参考工程依赖。数学用途是 Joshi III
`le:volume-lemma2/3` 的后续 tensor determinant/volume 会计。`Prologue-R5 →
Prologue-R5`，operation `derive`，owner Scene1；不改 Core/Candidate/Obligations
或 Lake 依赖。factor norm 接口义务减少，前置信任不增加。Haar/index 数值评价、
local/residue degree、论文处集代表和 normalization、maximal-order/hull、不同
untilt/Bloch–Kato、真实 q-pilot/thetaVolume 及最终 3.12 仍 open；验证见 log4。

## S1.265：完整张量行列式的 factor-norm 幂乘积

| Source id | 本地声明与路径 | 来源、适配与边界 |
| --- | --- | --- |
| `JT-SCENE1-FINITE-TENSOR-MATRIX-DETERMINANT` | `FiniteTensorMatrix.product`、`otherDimension`、`product_det`；`Act1Scene1/FiniteTensorMatrixDeterminant.lean` | 本地 finite-type induction proof。通过类型等价的重标号不变性和 `Equiv.piOptionEquivProd`，将有限 tensor matrix 逐个分解为 binary Kronecker product，应用 Mathlib `Matrix.det_kronecker`。`det(product A) = ∏ i, det(A i) ^ otherDimension d i`，`otherDimension d i = ∏ j, if j = i then 1 else d j`。空 tuple 与零维 factor 统一包含，不使用维数除法。 |
| `JT-SCENE1-LOCAL-TENSOR-DETERMINANT-NORM-PRODUCT` | `Packet.scaleMatrix_det_eq_factor_norm_prod`；`Act1Scene1/LocalCompletionTensorScaleMatrix.lean` | 消费 generic tensor-matrix determinant 公式、S1.264 的 tensor/factor matrix 项等式及 actual completion multiplication determinant/norm 等式。实际 tensor-scale 行列式等于各 actual `Algebra.norm ℚ_[p] (z i)` 的幂乘积，指数是其他 completion factor 维数之积。 |
| `JT-SCENE1-INITIAL-THETA-TENSOR-DETERMINANT-NORM-PRODUCT` | `InitialThetaTensorWitness.scaleMatrix_det_eq_factorLogNorm_prod`；`Act1Scene1/IutInitialThetaTensorScaleMatrix.lean` | 固定 actual canonical logarithm scalars，将完整 tensor-scale determinant 评价为 actual `factorLogNorm` 的幂乘积；指数明确用 source completion `padicAlgebra` 下的 `ℚ_[p]` finrank。没有 detached determinant-product 或 index certificate。 |

本轮闭合完整 tensor determinant 的代数域范数幂乘积。范数结果和 determinant
均位于 `ℚ_[p]`；其 p-adic absolute norm 到 completion 实数范数/local-degree/
residue-degree 的归一化以及 Haar/index 评价仍 open。论文 representatives/重数/
权重、maximal-order/hull、不同 untilt/Bloch–Kato、真实 q-pilot 满足模型、
thetaVolume 和最终 Corollary 3.12 仍未闭合，不能由此宣布完整体积公式已完成。

服务于 Joshi III `le:volume-lemma2/3` 的 tensor-volume 缩放计算，本地 proof terms，
无新 IUT 代码移植。`Prologue-R5 → Prologue-R5`，operation `derive`，owner Scene1；
不改 Core/Candidate/Obligations、Lake 依赖或冻结 Mathlib。新 generic producer 经
completion consumer 接入 actual q-root region 的缩放，Scene1 的 determinant
乘积义务减少，前置信任不增加。资源及验证见 log4 的 S1.265。

## S1.266：p-adic Haar 维数缩放与实际 tensor region

| Source id | 本地声明与路径 | 来源、适配与边界 |
| --- | --- | --- |
| `JT-SCENE1-PADIC-HAAR-DIMENSION-SCALING` | `PadicHaar.measure_preimage_mul_padic`、`pi_measure_preimage_smul_padic`、`measure_preimage_smul_padic`、`measure_image_smul_padic`；`Act1Scene1/PadicHaarScaling.lean` | 逐文件适配 `refer/iut/Iut/Concrete/LocalConstruct/Haar.lean`，原提交 `4d2b6e926089b949109c69c28f13c7f878249c5d`，Git 作者 Christian Merten，文件作者 The iut contributors，参考快照 `07cb1da58f6d428a670dbb5dd6093d428bcbcdd8`。复制前核查文件头及双方 Apache-2.0 LICENSE，保留版权、许可证及 provenance。只选取真实 p 个 integral cosets 计数、product Haar 和有限维 coordinate transport；本地独立 namespace、精确 imports、新增 image-scaling corollary。不导入参考工程、reference packet 或 volume。 |
| `JT-SCENE1-INITIAL-THETA-TENSOR-HAAR-DIMENSION-SCALING` | `region_haar_image_smul_padic`、`region_haar_image_smul_padic_factor_prod`、`region_haar_image_smul_padic_eq_inv_index`；`Act1Scene1/IutInitialThetaTensorHaarScaling.lean` | 对真实 canonical q-root region 及实际 unitLattice-normalized Haar 应用有限维 p-adic scaling。`μ(p • region) = p^(-dim tensor) * μ(region)`，再消费 S1.261 维数乘积和 S1.253 finite-index 公式。measurability 来自 actual compact region；finite-dimensionality 来自 actual completion factors，不接收 measure/index scaling certificate。 |

这是一般 determinant/Haar 连接的 prime-scalar 步骤，适用于 Joshi III
`le:volume-lemma2/3` 后续 tensor volume normalization。参考文件另提到 IUT III
Proposition 3.9 的 log-volume 用途；本地不接受该论文 normalization 为假设，
只使用有限陪集计数的独立数学证明。固定 Mathlib 的实空间 Haar/determinant
定理无法直接用于 `ℚ_p`；任意矩阵、自同构和 algebraic norm 的 absolute-value
测度公式仍需独立证明，当前结果不替代它们。

`Prologue-R5 → Prologue-R5`，operation `derive`，owner Scene1。无新 Lake 依赖，
Core/Candidate/Obligations 不改；generic producer 被实际 tensor region 消费。
Scene1 的 prime-scalar Haar 维数归一化义务减少，前置信任不增加。一般
determinant/Haar、completion norm/local-degree 归一化、论文 representatives/
重数/权重、maximal-order/hull、不同 untilt/Bloch–Kato、真实 q-pilot/thetaVolume
与最终 Corollary 3.12 仍 open。编译与审计状态、资源见 log4 的 S1.266。

## S1.267：实际 index/Haar 无分母 accounting

| Source id | 本地声明与路径 | 来源、适配与边界 |
| --- | --- | --- |
| `JT-SCENE1-INITIAL-THETA-TENSOR-INDEX-HAAR-ACCOUNTING` | `regionIndex_pow_finrank_mul_region_haar_image_smul_eq_one`；`Act1Scene1/IutInitialThetaTensorHaarScaling.lean` | 组合 S1.253 的 `regionIndex_haar_product_eq_one`、S1.261 actual tensor finrank 和 S1.266 p-adic Haar image scaling，证明 `regionIndex * p^dim * μ(p • region) = 1`。全式在 `ENNReal` 中以非零/非顶条件逐项消去，不引入新的 index 或 measure certificate。 |

该恒等式是后续数值 index、determinant 和 weighted volume accounting 的无分母
接口；它尚未计算 `regionIndex` 的 factor norm/degree 公式，也未把 `p^dim`
替换为论文 local-degree normalization。论文 representatives/重数/权重、
maximal-order/hull、不同 untilt/Bloch–Kato、真实 q-pilot/thetaVolume 与最终
Corollary 3.12 仍 open。

`Prologue-R5 → Prologue-R5`，operation `derive`，owner Scene1；无新参考代码、
Lake 依赖或 Core/Candidate/Obligations 变更。实际 index/Haar accounting 义务
减少，前置信任不增加。验证资源见 log4 的 S1.267。

## S1.268：common p-adic scalar 的 tensor determinant bridge

| Source id | 本地声明与路径 | 来源、适配与边界 |
| --- | --- | --- |
| `JT-SCENE1-LOCAL-TENSOR-COMMON-PADIC-SCALAR-DETERMINANT` | `scaleMatrix_det_common_algebraMap`；`Act1Scene1/LocalCompletionTensorScaleMatrix.lean` | 将每个 factor scalar 固定为同一个 `a : ℚ_[p]` 的 algebraMap，消费 S1.265 factor norm 幂公式和 `Algebra.norm_algebraMap`，证明 tensor-scale determinant 为 `a ^ (Fintype.card ι * ∏ i, Module.finrank ℚ_[p] (P.Factor i))`。`otherDimension` 的总和用 finite product erase 恒等式，无维数除法。 |
| `JT-SCENE1-INITIAL-THETA-COMMON-PADIC-SCALAR-DETERMINANT` | `commonPadicScaleMatrix`、`commonPadicScaleMatrix_det_eq_pow`、`commonPadicScaleMatrix_det_eq_prime_pow`；`Act1Scene1/IutInitialThetaTensorScaleMatrix.lean` | 实例化 actual packet 的 common scalar matrix，并特别得到 `a = p` 的实际 determinant 幂公式。factor algebra/module instances 明确来自实际 completion `padicAlgebra`；未将该 common-factor map 误称为 general tensor scalar action 或 Haar map。 |

本轮为 p-adic Haar 的 `p^dim` 系数提供 determinant-side sanity bridge；它使用
“每个 factor 乘 p”的 tensor map，实际 Haar image 使用的是 tensor scalar
乘法，因此一般情况下二者的 map identification 仍需单独证明。该差异已显式
保留，未把 common map 的 determinant 公式当成一般 determinant/Haar theorem。

`Prologue-R5 → Prologue-R5`，operation `derive`，owner Scene1；无新参考代码、
Lake 依赖或 Core/Candidate/Obligations 变更。actual scalar determinant 记账义务
减少，前置信任不增加。completion norm/local-degree、一般 Haar/determinant、
论文 representatives/权重、maximal-order/hull、不同 untilt/Bloch–Kato、真实
q-pilot/thetaVolume 和最终 Corollary 3.12 仍 open。资源见 log4 的 S1.268。

## S1.269：single-factor tensor scalar action bridge

| Source id | 本地声明与路径 | 来源、适配与边界 |
| --- | --- | --- |
| `JT-SCENE1-LOCAL-TENSOR-SCALAR-ACTION` | `scaleAt`、`scaleAt_apply`；`Act1Scene1/LocalCompletionTensorScalarAction.lean` | 在实际 `Packet.Tensor` 上只缩放一个 factor，使用 `PiTensorProduct.induction_on` 与 `tprodCoeff` 的单坐标缩放定理证明它等于整个 tensor 的 `a • x`。factor algebra/module 实例固定为实际 `padicAlgebra` 与 `finite_padicAlgebra`；不接收 detached tensor action 或 Haar certificate。 |

本单元专门固定 S1.268 与 p-adic Haar 之间的 map distinction：S1.268 的
common map 同时乘每个 factor，因而 determinant 指数带 `Fintype.card ι`；本单元
的 `scaleAt` 只在一个 factor 乘 `a`，正是 whole-tensor scalar action。一般
algebraic norm 到 completion real norm/local degree、任意 determinant/Haar、论文
representatives/权重、maximal-order/hull、q-pilot/thetaVolume 与最终 Corollary
3.12 仍 open。

`Prologue-R5 → Prologue-R5`，operation `derive`，owner Scene1；无新参考代码、
Lake 依赖或 Core/Candidate/Obligations 变更。验证资源见 `docs/开发计划.V1Act1log4.md`
的 S1.269；窄审计结果为 SceneBounds 214/45、总计 786/369。

## S1.270：canonical Scene1 input 的 q-pilot 来源与模型障碍

| Source id | 本地声明与路径 | 来源、适配与边界 |
| --- | --- | --- |
| `IUT-COR312-CANONICAL-SOURCE-FIELD-AUDIT` | `IutQPilotSource.ofCanonicalInitialThetaScene1Input`、`CanonicalInitialThetaScene1Input.finrank_eq_one_of_weightedNormalization`；`Act1Scene1/IutInitialThetaCanonicalSourceAudit.lean` | 消费 S1.241–242 的 canonical 场景输入和既有 canonical q-pilot source 构造器，直接在 `X.toData` 上构造来源，无独立 `hEll`/`hLink` certificate。随后消费实际非空处集、source 的 raw norm theorem 与逐处 normalization audit，证明当前 weighted normalization 必须满足 `Module.finrank ℚ D.F = 1`。保留 theta、Perfectoid、packet/hull、volume 和 q-family 义务为显式输入；未构造一般数域的完整满足模型。 |

Joshi III 的 `cor:cor312` 不能靠这个 degree-one 限制得到一般数域的来源模型。
本单元证明当前两种 normalization 的障碍确实出现在 canonical source 路径上，
并未据此改变论文目标、删除非空处集或增加 Prologue 假设。raw 与
paper/degree normalization 的最终选择仍需来源复审。

`Prologue-R5 → Prologue-R5`，operation `derive`，owner Scene1。新增来源构造与
必要条件 proof term；无退休、晋升、抽取、新参考代码复制、Lake 依赖或
Core/Candidate/Obligations 改动。新构造由必要条件定理实际消费。
参数来源识别负担减少，前置信任负担不增加；完整 Scene1 与 Corollary 3.12 仍 open。
验证、资源和完整动态记录见 log4 的 `S1-BND-270`。

## S1.271：raw q-sum 的全局次数会计

| Source id | 本地声明与路径 | 来源、适配与边界 |
| --- | --- | --- |
| `JT-SCENE1-QPILOT-RAW-DEGREE-ACCOUNTING` | `degreeNormalizedSourceQLogSum_eq_raw_div_degree`、`Corollary312QPilotSourceIndexBridge.rawSourceQLogSum_eq_degree_mul_absLogQ`；`Act1Scene1/QPilotRawDegreeAccounting.lean` | 用既有 local degree adapter 对同一 finite grouping 求和，得到 degree-normalized sum = raw sum / `[K : ℚ]`。随后消费实际 raw uniformizer norm certificate 和 finite source-index bridge，证明 raw sum = `[K : ℚ] * absLogQ`，不要求 weighted normalization 或 degree-one。 |
| `JT-SCENE1-INITIAL-THETA-QPILOT-RAW-ACCOUNTING` | `Corollary312Scene1DegreeNormalizedQPilotData.qLogSum_eq_degree_mul_absLogQ`、`qLogSum_div_degree_eq_absLogQ`、`qLogSum_div_degree_eq_degreeNormalizedSourceQLogSum`、`corollary312_iff_degreeScaledQPilot`；`Act1Scene1/IutInitialThetaQPilotRawAccounting.lean` | 对已有真实 InitialThetaData source 可构造的 degree-normalized bundle 应用 generic accounting，消费其 actual raw certificate、q-family 和 sourceIndexBridge，证明当前 raw target 的 `qLogSum = [K : ℚ] * absLogQ`、除以 `[K : ℚ]` 后等于 q-pilot `absLogQ`，并进一步等于 grouped degree-normalized source sum，再将精确系数带入 `Corollary312` 的等价表述。base 的 theta/packet/hull/volume 会计仍是条件输入，不声称完整真实满足模型。 |

Joshi III `th:moccor`（1748–1754）、`th:moccor-tensor-product1`（2086–2095）
明确选择 local `|π_w| = p⁻¹`；`ss:weighted-vol`、`eq:weights`（3553–3555）
涉及 relative completion degree，`cor:cor312`（3647–3650）使用未加权代表处和。
本单元的 global `[K : ℚ]` 转换不能代替 local residue-degree correction 或
paper representative normalization。它校正当前 raw candidate 的 q-pilot 表述，
不冻结 literal paper target、不取消 S1.270 的 weighted-contract 障碍。

`Prologue-R5 → Prologue-R5`，operation `derive`，owner Scene1；新增四个 proved
会计/等价声明，由 generic finite sum 到 actual bundle、再到 target equivalence
逐层消费。无退休、Prologue 晋升/抽取、新参考代码复制或 Lake 依赖。前置信任
不增加；一般真实模型、论文代表/权重、thetaVolume 与最终 Corollary 3.12 仍 open。
验证与资源见 log4 的 `S1-BND-271`。

## S1.272：代表纤维 mass-one 条件的限制

| Source id | 本地声明与路径 | 来源、适配与边界 |
| --- | --- | --- |
| `JT-SCENE1-PAPER-REPRESENTATIVE-MASS-AUDIT` | `Corollary312QPilotPaperRepresentativeAccounting.representativeOfSource_surjective`、`primeLabel_injective`、`Corollary312PaperRepresentativeSectionLinkAccounting.sectionLink_residueChar_injective`；`Act1Scene1/PaperQRepresentativeMassAudit.lean` | mass-one 条件先推出 source-to-representative 映射满射。若该映射保持有理素数标签，同素数两个不同代表的互斥纤维各有权重 1，但它们的总权重≤该素数完整 source 子纤维权重≤1，矛盾；因此素数标签单射。随后通过实际 `InitialThetaData` canonical section-link 的 representativeLinkEquiv 运输该限制。 |

来源是已证明的 Core `Arithmetic.qPilotWeight_sum_le_one_of_residueChar_filter`
和本地 Scene1 representative accounting 字段；未移植新参考代码。Joshi III
`ss:val-sets-defn`、`cor:cor312` 的处集允许逐 prime 使用其全部选定代表；本单元
不把“每 prime 至多一个代表”当作论文假设。它揭示当前去权 certificate 在保持
prime 时的限制，不声称存在实际 two-place countermodel，也不声称已证明某个
未构造的 source-to-paper map 保持 prime。

`Prologue-R5 → Prologue-R5`，operation `derive`，owner Scene1；新增三条必要性质，
满射结果由 prime-label 单射证明消费，后者由 actual section-link 单射定理消费。
无旧声明退休、Prologue 晋升/抽取、Core/Candidate/Obligations 或 Lake 依赖变更。
前置信任不增加；去权、代表/重数、paper normalization、thetaVolume 和完整
Scene1 仍 open。动态记录、验证和资源见 log4 的 `S1-BND-272`。

S1.272 验证补记：三条公共定理及 PaperAccounting 30/14 和 Scene1 聚合通过；
`9255/9255` jobs、退出码 0，公理仅有标准允许集合。数学前提不变，完整模型仍 open。

## S1.273：派生 representative fibre mass 的会计

| Source id | 本地声明与路径 | 来源、适配与边界 |
| --- | --- | --- |
| `JT-SCENE1-PAPER-REPRESENTATIVE-FIBER-MASS` | `qPilotRepresentativeFiberMass`、`qPilotWeightedSourceSum_eq_fiberMassSum`、`qPilotRepresentativeFiberMass_mem_unitInterval`、`Corollary312QPilotData.absLogQ_eq_fiberMassRepresentativeSum`、`absLogQ_le_unweightedRepresentativeSum`；`Act1Scene1/PaperQRepresentativeFiberMass.lean` | fibre mass 定义为实际 `Arithmetic.qPilotWeight` 在 source-to-representative 映射纤维上的有限和，不作为自由字段给出。Finite sum partition 得到 weighted regrouping；原 raw norm law 的 paper-normalized q-log theorem 连接到实际 q-pilot。prime-preserving map 下，每 fibre mass 在 `[0,1]`；代表项非负时 weighted sum≤unweighted sum。source map、局部 term identity 和非负性保持显式条件，未构造 paper carrier 或去权等式。 |

消费链为 computed mass → finite weighted regrouping → actual q-pilot equality；
prime-fibre bound → mass interval → q-pilot/unweighted inequality。
旧 `Corollary312QPilotPaperRepresentativeAccounting` 及 S1.272 necessary restrictions
保留，未改已有声明、未把计算得出的 mass 强制设为 1。Joshi III
`ss:weighted-vol` / `le:volume-lemma3` 的权重方向与此有限非负和比较一致；识别
这些 mass 与论文 relative completion weights、paper representatives/local terms
仍是来源义务，不从这个 inequality 宣布 Corollary 3.12 已冻结或证明。

`Prologue-R5 → Prologue-R5`，operation `derive`，owner Scene1；新增定义和四条
会计/范围/不等式 theorem，无退休、Prologue 晋升/抽取、新参考代码复制或 Lake
依赖变更。前置信任不增加；完整真实模型、论文归一化/代表身份、thetaVolume 和
Corollary 3.12 仍 open。动态记录、最终编译与资源见 log4 的 `S1-BND-273`。

S1.273 验证补记：最终精确导入版本 `9256/9256` jobs 通过，退出码 0；
PaperAccounting 35/18 和 Scene1 聚合通过，公理仅有标准允许集合。完整模型仍 open。

## S1.274：实际 section 代表项的严格正性

| Source id | 本地声明与路径 | 来源、适配与边界 |
| --- | --- | --- |
| `JT-SCENE1-INITIAL-THETA-REPRESENTATIVE-TERM` | `iutInitialThetaSectionRepresentativeTerm`、`iutInitialThetaSectionRepresentativeTerm_pos`、`iutInitialThetaSectionRepresentativeSum_pos`、`Corollary312QPilotData.absLogQ_le_initialThetaSectionRepresentativeSum`；`Act1Scene1/IutInitialThetaRepresentativeTerm.lean` | 代表项为实际 canonical section Tate `qOrder/(2*D.prime.ℓ) * log(residueChar)`。实际 Tate laws 给出 qOrder>0，actual prime≥5、residue prime>1，因而每个实际代表项>0；处集非空来自 actual InitialThetaData 的 bad-support section，有限和>0。实际项正性随后消费到 S1.273 上界，消除独立 representative nonnegativity 参数。source map、逐处 prime identity、paper-local-term identity 和 raw norm/source compatibility 继续显式；不接收 mass-one certificate。 |

两个精确 imports 是 actual `IutInitialThetaSectionLink` 和已证明的 fibre-mass
模块。新定理不导入 Prologue Obligations，不新增 IUT 代码复制或 Lake 依赖。
canonical section carrier 来源等式已由既有 section-link/Voss 定理提供，实际项
与 selected-q-root paper sum 的进一步无证书装配是后续消费者义务；本单元没有
提供 detached representative carrier 或宣称 source map 已构造。

`Prologue-R5 → Prologue-R5`，operation `derive`，owner Scene1。新增定义与三条
定理；严格正性被实际有限和及 q-pilot inequality 消费；退休、Prologue 晋升/
抽取均为无，Core/Candidate/Obligations 不变。代表非负性证明负担减少，前置
信任不增加。完整真实来源模型、paper mapping/normalization、thetaVolume 和
Corollary 3.12 仍 open。验证及资源见 log4 的 `S1-BND-274`。

S1.274 验证补记：首次窄热构建 `9257/9257` jobs 通过，退出码 0；
PaperAccounting 39/21 与 Scene1 聚合通过，公理仅有标准允许集合。完整模型仍 open。

## S1.275：actual representative sum 与 selected q-root sum

| Source id | 本地声明与路径 | 来源、适配与边界 |
| --- | --- | --- |
| `JT-SCENE1-INITIAL-THETA-REPRESENTATIVE-QROOT-SUM` | `iutInitialThetaSelectedQRootPaperSum`、`iutInitialThetaSelectedQRootPaperSum_eq_representativeSum`、`iutInitialThetaSelectedQRootPaperSum_pos`、`Corollary312QPilotData.absLogQ_le_initialThetaSelectedQRootPaperSum`；`Act1Scene1/IutInitialThetaRepresentativeQRootSum.lean` | 直接由 actual selected q-root power = canonical section Tate parameter，消费 completion valuation/ordp，证明 absolute ramIdx * ordp(qroot) = actual section qOrder/(2*ℓ)。同一 section 的有限 subtype 通过保留底层处的 Equiv 逐项运输，证明 selected root paper sum 与 S1.274 actual representative sum 相等；得到严格正性，并接入既有条件性 q-pilot upper bound。和式识别不需要 independent analytic payload 或 sum-equality certificate。 |

相对 ramification、residue degree 或 global degree 没有被错误替换为此处的
absolute `ramIdx`。定义保留 selected source 和其实际 q-root，由 actual power law
推导 local equality；来源 mapping/local term/prime identity 仍是最终 q-pilot
consumer 的显式输入，不声称把它们构造出来。旧 selected section-link 的
finite-sum 定理保持不变；本单元补齐无无关 theta/packet/hull 参数的直接接口。

`Prologue-R5 → Prologue-R5`，operation `derive`，owner Scene1；新定义及三条
公共定理，private local equality 和 finite carrier equivalence 由 sum theorem
消费，sum equality 由正性与 q-pilot upper bound 消费。无退休、Prologue 晋升/
抽取、新参考代码复制、Core/Candidate/Obligations 或冻结依赖变更。直接识别
证明负担减少，前置信任不增加；真实模型、paper mapping/normalization、
thetaVolume 和最终 Corollary 3.12 仍 open。动态记录及资源见 log4 的 S1-BND-275。

S1.275 验证补记：最终窄热构建 `9258/9258` jobs 通过，退出码 0；
PaperAccounting 43/24 和 Scene1 聚合通过，公理仅有标准允许集合。完整模型仍 open。

## S1.276：实际 selected source/base 的加权比较

| Source id | 本地声明与路径 | 来源、适配与边界 |
| --- | --- | --- |
| `JT-SCENE1-INITIAL-THETA-SELECTED-WEIGHTED-BOUND` | `iutInitialThetaSelectedWeightedQRootLogSum`、`iutInitialThetaSelectedWeightedQRootLogSum_le_paperSum`、`iutInitialThetaSelectedWeightedQRootLogSum_eq_baseQOrderSum`、`iutInitialThetaSelectedBaseQOrderLogSum_le_paperSum`；`Act1Scene1/IutInitialThetaSelectedWeightedBound.lean` | 实际 selected source 上以 contracted base qPilotWeight、base ramIdx 和 actual q-root ordp 定义加权和。单处权重≤1 来自实际 prime-fibre 上界；tower identity 证明 base ramIdx≤source ramIdx；actual q-root ordp 非负来自 base qOrder 公式，得到加权和≤selected paper sum。实际 contraction equivalence 及逐处 q-root 公式再将加权和识别为 selected base qOrder 的 weighted log sum，最后消费为直接 upper bound。三个定理只接收 actual D，无自由 source-to-paper 映射或 local-term certificate。 |

结果限于 actual selected base 子集。完整 q-pilot support 的逆向 section coverage
仍须证明，不能将子集 upper bound 声称为 full source absLogQ 上界或论文等式。
本单元保留 base/source absolute ramIdx 的差别，未将两者误认为相同，也未修改
S1.275 依赖显式 mapping 的一般 q-pilot consumer。

`Prologue-R5 → Prologue-R5`，operation derive，owner Scene1；新增定义及三条
公共 theorem。actual source producer→base finite-sum equality→base upper bound
形成消费链；无退休、Prologue 晋升/抽取、新 IUT 文件复制、Core/Candidate/
Obligations 或冻结依赖变更。selected carrier 上的自由 mapping/term 输入负担
减少，前置信任不增加；full carrier、paper normalization、thetaVolume 和最终
Corollary 3.12 仍 open。验证与资源见 log4 的 S1-BND-276。

S1.276 验证补记：最终窄构建 `9259/9259` jobs 通过、退出码0；
PaperAccounting 47/27 和Scene1聚合通过，公理仅有标准允许集合。完整目标仍open。

## S1.277：完整 base q-pilot 和的遗漏部分与覆盖判据

| Source id | 本地声明与路径 | 来源、适配与边界 |
| --- | --- | --- |
| `JT-SCENE1-INITIAL-THETA-SELECTED-SUPPORT-DEFECT` | `iutInitialThetaBaseQPilotLogTerm`、`iutInitialThetaBaseQPilotLogTerm_pos`、`iutInitialThetaFullBaseQPilotLogSum`、`iutInitialThetaOmittedBaseQPilotLogSum`、`iutInitialThetaFullBaseQPilotLogSum_eq_selected_add_omitted`、`iutInitialThetaOmittedBaseQPilotLogSum_eq_zero_iff_coverage`、`iutInitialThetaFullBaseQPilotLogSum_le_paperSum_of_coverage`；`Act1Scene1/IutInitialThetaSelectedSupportDefect.lean` | 在 actual full odd-support base carrier 上定义真实 q-pilot log term，并从 qOrder>0、arithmetic weight>0、ℓ≥5 和 residue prime>1 证明严格正性。用已证明 selected subset 将完整有限和分解为 selected weighted q-root sum 加实际未选定 base 项。严格正性证明 omitted sum=0 iff selected base support=full odd support；显式 coverage 下消费 S1.276 的上界得到 full base sum≤selected paper sum。 |

分解只接受 actual D，未加入自由差额、覆盖 certificate 或 synthetic witness。
最后的 full upper bound明确保留 coverage 参数；未将 full odd support 与
D.VBad q-pilot carrier 自动等同，也不由 finite sum decomposition 推出论文
normalization 或 thetaVolume。处集若有遗漏，各项正性阻止将遗漏贡献视为零。

`Prologue-R5 → Prologue-R5`，operation derive，owner Scene1。新增三定义与四
定理，source positivity→coverage iff，selected/base identity→decomposition→
conditional full upper bound形成消费者链。无退休、Prologue晋升/抽取、IUT文件
复制、Core/Candidate/Obligations或冻结依赖改动。完整 finite accounting 的差额
明确，前置信任不增加；actual coverage、VBad/full identity、paper代表/归一化、
thetaVolume和最终Corollary3.12仍open。动态记录/资源见log4的S1-BND-277。

S1.277 验证补记：最终窄构建9260/9260 jobs通过，退出码0；
PaperAccounting54/31及Scene1聚合通过，公理仅有标准允许集合。完整目标仍open。

## S1.278：actual q-pilot 的 j-log 和完整纤维归一化

| Source id | 本地声明与路径 | 来源、适配与边界 |
| --- | --- | --- |
| `JT-SCENE1-INITIAL-THETA-QPILOT-JLOG` | `iutNormalizedLog_norm_embedding_sum_liesOver`、`iutInitialThetaBaseQPilotLogTerm_eq_jLog`、`iutInitialThetaFullBaseQPilotLogSum_eq_jLogSum`、`iutInitialThetaModuliJ_normalized_fiber`；`Act1Scene1/IutInitialThetaQPilotJLog.lean` | 从 actual base Tate j-identity 与 `TateParameter.norm_tateJ`、raw norm/qOrder law 证明每个 base term 等于 `log ‖embedding j‖/(2*ℓ*[F:ℚ])`，完整 full-support sum 因而等于同一完整 carrier 的 normalized j-log sum。generic full-fibre norm-degree theorem 与 finrank tower 证明完整上方纤维的 log-norm sum 除以全局次数后不随扩域改变，actual moduli j specialization直接消费它。 |

ValuationSection 只选择每个 moduli place 上方一个 torsion place，未提供所有base
处的覆盖。InitialThetaData 也不要求 torsion field/moduli Galois，本单元没有新增
此条件或用base Galois字段猜测coverage。新路径保留完整纤维（relative ramification
与residue-degree计数），将actual full q-pilot写为同源j-log，为后续按moduli处
重组提供数学接口；有限纤维枚举/完整性hs仍显式，完整支撑跨moduli的全局重组和
paper normalization尚未闭合。

Prologue-R5→Prologue-R5，derive，owner Scene1。新增四条theorem，local Tate
producer→full sum consumer，generic fiber theorem→actual moduli j consumer；无
退休/Prologue晋升或抽取、IUT复制、Core/Candidate/Obligations或冻结依赖改动。
对chosen Tate parameter的数值依赖通过actual j身份消除，前置信任不增加。
资源/验证和剩余义务见log4的S1-BND-278。

S1.278 验证补记：最终窄构建9261/9261 jobs通过、退出码0；
PaperAccounting58/35及Scene1聚合通过，公理仅有标准允许集合。完整目标仍open。

## S1.279：actual full q-pilot 按模域处的 j-log 重组

| Source id | 本地声明与路径 | 来源、适配与边界 |
| --- | --- | --- |
| `JT-SCENE1-INITIAL-THETA-MODULI-J-ACCOUNTING` | `iutInitialThetaOddModSupportFinset`、`iutInitialThetaBaseModuliFiber`、`mem_iutInitialThetaBaseModuliFiber_iff`、`iutInitialThetaBaseModuliFiber_normalized_jLog`、`iutInitialThetaFullBaseQPilotLogSum_eq_moduliJLogSum`；`Act1Scene1/IutInitialThetaModuliJAccounting.lean` | 由 actual odd moduli support 的有限性及其完整 base pullback 构造模域有限支撑与完整 base 纤维，证明每个支撑处的纤维成员当且仅当 LiesOver。消费 S1.278 的 normalized fibre j-log 定理，再由 canonical contraction 分组 actual full base finite sum，得到 full q-pilot 等于 actual moduli j-log sum 除以 `2*ℓ*[fieldOfModuli:ℚ]`。 |

三个公共定理只消费 actual D 与所属模域支撑的处。纤维完整性由实际 pullback
和 canonical contraction 唯一性证明，调用方无需另交完整枚举 hs，也无需证明
section 覆盖 full base support。最终和式保留所有实际 base 处；relative local
程度通过完整纤维的 global-degree normalization 消去。

Prologue-R5→Prologue-R5，derive，owner Scene1。新增两定义、三定理，实际
carrier producer→完整纤维判据→归一化→全局重组形成消费链。前置信任不增加；
Core/Candidate/Obligations、冻结依赖均不变。full/VBad 身份、模域 j-log 与
论文 selected representative 的权重/归一化比较、真实完整模型及 thetaVolume/
Corollary3.12 仍 open。动态记录及构建资源见 log4 的 S1-BND-279。

S1.279 验证补记：首次窄热构建9262/9262 jobs通过，退出码0；
PaperAccounting63/38及Scene1聚合通过，38条公理报告仅含标准允许集合。完整目标仍open。

## S1.280：完整 odd-support q-pilot 与实际 selected paper sum 的上界

| Source id | 本地声明与路径 | 来源、适配与边界 |
| --- | --- | --- |
| `JT-SCENE1-INITIAL-THETA-FULL-REPRESENTATIVE-BOUND` | `iutInitialThetaModuliSelectedSourceEquiv`、`iutInitialThetaModuliJLogTerm_eq_weightedBaseQOrder`、`iutInitialThetaModuliJLogTerm_le_selectedPaperTerm`、`iutInitialThetaFullBaseQPilotLogSum_le_selectedPaperSum`、`iutInitialThetaFullBaseQPilotLogSum_le_representativeSum`；`Act1Scene1/IutInitialThetaFullRepresentativeBound.lean` | 消费 actual full moduli j-log accounting，以 base/moduli completion norm 的相对 e*f 幂律和 inertia tower 消去相对 residue degree，证明每个 normalized moduli j-log term 等于 `(qPilotWeight v / relRamIdx b v) * (baseQOrder b/(2*ℓ))*log(residueChar b)`。系数≤1，base/source ramification tower 与 actual selected q-root ordp identity 给出逐代表上界。模域有限支撑与实际 selected source 的双射运输 finite sum，得到 actual full base q-pilot≤actual selected paper sum，进而≤同一 section representative sum。 |

这条 full 上界不需要 section 覆盖 full base support：所有 base 处已在完整 moduli
纤维中求和，然后对每个 moduli 处比较一个实际选定代表。它不把 full carrier
等同于 selected carrier，亦不把上界当成论文要求的未加权等式。参照 Joshi III
`ss:val-sets-defn`、`th:moccor-Mochizuki-form2`、`cor:cor312`（index 第133–134条），
本文仍需证明论文处集/代表来源身份、paper norm 和 thetaVolume 的定量传递。

Prologue-R5→Prologue-R5，derive，owner Scene1；新增一个实际 carrier equivalence
及四条 theorem；local numeric producer→逐项 bound→full finite sum→representative
consumer。前置信任不增加，Core/Candidate/Obligations、冻结依赖不变。资源、验证
与未完成模型义务见 log4 的 S1-BND-280。旧显式 coverage 下的上界声明保留。

S1.280 验证补记：最终窄热构建9263/9263 jobs通过，退出码0；
PaperAccounting68/42与Scene1聚合通过，42条公理报告只含标准允许集合。完整目标仍open。

## S1.281：actual VBad 与 canonical Scene1 q-pilot 的代表上界

| Source id | 本地声明与路径 | 来源、适配与边界 |
| --- | --- | --- |
| `JT-SCENE1-INITIAL-THETA-VBAD-REPRESENTATIVE-BOUND` | `iutInitialThetaReferenceAbsLogQ_eq_fullCarrierRestriction`、`iutInitialThetaReferenceAbsLogQ_le_fullBaseSum`、`iutInitialThetaReferenceAbsLogQ_le_selectedPaperSum`、`Corollary312QPilotData.absLogQ_le_selectedPaperSum_ofCanonicalInitialThetaLink`；`Act1Scene1/IutInitialThetaVBadRepresentativeBound.lean` | 由 actual VBad base support 包含于完整 odd-support 构造保留底层处的 finite carrier inclusion；已有 Tate parameter uniqueness/qOrder equality 识别共同处的实际 admissible-prime 项。ReferenceIut.absLogQ 精确等于完整 carrier 上按 actual VBad pullback 过滤的项和，正性给出≤full sum。消费 S1.280 full bound 得到 actual VBad absLogQ≤selected paper sum，再通过 canonical source/reference equality 接入实际 canonical Scene1 q-pilot。 |

本模块使用已有实际数据，不移植新文件。VBad/full 的数值关系是限制和式身份，
未把包含关系改称 carrier equality。canonical consumer 保留既有 hEll/hLink 和
解析载体参数，但不需要新 source-to-representative 映射、prime/term certificate、
section coverage 或 degree-one 条件；新上界针对 degree-normalized absLogQ，
不是 raw target qLogSum 与论文和式的等式或 thetaVolume 估计。

Prologue-R5→Prologue-R5，derive，owner Scene1。新增四条 theorem，actual carrier
restriction identity→full bound→selected bound→canonical consumer。共同处项的
身份来自已经证明的 actual qOrder equality，前置信任不增加；Core/Candidate/
Obligations、既有声明和冻结依赖不变。完整来源模型、论文载体身份/归一化和
volume transfer 仍 open。验证、资源与动态记录见 log4 的 S1-BND-281。

S1.281 验证补记：最终窄热构建9264/9264 jobs通过，退出码0；
PaperAccounting72/46及Scene1聚合通过，46条公理报告只含标准允许集合。完整目标仍open。

## S1.282：实际完整 q-pilot 的代表系数与去权等式判据

| Source id | 本地声明与路径 | 来源、适配与边界 |
| --- | --- | --- |
| `JT-SCENE1-INITIAL-THETA-REPRESENTATIVE-COEFFICIENTS` | `iutInitialThetaRepresentativeCoefficient`、`iutInitialThetaModuliJLogTerm_eq_coefficient_mul_selectedPaperTerm`、`iutInitialThetaRepresentativeCoefficient_mem_Ioc`、`iutInitialThetaFullBaseQPilotLogSum_eq_coefficientWeightedPaperSum`、`iutInitialThetaFullBaseQPilotLogSum_eq_paperSum_iff_coefficients_eq_one`；`Act1Scene1/IutInitialThetaRepresentativeCoefficients.lean` | 对实际 moduli support 的每个 v，令 s 为 actual section q-root source、b=contraction(s)，计算 `c(v)=qPilotWeight(v)/(relRamIdx(b/v)*relRamIdx(s/b))`。由实际 selected q-root ordp、ramification tower 和 S1.280 normalized moduli j-log formula 证明 local full contribution=c(v)*paperTerm(s)。已有实际 local bound与严格正性给出 0<c≤1，full moduli grouping 给出完整 q-pilot 的 exact coefficient-weighted representative sum。全部 paper 项严格正，有限差额和因此给出 full sum=unweighted selected paper sum iff 每个 c(v)=1。 |

系数不是自由输入。完整 base 纤维已求和，相对 residue degree 在该求和/归一化
中消去；两层相对 ramification 则仍出现在代表系数的分母。S1.280/281 的上界
不能代替去权等式。此必要充分判据未提供 actual coefficient=1 证明，也未构造
系数严格小于1的特定 InitialThetaData 反例。Joshi III 的 `ss:theta-data-fixing2`、
`ss:val-sets-defn` 和 `cor:cor312` 的论文 carrier/norm 身份仍须独立证明。

Prologue-R5→Prologue-R5，derive，owner Scene1。新增实际 coefficient 定义及四条
theorem；local identity→interval bound/full weighted sum→unweighted equality iff
形成消费链。前置信任不增加，Core/Candidate/Obligations、既有目标声明和冻结
依赖不变。资源、完整公共类型、模型义务及验证见 log4 的 S1-BND-282。

S1.282 验证补记：最终窄热构建9265/9265 jobs通过，退出码0；
PaperAccounting77/50及Scene1聚合通过，50条公理报告只含标准允许集合。完整目标仍open。

## S1.283：actual VBad ramification 与代表和式的严格差额

| Source id | 本地声明与路径 | 来源、适配与边界 |
| --- | --- | --- |
| `JT-SCENE1-INITIAL-THETA-REPRESENTATIVE-RAMIFICATION-GAP` | `iutInitialThetaEll_dvd_qRootRelativeRamIdx_on_vbad`、`iutInitialThetaRepresentativeCoefficient_lt_one_on_vbad`、`iutInitialThetaFullBaseQPilotLogSum_lt_selectedPaperSum`、`iutInitialThetaReferenceAbsLogQ_lt_selectedPaperSum`；`Act1Scene1/IutInitialThetaRepresentativeRamificationGap.lean` | 对 actual full torsion q-root source 中 contracted base place 属于 VBad pullback 的 s，由实际 qroot^(2ℓ)=completionMap(base Tate q) 对整数 valuation 取 log，得到 ℓ∣relRamIdx(s/b)*baseQOrder(b)。实际 VBad 的 qOrder 与 ℓ 互素，故 ℓ∣relRamIdx(s/b)。ℓ≥5、其余相对 ramification≥1、moduli qPilotWeight≤1，推出实际 VBad moduli 代表系数<1。非空 VBad 和 S1.282 去权 iff 判据排除 full normalized q-pilot=unweighted selected paper sum，已有 upper bound给出严格小于；实际 reference absLogQ≤full，因此也严格小于 selected paper sum。 |

推导消费实际 D 的 root equation、completion map、qOrder coprimality与非空性；
不需要额外 root-class、ramification、uniformizer 或 paper mapping certificate。
这与现有 IutRootClassRamification 的来源方法一致，本模块直接用已构造 q-root。
没有复制新参考文件或构造特定 InitialThetaData，不能据 universally quantified
conditional theorem 声称 actual D 的存在性已完成。

Prologue-R5→Prologue-R5，derive，owner Scene1。新增四条 theorem，integer valuation
producer→actual ramification divisor→strict coefficient→full strict separation→
actual reference consumer。当前 normalization 下的去权等式被实际字段排除；
应对 target 与对应 volume 的论文归一化作来源复审，不能补一个 coefficient=1
假设。Core/Candidate/Obligations、既有声明与冻结依赖不变。完整动态记录、模型
义务、验证和资源见 log4 的 S1-BND-283。

S1.283 验证补记：最终窄热构建9266/9266 jobs通过，退出码0；
PaperAccounting81/54及Scene1聚合通过，54条公理报告只含标准允许集合。完整目标仍open。

## S1.284：实际 selected q-root 球的 paper-normalized 体积乘积

| Source id | 本地声明与路径 | 来源、适配与边界 |
| --- | --- | --- |
| `JT-SCENE1-INITIAL-THETA-SELECTED-PAPER-BALL-PRODUCT` | `iutInitialThetaFullQRoot_norm_lt_one`、`iutInitialThetaQRootIntegralBall`、`iutInitialThetaQRootIntegralBall_haar_toReal_eq_norm`、`iutInitialThetaPaperBallVolume`、`iutInitialThetaPaperBallVolume_mem_Ioo`、`iutInitialThetaPaperBallVolume_negLog_eq_paperTerm`、`iutInitialThetaSelectedPaperBallProduct`、`iutInitialThetaSelectedPaperBallProduct_negLog_eq_paperSum`、`iutInitialThetaSelectedPaperBallProduct_mem_Ioo`；`Act1Scene1/IutInitialThetaSelectedPaperBallProduct.lean` | actual full torsion q-root 的 power equation 与 canonical completion map 给出 norm<1。将 actual root 打包到 completion integer ring，消费已有 normalized scalar-ball Haar/index/norm theorem，证明 root*O球的 Haar.toReal=raw root norm。取体积数值的 `1/inertDeg` 次幂，实现 Joshi III 1748、2086 的局部 uniformizer 归一化；Arithmetic.ordp 与 e*f accounting 证明负对数=实际 paper root 项。实际 selected carrier 的有限乘积负对数精确等于 selected paper sum，且乘积在(0,1)。 |

所有局部球由 actual D 的实际 root 构造。normalized Haar 原始体积通过真实
integer quotient/index 计算；paper correction 是该体积数值的幂，不声称幂修正
仍为 additive Haar measure。有限乘积使用原有 actual selected source，不改用
full base carrier 或自由 paper mapping。该乘积可以服务于论文 product 下界的
q侧，但它本身还不是 tensor/hull 或 thetaVolume；log-shell witness、untilt、
packet/collation/hull 的来源和 volume transfer 必须继续证明。

Prologue-R5→Prologue-R5，derive，owner Scene1。新增三定义及六公共 theorem，
actual root norm→实际 Haar volume→paper local log→selected finite product/log
形成消费链。Core/Candidate/Obligations、既有target签名和冻结依赖不变，前置
信任不增加。边界/模型义务、完整类型、验证与资源见log4的S1-BND-284。

S1.284 验证补记：最终窄热构建9267/9267 jobs通过，退出码0；
PaperAccounting90/60及Scene1聚合通过，60条公理报告只含标准允许集合。完整目标仍open。

## S1.285：完整 q-root 的实际 log-shell 球与 selected 体积乘积

| Source id | 本地声明与路径 | 来源、适配与边界 |
| --- | --- | --- |
| `JT-SCENE1-INITIAL-THETA-SELECTED-LOG-BALL-PRODUCT` | `iutInitialThetaFullQRootLogValue`、`iutInitialThetaFullQRootLogValue_norm_eq`、`iutInitialThetaFullQRootLogValue_mem_logShell`、`iutInitialThetaFullQRootLogBall`、`iutInitialThetaFullQRootLogBall_eq_rootBall`、`iutInitialThetaFullQRootLogBall_subset_logShell`、`iutInitialThetaFullQRootLogBall_haar_toReal_eq_norm`、`iutInitialThetaSelectedPaperLogBallProduct`、`iutInitialThetaSelectedPaperLogBallProduct_eq_rootBallProduct`、`iutInitialThetaSelectedPaperLogBallProduct_negLog_eq_paperSum`；`Act1Scene1/IutInitialThetaSelectedLogBallProduct.lean` | 对 actual full odd-support torsion q-root 构造普通 normalized p-adic logarithm，使用 actual residue characteristic prime、norm(p)<1 和 S1.284 actual root norm<1，证明其范数等于实际root范数并属于logShell。两个非零scalar的积分球由共同范数识别，故实际logValue*O球=actual root*O球。局部log-shell surjectivity给出整个球的包含，真实Haar volume和paper-corrected selected product通过球集等式运输；乘积的负log精确等于selected paper sum。 |

本轮把前期只对实际VBad source证明的普通log witness路径接到actual full
odd-support source；没有改写已有载体。球身份是实际set等式，不接收独立norm、
set或volume certificate。paper correction仍为数值residue-degree幂，原始Haar
measure保持不变。ordinary logShell不等于尚未构造的Bloch–Kato cohomology/log
shell，selected scalar product也不等于最终theta tensor/hull；此处不替代那些
来源义务。Joshi III `le:elem-lemma`、`eq:multiplicative-coh-class` 和
`th:moccor-Mochizuki-form1/2` 提供后续目标角色。

Prologue-R5→Prologue-R5，derive，owner Scene1。新增三定义及七公共theorem；
actual full root→ordinary log norm/source→whole ball identity/containment→Haar
consumer→selected corrected product/log consumer。Core/Candidate/Obligations、
既有声明和冻结依赖不变，前置信任不增加。模型/边界、完整公共类型、验证和
资源见log4的S1-BND-285。

S1.285 验证补记：首次窄热构建9268/9268 jobs通过，退出码0；
PaperAccounting100/67及Scene1聚合通过，67条公理报告只含标准允许集合。完整目标仍open。

## S1.286：全部实际 selected prime-fibre 的 canonical tensor log-region

| Source id | 本地声明与路径 | 来源、适配与边界 |
| --- | --- | --- |
| `JT-SCENE1-INITIAL-THETA-SELECTED-TENSOR-LOG-REGION` | `SelectedThetaTensor.fiber`、`enumeration`、`sourceAt`、`sourceAt_selected_residueChar`、`packet`、`value`、`region`、`value_ne_zero`、`value_mem_region`、`region_eq_rootBallLattice`、`region_le_tensorLogShell`、`region_isOpen`、`region_isCompact`、`regionIndex`、`regionIndex_pos`、`region_normalizedHaar_eq_inv_index`、`region_normalizedHaar_pos_le_one`；`Act1Scene1/IutInitialThetaSelectedTensorLogRegion.lean` | actual selected source 按 residueChar=p 的 finite filter 给出完整 prime fibre，Fintype.equivFin 的逆是 bijective enumeration。packet factors直接取该枚举的 actual torsion completions，value 是 S1.285 full-source ordinary logarithm scalars 的 pure tensor，region是实际log-ball纯tensor的积分span。factor balls等于实际root balls，pure witness非零且属于region，region包含于tensor ordinary logShell。已有actual tensor lattice topology/index/Haar theorem给出compact openness、positive finite integral index和normalized tensor Haar=index⁻¹、0<measure≤1。 |

该构造只接实际D和有理prime p，不再给任意tuple c或prime-alignment certificate。
Fin(card fibre)枚举用于满足现有Packet的small index universe，同时完整bijection
保留所有selected处；它不是删除处的截断。空fibre按已有空tensor约定存在，
此处未把空packet计作非空论文prime strip。指数来自实际tensor积分lattice；
未将factor paper-volume乘积误作raw tensor Haar。tensor Haar/index与论文weighted
volume、重排独立性、不同untilt/Bloch–Kato类和theta hull的身份仍须继续证明。

Prologue-R5→Prologue-R5，derive，owner Scene1；新增七定义、十公共theorem，actual
prime filter→complete enumeration→canonical packet/log region→topology/index/Haar
消费链。Core/Candidate/Obligations、旧公共API与冻结依赖不变，前置信任不增加。
完整类型、模型义务和资源/验证见log4的S1-BND-286。

S1.286 验证补记：首次窄热构建9269/9269 jobs通过，退出码0；
SceneBounds231/55与Scene1聚合通过，55条公理报告仅含标准允许集合。完整目标仍open。

## S1.287：p-adic transvection 的 Haar 不变性与 selected tensor 消费者

| Source id | 本地声明与路径 | 来源、适配与边界 |
| --- | --- | --- |
| `JT-SCENE1-PADIC-HAAR-TRANSVECTION` | `PadicHaar.productHaar_measurePreserving_transvection`、`haar_measurePreserving_transvection`、`basisTransvection`、`haar_measurePreserving_basisTransvection`；`Act1Scene1/PadicHaarTransvection.lean` | 参考冻结版 Mathlib `MeasureTheory/Measure/Lebesgue/Basic.lean` 中 Real.volume_preserving_transvectionStruct 的 Fubini/单坐标平移证明，将局部 measure 改为 ℚ_p 的 actual additive Haar，再由 Haar uniqueness 到任意 coordinate Haar measure，最后经有限维 basis transport 得到实际有限维空间 elementary shear measure preservation。文件头保留来源commit、作者、Apache-2.0通知；不改Mathlib或新增依赖。 |
| `JT-SCENE1-INITIAL-THETA-SELECTED-TENSOR-SHEAR` | `SelectedThetaTensor.shear`、`shear_measurePreserving`、`region_haar_shear_image`、`region_haar_shear_image_eq_inv_index`；`Act1Scene1/IutInitialThetaSelectedTensorShear.lean` | 在actual selected packet tensorBasis上构造实际continuous basis transvection，消费通用p-adic Haar theorem，证明actual compact-open log-region的shear image与原region有相同normalized Haar measure，并与真实regionIndex⁻¹连接。 |

冻结 Mathlib 的现有 complete determinant/Haar formula 仅针对实数。这里闭合其
p-adic 推导中 transvection 生成元步骤，未假定对角matrix scaling或一般determinant
formula。actual selected consumer证明的是Haar测度不变性，不是theta hull set
不变或paper weighted volume。对角标量与norm、matrix product到完整det/Haar、
factor algebraic norm/actual completion norm及论文归一化仍待实际证明。

Prologue-R5→Prologue-R5，derive，owner Scene1。两个实际continuous equivalence定义
与六条公共theorem；Fubini/translation producer→coordinate arbitrary Haar→basis
transport→actual selected region consumer。Core/Candidate/Obligations和冻结依赖
不变，前置信任不增加。完整类型、模型/来源审查和资源见log4的S1-BND-287。

S1.287 验证补记：最终窄热构建9271/9271 jobs通过，退出码0；
SceneBounds239/61及Scene1聚合通过，61条公理报告只含标准允许集合。完整目标仍open。

## S1.288：一般 p-adic determinant/Haar 与 actual selected tensor 体积

| Source id | 本地声明与路径 | 来源、适配与边界 |
| --- | --- | --- |
| `JT-SCENE1-PADIC-HAAR-SCALAR-NORM` | `PadicHaar.distribHaarChar_eq_norm`、`measure_image_mul_eq_norm`、`measure_preimage_mul_eq_inv_norm`；`Act1Scene1/PadicHaarScalarNorm.lean` | p-adic valuation 分解任意非零 scalar 为 norm-one unit 与 p 的整数幂。norm-one scalar 的积分球 image等于原球，故Haar character=1；已有prime Haar scaling给出p的character。character hom与actual p-adic norm law给出任意scalar modulus=norm及任意set的image/preimage Haar公式。 |
| `JT-SCENE1-PADIC-HAAR-DETERMINANT` | `map_matrix_productHaar_eq_norm_det_inv`、`map_matrix_haar_eq_norm_det_inv`、`map_linearEquiv_haar_eq_norm_det_inv`、`measure_image_linearEquiv_eq_norm_det`；`Act1Scene1/PadicHaarDeterminant.lean` | 实际scalar law给出diagonal矩阵对product Haar的缩放，S1.287 transvection measure preservation与Matrix.diagonal_transvection_induction_of_det_ne_zero给出任意invertible matrix map Haar=norm(det⁻¹)·Haar。Haar uniqueness与basis conjugation运输到任意有限维ℚ_p空间的actual additive Haar，inverse map给出image scaling norm(det)。保留冻结Mathlib实数证明结构的作者/Apache-2.0来源通知，不改Mathlib。 |
| `JT-SCENE1-INITIAL-THETA-SELECTED-TENSOR-DET-HAAR` | `SelectedThetaTensor.logScale`、`logScaleDet`、`logFactorNorm`、`region_eq_logScale_image`、`region_normalizedHaar_eq_det_norm`、`region_normalizedHaar_eq_factorNorm_product`、`regionIndex_inv_eq_det_norm`；`Act1Scene1/IutInitialThetaSelectedTensorDetHaar.lean` | actual selected log-scalars确定真实tensor scaling map/matrix，region是unit integral lattice的image。general p-adic Haar law给出normalized region measure=norm(actual scaling determinant)；已有factor determinant theorem给出factor algebraic norm的模乘积，各项指数是其他factor维数乘积。真实regionIndex⁻¹也被识别为该det norm。 |

完整 p-adic det/Haar law消费actual scalar/Fubini/矩阵生成元，不需要free modulus
certificate。actual tensor使用原selected prime-fibre和actual log-scalars；finite
instance由实际tensorBasis派生。factor algebraic norm的p-adic模如何等于actual
completion norm、对应local degree与论文weighted-volume仍需证明。这里不把
raw tensor Haar改称paper product、Bloch–Kato类或theta hull。

Prologue-R5→Prologue-R5，derive，owner Scene1；四个actual scale/norm定义及十三
公共theorem，scalar producer→matrix/finite-dimensional det/Haar→actual tensor
region/index/factor-norm consumer。Core/Candidate/Obligations、旧target/API和
冻结依赖不变，前置信任不增加。完整类型、模型义务、验证和资源见log4的
S1-BND-288。

S1.288 tensor分层补记：`JT-SCENE1-LOCAL-COMPLETION-TENSOR-DET-HAAR` 登记
`LocalCompletion.Packet.normalizedHaar_scalarLattice_eq_det_norm` 与
`normalizedHaar_scalarLattice_eq_factorNorm_product`；生产路径
`Act1Scene1/LocalCompletionTensorDetHaar.lean`。抽象actual Packet P上的tensor
Haar→det norm→factor algebraic norms提供稳定proof接口，actual selected consumer
直接实例化。generic theorem显式接actual factor scalars及nonzero proof，不接
free measure/scaling证书。最终四窄叶子、四定义、十三公共theorem，SceneBounds
256/74、全工程907/460；Core仍R5，前置信任不增加。

S1.288 determinant边界补记：`LocalCompletion.Packet.scaleDet P z hz` 按抽象Packet
的固定有限索引/decidable实例直接定义为 `(P.scaleMatrix z hz).det : ℚ_p`；actual
`SelectedThetaTensor.logScaleDet` 是同一实际log-scalars的实例化。将determinant
数值在Packet层固定，避免actual D层重复合成矩阵索引，不改变数学量或参数。
generic Haar norm公式及actual region/index consumer都消费这个actual matrix
数值，factor norm乘积仍由同一matrix determinant theorem证明。新增scaleDet的
check，最终四定义、十三theorem，SceneBounds256/74、总计907/460。

S1.288 验证补记：最终窄热构建9275/9275 jobs通过、退出码0；
SceneBounds256/74与Scene1聚合通过，74条公理报告仅含标准允许集合。
最终四新模块默认heartbeat，det数值在抽象Packet层固定；完整目标仍open。

## S1.289：completion algebraic norm 与 actual raw tensor volume

| Source id | 本地声明与路径 | 来源、适配与边界 |
| --- | --- | --- |
| `JT-SCENE1-LOCAL-COMPLETION-ALGEBRA-NORM` | `LocalCompletion.norm_algebraNorm_eq_completionNorm_of_contracting`；`Act1Scene1/LocalCompletionAlgebraNorm.lean` | 以actual padicAlgebra将completion看作有限维topological ℚ_p module，通过实际finite basis把乘法linear equiv运输到ℚ_p坐标空间。generic determinant/Haar计算scalar integral ball的真实measure为norm(Algebra.norm x)，已有integer quotient/index/Haar计算同一measure.toReal为raw completion norm。对actual非零收缩scalar比较两者得等式，未假定raw completion norm有NormedSpace ℚ_p结构或等距embedding。 |
| `JT-SCENE1-LOCAL-TENSOR-RAW-VOLUME` | `LocalCompletion.Packet.normalizedHaar_scalarLattice_eq_completionNorm_product`；`Act1Scene1/LocalCompletionTensorRawVolume.lean` | 消费scalar algebraic-norm identity与S1.288 tensor Haar factorNorm乘积，计算真实contracting scalar lattice的Haar为actual completion norms的otherDimension幂乘积。 |
| `JT-SCENE1-INITIAL-THETA-SELECTED-TENSOR-RAW-VOLUME` | `SelectedThetaTensor.logFactorNorm_norm_eq_rootNorm`、`region_normalizedHaar_eq_rootNorm_product`；`Act1Scene1/IutInitialThetaSelectedTensorRawVolume.lean` | actual selected logValue norm=root norm，且nonzero/contracting来自actual source。实例化scalar norm law给logFactorNorm modulus=root norm，actual tensor region raw Haar因而等于actual roots的norm幂乘积；支持仍为全部selected prime fibre，指数保留其他factor维数。 |

结果闭合实际收缩log-scalars所需的代数norm与raw completion norm身份，不以自由
norm-law或degree证书给出。paper norm correction、factor finrank与e*f身份、
weighted tensor volume及actual collation/hull/不同untilt/Bloch–Kato仍须继续证明。
本轮不把raw Haar product改称论文最终thetaVolume。

Prologue-R5→Prologue-R5，derive，owner Scene1。新增四公共theorem，无新公共数据
定义；actual scalar Haar/index与coordinate determinant→generic raw tensor→actual
selected root norm消费者。Core/Candidate/Obligations、冻结依赖与旧API不变，
前置信任不增加。完整类型、模型义务、验证和资源见log4的S1-BND-289。

S1.289 验证补记：最终窄热构建9278/9278 jobs通过、退出码0；
SceneBounds260/78和Scene1聚合通过，78条公理报告仅含标准允许集合。
scalar代数结构在签名内由actual hw派生，三模块默认heartbeat；完整目标仍open。


## S1.290：actual completion 的 e·f 维数与 raw tensor 算术指数

| Source id | 本地声明与路径 | 来源、适配与边界 |
| --- | --- | --- |
| `JT-SCENE1-LOCAL-COMPLETION-DEGREE` | `LocalCompletion.intValuation_residueChar`、`valued_residueChar`、`norm_residueChar_eq_inv_pow_localDeg`、`finrank_padic_eq_localDeg`；`Act1Scene1/LocalCompletionDegree.lean` | 逐段适配refer/iut/Iut/Concrete/LocalConstruct/Arithmetic.lean的两个residue-characteristic valuation证明；原提交b76207ab8955e68a7408d5d2a770b75a30c3bebf，参考快照07cb1da58f6d428a670dbb5dd6093d428bcbcdd8，Git作者Christian Merten，文件作者The iut contributors。复制前核查双方Apache-2.0 LICENSE，保留版权、许可证与provenance。实际ideal factors count给v_w(p)=-e，completion norm给norm(p)=(p⁻¹)^(e*f)；本地消费S1.289代数范数身份和Algebra.norm_natCast，再由p>1的幂指数单射证明actual padicAlgebra上的finrank=e*f。未假定raw completion norm有NormedSpace ℚ_p结构。 |
| `JT-SCENE1-LOCAL-TENSOR-ARITHMETIC-VOLUME` | `LocalCompletion.Packet.factor_finrank_eq_localDeg`、`normalizedHaar_scalarLattice_eq_localDeg_product`；`Act1Scene1/LocalCompletionTensorArithmeticVolume.lean` | 任意actual Packet的每个factor以actual residueChar_eq实例化degree theorem，替换S1.289 raw scalar tensor Haar的所有otherDimension维数为actual localDeg=e*f。无新的degree/norm-law证书。 |
| `JT-SCENE1-INITIAL-THETA-SELECTED-TENSOR-ARITHMETIC-VOLUME` | `SelectedThetaTensor.region_normalizedHaar_eq_localDeg_product`；`Act1Scene1/IutInitialThetaSelectedTensorArithmeticVolume.lean` | 消费实际selected region raw root norm体积和actual factor dimension，得到全selected prime fibre上root norm的算术指数乘积。处集、重数及raw norm保留，未声称paper weighted volume或thetaVolume身份。 |

Prologue-R5→Prologue-R5，derive，owner Scene1。七公共theorem，无新自由数据
定义。实际ideal/valuation→scalar degree→Packet raw arithmetic volume→actual D
selected region；Scene1对应证明负担减少，前置信任不增加。Core/Candidate/
Obligations与旧公共API不变。完整类型、模型义务、资源与验证见log4的S1-BND-290。

实际factor finrank=e*f身份闭合；paper tensor weighting、V_p^oss/L'载体与代表
选择独立性、完整真实Scene1模型、Bloch–Kato/不同untilt、collation/hull/thetaVolume
及最终Corollary3.12仍open。维数身份不关闭上述整体数学闸门。

S1.290 验证补记（2026-10-14 05:16:00 CST）：首次窄热构建9281/9281 jobs通过，退出码0；
SceneBounds267/85与Scene1聚合通过，85条公理报告仅含标准允许集合。耗时3:38.57，
进程组采样峰值25656516KiB（约24.468GiB）；无Mathlib重编译。
七定理proved，三叶子默认heartbeat；完整数学目标仍open。


## S1.291：actual tensor 的 degree-normalized Haar volume 与 q-root log 会计

| Source id | 本地声明与路径 | 来源、适配与边界 |
| --- | --- | --- |
| `JT-SCENE1-LOCAL-TENSOR-DEGREE-VOLUME` | `LocalCompletion.Packet.tensor_finrank_eq_localDeg_prod`、`tensor_finrank_pos`、`degreeLogVolume`、`degreeVolume`、`degreeVolume_eq_exp_degreeLogVolume`、`degreeLogVolume_scalarLattice_eq_norm_sum`、`degreeVolume_scalarLattice_eq_norm_product`；`Act1Scene1/LocalCompletionTensorDegreeVolume.lean` | 独立消费S1.290 actual completion degrees与raw Haar乘积。otherDimension/total tensor dimension=1/localDeg，得到log(Haar)/finrank的局部log和及Haar^(1/finrank)的norm幂乘积。参考Volume.lean 18–23、195–204仅作normalization guide，无复制或import。积分结构取实际unitLattice，未识别为reference maximal order；只在正有限region上声称真实log-volume。 |
| `JT-SCENE1-INITIAL-THETA-SELECTED-TENSOR-DEGREE-VOLUME` | `SelectedThetaTensor.region_degreeLogVolume_eq_rootNorm_sum`、`region_degreeVolume_eq_rootNorm_product`、`region_degreeVolume_negLog_eq_ordp_sum`；`Act1Scene1/IutInitialThetaSelectedTensorDegreeVolume.lean` | actual D全部selected prime fibre及ordinary logValue nonzero/contracting/norm=root norm实例化generic law，得到actual region的degree-normalized数值乘积与negative log=∑ordp(root)*log p。无自由measure/norm/degree证书或对最终theta hull的身份声明。 |

Joshi III `ss:weighted-vol` 3522–3543的factor γ product与3554–3557 `eq:weights`
的inverse relative local degrees不能直接与本地degree normalization互换。本单元
γ=1/(e*f)，而S1.284 uniformizer normalization使用1/f，paperTerm为
 e*ordp(root)*log p；本单元negative log是ordp(root)*log p。相对次数、论文
载体、实际maximal order/hull与规范化转换仍是明确证明义务。

Prologue-R5→Prologue-R5，derive，owner Scene1；两个数值definition和八公共
定理，无新假设。实际dimension/measure→generic normalized numeric volume→
actual selected prime-fibre root/ordp consumers，对应Scene1证明负担减少，
前置信任不增加。Core/Candidate/Obligations和旧公共类型不变。
完整类型、满足模型域和构建资源见log4的S1-BND-291；完整数学目标仍open。

S1.291 验证补记（2026-10-14 05:29:26 CST）：最终窄热构建9283/9283 jobs通过，退出码0；
SceneBounds277/93与Scene1聚合通过，93条公理报告仅含标准允许集合。最终耗时
2:40.79，进程组采样峰值25708892KiB（约24.518GiB）；两次失败
及三轮总耗时400.541s已逐轮记录log4。无Mathlib重编译。两个definition及八公共
定理通过，默认heartbeat；完整数学目标仍open。


## S1.292：actual relative completion degree 与 selected tensor 相对权重

| Source id | 本地声明与路径 | 来源、适配与边界 |
| --- | --- | --- |
| `JT-SCENE1-LOCAL-COMPLETION-RELATIVE-DEGREE` | `LocalCompletion.relativeAlgebra`、`embedCompletion_padicEmb`、`relativeAlgebra_padicTower`、`finite_relativeAlgebra`、`finrank_relativeAlgebra_eq_ramification_inertia`、`inverse_relativeFinrank_eq_localDeg_ratio`、`inverse_relativeFinrank_mem_Ioc`；`Act1Scene1/LocalCompletionRelativeDegree.lean` | actual iutEmbedCompletion.toAlgebra构造真实relative completion extension。连续性及ℚ稠密性证明它与两个actual padicEmb相容，构造ℚ_p scalar tower；finite降基和finrank tower结合S1.290 absolute e*f及Prologue localDeg tower，计算relative degree=e_rel*f_rel和inverse degree=localDeg(w)/localDeg(v)，在(0,1]。本地独立证明，无参考代码复制或import；Joshi III eq:weights 3554–3557确定inverse relative degree的角色。 |
| `JT-SCENE1-INITIAL-THETA-SELECTED-TENSOR-RELATIVE-WEIGHTS` | `SelectedThetaTensor.moduliAt`、`relativeDegree`、`relativeWeight`、`relativeRootVolume`、`relativeDegree_eq_ramification_inertia`、`relativeWeight_eq_localDeg_ratio`、`relativeWeight_mem_Ioc`、`relativeRootVolume_eq_localDeg_product`、`relativeRootVolume_negLog_eq_ordp_sum`、`relativeRootVolume_eq_degreeVolume_pow_of_common_moduliDegree`；`Act1Scene1/IutInitialThetaSelectedTensorRelativeWeights.lean` | actual source torsion prime contraction到moduli，真实relative completion的finrank定义eq:weights候选权重。原始根范数的数值乘积写为localDeg(moduli)/localDeg(torsion)指数，negative log=∑localDeg(moduli)*ordp(root)*log p。显式common moduli local degree=d时，它等于actual selected region.degreeVolume^d；未从arbitrary D推导此common degree条件。 |

Prologue-R5→Prologue-R5，derive，owner Scene1；五definition、十二公共theorem，
无新假设。真实continuous completion map→padic tower/relative finite field degree→
actual selected weights/root numerical product→conditional region.degreeVolume。
对应Scene1证明负担减少，前置信任不增加。Core/Candidate/Obligations及旧API不变。

相对权重的数学数字已从真实completion扩张构造；该selected presentation尚未
证明=论文V_p^oss/L'，且raw norm与paper uniformizer norm仍需转换。不同moduli
localDeg不能无证据统一成一个Haar幂；common degree只作为明确conditional
consumer，未把其作为Core公理。maximal order、代表选择独立性/重数、完整真实
模型、Bloch–Kato/不同untilt/collation/hull/thetaVolume和最终3.12仍open。
完整public类型、模型域、资源与验证见log4的S1-BND-292。

S1.292 验证补记（2026-10-14 05:46:18 CST）：最终窄热构建9285/9285 jobs通过，退出码0；
SceneBounds294/105与Scene1聚合通过，105条公理报告仅含标准允许集合。最终耗时
2:50.48，组采样峰值25753260KiB（约24.560GiB）；前三次失败和
四轮总耗时467.443s已逐轮记录log4，无Mathlib重编。五definition/abbrev与十二
公共定理通过；common moduli degree消费者显式conditional，默认heartbeat，
完整数学目标仍open。


## S1.293：actual tensor 相对权重的区域呈现相容性审计

| Source id | 本地声明与路径 | 来源、适配与边界 |
| --- | --- | --- |
| `JT-SCENE1-LOCAL-TENSOR-WEIGHT-DESCENT` | `LocalCompletion.Packet.primeAtScalar`、`primeAtScalar_ne_zero`、`primeAtScalar_lattice_eq`、`factor_prime_norm_eq_inv_pow_localDeg`、`weightedScalarVolume`、`weightedScalarVolume_primeAt_eq`、`weightedScalarVolume_primeAt_eq_iff`、`weightedDegree_eq_of_prime_region_volume`；`Act1Scene1/LocalCompletionTensorWeightDescent.lean` | actual scalar tensor multilinearity/scaleAt_apply使primeAtScalar在任一factor放p得到相同region；actual p norm=(p⁻¹)^localDeg及rpow指数单射证明weighted norm product相同iff localDeg(i)*γ(i)相同。任何只依赖region且满足这些factor公式的函数都必须满足此条件。独立本地证明，无参考代码复制/import；Joshi III ss:weighted-vol 3522–3543将weighted product描述为tensor subset function，是此审计的数学作用来源。 |
| `JT-SCENE1-INITIAL-THETA-SELECTED-TENSOR-WEIGHT-DESCENT` | `SelectedThetaTensor.relativeWeightedPrime_eq_iff_moduliDegree_eq`、`no_relative_region_volume_of_distinct_moduliDegree`；`Act1Scene1/IutInitialThetaSelectedTensorWeightDescent.lean` | S1.292 actual inverse relative finrank给γ=localDeg(moduli)/localDeg(torsion)，所以两个prime presentations weighted值相同iff moduli localDeg相同。显式实际i,j的moduli degrees不同排除任何满足raw norm factor公式的region-only函数。未构造这样的具体D；不声称paper carrier/norm/hull等同或整个论文反例。 |

Prologue-R5→Prologue-R5，derive，owner Scene1；两个definition和八公共theorem。
V只在必要条件及否定存在证明中量化，不作为新自由volume字段进入生产者。
新增0数学假设，前置信任不增加；Scene1呈现独立性条件被精确定位。Core/
Candidate/Obligations与旧API不变。完整类型和资源见log4的S1-BND-293。

S1-MODEL-293（owner Scene1，open）：具体actual D及同一selected prime fibre中
moduli localDeg不同的两个处尚未构造。当前结论是raw norm与inverse relative
weights组合的条件性排除；paper norms、处集、untilts、grouping或额外presentation
数据的来源转换仍需复审。完整真实模型、V_p^oss/L'、代表重数/选择独立性、
maximal order、Bloch–Kato/collation/hull/thetaVolume及最终3.12仍open。

S1.293 验证补记（2026-10-14 05:57:23 CST）：最终窄热构建9287/9287 jobs通过，退出码0；
SceneBounds304/113与Scene1聚合通过，113条公理报告仅含标准允许集合。最终耗时
3:15.99，组采样峰值25684344KiB（约24.494GiB）；首轮失败与
两轮总耗时274.217s已记录log4，无Mathlib重编。两个definition及八公共定理
通过，默认heartbeat；具体actual unequal-degree D模型仍open，整体目标仍open。


## S1.294：actual relative q-root product 的完整 q-pilot 全局会计

| Source id | 本地声明与路径 | 来源、适配与边界 |
| --- | --- | --- |
| `JT-SCENE1-INITIAL-THETA-RELATIVE-QROOT-FACTOR` | `iutInitialThetaModuliSelectedSource_liesOver`、`iutInitialThetaRepresentativeCoefficient_mul_ramIdx_eq_localDeg_div_finrank`、`iutInitialThetaRelativeQRootFactor`、`iutInitialThetaRelativeQRootFactor_eq_localDeg_ratio`、`iutInitialThetaRelativeQRootFactor_mem_Ioo`、`iutInitialThetaRelativeQRootFactor_negLog_div_eq_moduliJLogTerm`；`Act1Scene1/IutInitialThetaRelativeQRootFactor.lean` | selected root来自actual moduli-source equivalence及actual section liesOver。inverse relative completion finrank（真实embedding.toAlgebra）给localDeg(moduli)/localDeg(source)，raw root norm定义positive contracting factor。actual ramification tower给representativeCoefficient*ramIdx(source)=localDeg(moduli)/globalDegree(moduli)，故factor negative log/global degree=actual moduli j-log/(2ℓ*global degree)。独立本地证明，无参考代码复制/import；Joshi III eq:weights 3554–3557是权重来源角色，paper norm/carrier/hull身份不假定。 |
| `JT-SCENE1-INITIAL-THETA-RELATIVE-QROOT-PRODUCT` | `iutInitialThetaRelativeQRootProduct`、`iutInitialThetaNormalizedRelativeQRootProduct`、`iutInitialThetaRelativeQRootProduct_pos`、`iutInitialThetaRelativeQRootProduct_negLog_div_eq_fullBaseSum`、`iutInitialThetaNormalizedRelativeQRootProduct_negLog_eq_fullBaseSum`；`Act1Scene1/IutInitialThetaRelativeQRootProduct.lean` | actual所有odd moduli representatives的finite factor product，再以moduli global degree归一化。完整moduli j-log会计给normalized product negative log=actual full odd-support base q-pilot。没有独立section coverage或sum equality证书，未删除相对次数/全局次数。乘积仍为presentation-indexed numerical value，未提升为只依赖tensor区域的volume。 |
| `JT-SCENE1-INITIAL-THETA-RELATIVE-QROOT-REFERENCE-BOUND` | `iutInitialThetaReferenceAbsLogQ_le_normalizedRelativeQRootProduct_negLog`、`Corollary312QPilotData.absLogQ_le_normalizedRelativeQRootProduct_negLog_ofCanonicalInitialThetaLink`；`Act1Scene1/IutInitialThetaRelativeQRootReferenceBound.lean` | actual VBad reference q-pilot是full odd-support sum的restriction，消费exact normalized-root product identity得到reference≤negative log；canonical Scene1/reference bridge接入同一upper bound。现有hLink/hEll和显式θ/packetHull payload保留，无新自由volume参数或最终theta estimate。 |

Prologue-R5→Prologue-R5，derive，owner Scene1；三个definition、十公共theorem。
真实relative completion factor/coefficient→完整normalized selected product→actual
reference/canonical消费者。对应Scene1归一化会计负担减少，新增0数学假设，前置
信任不增加，Core/Candidate/Obligations和旧API不变。完整类型及资源见log4的
S1-BND-294。

本单元精确等式对应full odd support；actual VBad≤full区别、S1.283去权严格
差额及S1.293区域呈现必要条件均保留。paper V_p^oss/L'与norm规范化、真正
presentation/representative independence、maximal order、完整真实模型、Bloch–Kato/
untilt/collation/hull/thetaVolume与最终3.12仍open。

S1.294 验证补记（2026-10-14 06:15:47 CST）：最终窄热构建9290/9290 jobs通过、退出码0；
SceneBounds317/123与Scene1聚合通过，123条公理报告仅含标准允许集合。最终耗时
3:41.64，组采样峰值25862828KiB（约24.665GiB）；两次失败和
三轮总耗时492.556s已逐轮记录log4，无Mathlib重编。三个definition与十公共
定理通过、默认heartbeat；actual VBad/full支撑差别及整体目标仍open。


## S1.295：actual VBad relative q-root product 的同支撑 reference/Scene1 等式

| Source id | 本地声明与路径 | 来源、适配与边界 |
| --- | --- | --- |
| `JT-SCENE1-INITIAL-THETA-VBAD-MODULI-J-ACCOUNTING` | `iutInitialThetaVBadModuliFinset`、`mem_iutInitialThetaVBadModuliFinset_iff`、`iutInitialThetaReferenceBaseModuliFiber_eq`、`iutInitialThetaReferenceAbsLogQ_eq_baseJLogSum`、`iutInitialThetaReferenceAbsLogQ_eq_VBadModuliJLogSum`；`Act1Scene1/IutInitialThetaVBadModuliJAccounting.lean` | actual D.VBad⊆odd moduli support构造finite VBad carrier，并证明membership iff D.VBad。reference badFinset_spec与canonical contraction唯一性证明Q.badFinset的moduli fibres等于实际完整BaseModuliFiber。actual admissible qOrder与source Tate j-log身份，再经完整fibre全局次数归一化，给reference absLogQ=准确VBad moduli j-log/(2ℓ*moduli global degree)。无section coverage或额外fibre证书。独立本地证明，无参考代码复制/import。 |
| `JT-SCENE1-INITIAL-THETA-VBAD-RELATIVE-QROOT-PRODUCT` | `iutInitialThetaVBadModuliAt`、`iutInitialThetaVBadRelativeQRootProduct`、`iutInitialThetaNormalizedVBadRelativeQRootProduct`、两个positive定理、`iutInitialThetaVBadRelativeQRootProduct_negLog_div_eq_referenceAbsLogQ`、`iutInitialThetaNormalizedVBadRelativeQRootProduct_negLog_eq_referenceAbsLogQ`、`iutInitialThetaNormalizedVBadRelativeQRootProduct_eq_exp_neg_referenceAbsLogQ`；`Act1Scene1/IutInitialThetaVBadRelativeQRootProduct.lean` | 精确VBad moduli representatives上限制S1.294 actual inverse relative completion degree root factor。degree-normalized product的negative log=actual reference absLogQ，产品exp(-reference absLogQ)作为后验推论，未用该exp值直接定义产品。允许空VBad，无额外非空性条件；product仍为actual presentation-indexed raw norm数值，未识别为theta/hull volume。 |
| `JT-SCENE1-INITIAL-THETA-VBAD-RELATIVE-QROOT-SCENE-BRIDGE` | `Corollary312QPilotData.absLogQ_eq_normalizedVBadRelativeQRootProduct_negLog_ofCanonicalInitialThetaLink`；`Act1Scene1/IutInitialThetaVBadRelativeQRootSceneBridge.lean` | canonical Scene1/reference q-pilot bridge消费新exact VBad root product identity，提供canonical Scene1 absLogQ同支撑negative log等式。现有hLink/hEll和显式θ/packetHull payload保留，不加入free coverage、sum equality或目标体积假设。 |

Prologue-R5→Prologue-R5，derive，owner Scene1；四个definition/abbrev、十公共
定理。actual VBad carrier/complete fibres→reference j-log→exact restricted
relative-root product→canonical Scene1 consumer。对应Scene1支撑/数值会计负担
减少，新增0数学假设，前置信任不增加，Core/Candidate/Obligations与旧API不变。
完整类型及资源见log4的S1-BND-295。

等式使用准确VBad限制，未声称reference=full odd-support。S1.293区域呈现必要
条件、paper V_p^oss/L'及norm规范化、代表选择独立性/重数、maximal order、完整
真实模型、Bloch–Kato/untilt/collation/hull/thetaVolume及最终3.12仍open。

S1.295 验证补记（2026-10-14 06:29:32 CST）：首次窄热构建9293/9293 jobs通过，退出码0；
SceneBounds331/133与Scene1聚合通过，133条公理报告仅含标准允许集合。耗时
4:28.34，组采样峰值25860184KiB（约24.662GiB）；无Mathlib
重编。四definition/abbrev与十公共定理通过、默认heartbeat；同支撑actual
reference/normalized-root product/canonical Scene1身份闭合，整体数学目标仍open。


## S1.296：fixed actual D 的 relative root factor / VBad product 代表选择独立性

| Source id | 本地声明与路径 | 来源、适配与边界 |
| --- | --- | --- |
| `JT-SCENE1-INITIAL-THETA-RELATIVE-QROOT-CHOICE` | `iutInitialThetaFullQRoot_pow_norm_inv_eq_torsionJNorm`、`iutInitialThetaRelativeQRootFactorAt`、`iutInitialThetaRelativeQRootFactorAt_eq_inverse_relativeFinrank`、`iutInitialThetaRelativeQRootFactorAt_mem_Ioo`、`iutInitialThetaRelativeQRootFactorAt_negLog_eq_moduliJLog`、`iutInitialThetaRelativeQRootFactorAt_eq_of_liesOver`、`iutInitialThetaRelativeQRootFactorAt_eq_selectedFactor`；`Act1Scene1/IutInitialThetaRelativeQRootChoice.lean` | actual root幂方程与base Tate j-norm给(norm(root)^(2ℓ))⁻¹=torsion j-norm。actual moduli/torsion completion norm transfer与D的algebra tower把该j-norm写为moduli j-norm的actual relative degree幂；inverse relative degree因子negative log=moduli j-log/(2ℓ)，仅由fixed D和moduli place决定。任意两actual source places above同一moduli place给相同数值因子，并与canonical selected factor相同。独立本地证明，无参考代码复制/import；paper carrier/norm/untilt/hull身份不假定。 |
| `JT-SCENE1-INITIAL-THETA-VBAD-QROOT-CHOICE` | `iutInitialThetaVBadRootSelector_injective`、`iutInitialThetaVBadRelativeQRootProductOf`、`iutInitialThetaNormalizedVBadRelativeQRootProductOf`、`iutInitialThetaVBadRelativeQRootProductOf_eq_canonical`、`iutInitialThetaNormalizedVBadRelativeQRootProductOf_eq_canonical`、`iutInitialThetaNormalizedVBadRelativeQRootProductOf_negLog_eq_referenceAbsLogQ`、`iutInitialThetaVBadRelativeQRootProductOf_choice_independent`；`Act1Scene1/IutInitialThetaVBadQRootChoice.lean` | ρ只要求ρ(v)为actual full torsion source且liesOver对应VBad moduli place。unique contraction派生selector单射，无额外重数证书；local factor choice law给all合法ρ产品=canonical VBad产品、normalized negative log=actual reference absLogQ。两个selector的raw加权产品相同。 |
| `JT-SCENE1-INITIAL-THETA-VBAD-QROOT-CHOICE-SCENE-BRIDGE` | `Corollary312QPilotData.absLogQ_eq_choiceVBadRelativeQRootProduct_negLog_ofCanonicalInitialThetaLink`；`Act1Scene1/IutInitialThetaVBadQRootChoiceSceneBridge.lean` | existing canonical Scene1/reference同支撑q-pilot桥消费任意actual selector的product equality；保留hLink/hEll与θ/packetHull显式数据，不加free numerical equality或目标volume假设。 |

Prologue-R5→Prologue-R5，derive，owner Scene1；三个definition、十二公共theorem。
actual root/Tate j/norm transfer→fixed-D local factor choice invariance→VBad
selector单射/global product/reference identity→canonical Scene1消费者。对应
Scene1实际数值代表选择/重数会计负担减少，新增0数学假设，前置信任不增加；
Core/Candidate/Obligations与旧API不变。完整类型与资源见log4的S1-BND-296。

范围为fixed actual D的torsion field/source，在同一moduli place上变换actual
source over-place；未比较不同D、不同torsion fields或untilts/论文L'全部代表。
S1.293 tensor region呈现条件、完整paper carrier/norm、joint真实模型、maximal
order、Bloch–Kato/untilt/collation/hull/thetaVolume和最终3.12仍open；不能仅以
本fixed-D数值不变性勾选完整论文代表独立性闸门。

S1.296 验证补记（2026-10-14 06:54:27 CST）：最终窄热构建9296/9296 jobs通过，退出码0；
SceneBounds346/145与Scene1聚合通过，145条公理报告仅含标准允许集合。最终耗时
3:37.21，组采样峰值25823460KiB（约24.627GiB）；首轮失败和
两轮总耗时378.571s已记录log4，无Mathlib重编。三个definition及十二公共定理
通过、默认heartbeat；fixed-D实际数值代表选择独立性闭合，整体数学目标仍open。

S1.297 验证补记（2026-10-14 07:15:44 CST）：最终热构建9297/9297 jobs通过，退出码0；
SceneBounds351/148与Scene1聚合通过，148条公理报告仅含标准允许集合。最终耗时
2:14.52，组采样峰值25808604KiB（约24.613GiB）；前五次失败与
六轮总耗时502.130s记录log4，无Mathlib重编。两个definition/三个theorem
通过、默认heartbeat；structural repeated packet volume identities闭合，整体目标仍open。


## S1.298：Corollary312 qProduct 的独立会计公式

`JT-SCENE1-COR312-QPRODUCT-ACCOUNTING`：`Corollary312QProductAccounting.lean`
新增三个公共theorem，显式在命题中安装`T.qIndexFintype`，证明qProduct正性和
ellStar幂与有限qFactor log/negative-log和的转换。只提供目标层代数会计；真实
q-family、paper carrier、thetaVolume和最终3.12仍open。
S1.298最终构建9298/9298通过，SceneBounds354/151、全工程1005/547，耗时2:15.75，
组采样峰值25796124KiB（约24.601GiB），无Mathlib重编。


## S1.299：paper residue-degree norm 与 actual relative norm 的局部转换

`JT-SCENE1-INITIAL-THETA-PAPER-RELATIVE-NORM-BRIDGE`：
`IutInitialThetaPaperRelativeNormBridge.lean`定义actualPaperRootNorm并证明
positive、actual relative factor与paper root norm的rpow转换，以及negative-log
转换。结论使用localDeg=ramIdx*inertDeg和actual liesOver；没有识别paper L'、
untilt、Bloch–Kato或theta hull。S1.299构建9299/9299通过，SceneBounds354/155、
全工程1009/551，耗时2:34.69，组峰值25871060KiB（约24.673GiB），无Mathlib重编。


## S1.300：paper corrected root norm 与 actual Haar root ball 的来源 bridge

`JT-SCENE1-INITIAL-THETA-PAPER-ROOT-HAAR-BRIDGE`：
`IutInitialThetaPaperRootHaarBridge.lean`证明actualPaperRootNorm等于actual
root integral ball normalized Haar的residue-degree修正，且negative log复用
paper term；未识别paper L'、Bloch–Kato、untilt或theta hull。S1.300构建9300/9300
通过，SceneBounds354/158、全工程1012/554，耗时2:32.61，组峰值25808556KiB
（约24.613GiB），无Mathlib重编。


## S1.301：selected paper root norm product 与实际 corrected Haar product

`JT-SCENE1-INITIAL-THETA-SELECTED-PAPER-ROOT-NORM-PRODUCT`，路径
`Act1Scene1/IutInitialThetaSelectedPaperRootNormProduct.lean`。新definition
actualSelectedPaperRootNormProduct直接在实际selected source subtype上取paper
root norms的有限乘积；三个theorem逐项消费S1.300 norm/Haar bridge，证明与
selectedPaperBallProduct相等、属于(0,1)、negative log=selected paper sum。
精确导入、独立本地证明，无参考工程复制/import。模型域为实际D完整selected
source；没有论文carrier、theta hull或Bloch–Kato身份。Prologue-R5→R5，derive，
owner Scene1，新增0假设，前置信任不增加。完整类型/负担/资源见log4 S1-BND-301。

2026-10-14 07:49:45 CST最终窄热构建9301/9301通过，耗时2:39.75，组采样峰值
25873892KiB（约24.675GiB）；首轮失败和两轮总耗时
252.227s已记录。162条公理报告仅含标准允许集合，无Mathlib源码重编。
源码枚举SceneBounds365/162、总计1016/548纠正历史累计漂移；整体目标仍open。

## S1.302：fixed-place repeated log tensor Haar 与 actual VBad q-pilot

`JT-SCENE1-INITIAL-THETA-REPEATED-ROOT-HAAR`，路径
`Act1Scene1/IutInitialThetaRepeatedRootHaar.lean`，消费S1.297的actual repeated
packet Haar公式和actual ordinary logValue norm。来源组织为Joshi III
th:moccor-Mochizuki-form2 3624–3631的fixed-place tensor；本地独立证明，无
参考代码复制/import。packet/region/moduliVolume及三个定理证明实际重复log
scalar lattice的degreeVolume为root norm的n/localDeg幂，按moduli localDeg
修正后等于actual relative root factor的n次幂，且严格为正。

`JT-SCENE1-INITIAL-THETA-VBAD-REPEATED-HAAR-PRODUCT`，路径
`Act1Scene1/IutInitialThetaVBadRepeatedHaarProduct.lean`，直接从上述local Haar
volume定义actual VBad全局乘积，显式按moduli global finrank规范化。三个定理
证明等于canonical normalized root product的n次幂、negative log=n*reference
absLogQ，且对合法actual over-place selector独立。局部和全局修正幂均显式；
未以q-pilot指数或目标lower bound定义volume。

Prologue-R5→R5，derive，owner Scene1；新增0数学假设，前置信任不增加。
本轮闭合fixed-place普通重复log tensor的Haar/q-root/VBad q-pilot数值连接。
Fin n factors是同一actual completion/log scalar的重复，未构造不同untilts、
τ_j或Bloch–Kato classes，未识别paper thetaVolume。论文V_p^oss/L'、joint
真实模型、maximal order/collation/hull及最终Corollary3.12仍open。
完整公共类型、动态边界和构建资源见log4 S1-BND-302。

2026-10-14 07:56:55 CST首轮窄热构建9303/9303通过，耗时3:37.41，进程组
采样峰值25726216KiB（约24.534GiB），最大同时Lean workers为3，无Mathlib
源码重编。172条公理报告仅含标准允许集合；源码枚举SceneBounds375/172、
全部家族1026/558。十个公共声明通过；整体目标仍open。

## S1.303：实际区域包含到 VBad Haar 下界和负平均 log 界

`JT-SCENE1-LOCAL-TENSOR-VOLUME-MONOTONICITY`，路径
`Act1Scene1/LocalCompletionTensorVolumeMonotonicity.lean`，从Mathlib的measure
mono/toReal/rpow单调性证明actual Packet的degreeVolume单调性。上层Haar必须
有限，以排除ENNReal.toReal(∞)=0；不要求measurability的外测度包含也适用。
另外证明unit lattice体积为1、其中任意区域体积≤1。对应Joshi III
th:moccor-Mochizuki-form2 3624–3631的测度步骤；本轮无参考代码复制/import。
非负性由generic degreeVolume_nonneg独立命名，供actual有限乘积比较直接调用，
避免在实际D上展开完整Haar/rpow定义；generic共四个定理。

`JT-SCENE1-INITIAL-THETA-VBAD-REGION-VOLUME-BOUND`，路径
`Act1Scene1/IutInitialThetaVBadRegionVolumeBound.lean`，对actual VBad区域族H
直接按实际normalized Haar、localDeg幂与moduli global finrank根定义体积。
S1.302 repeated log lattice逐处包含于H且Haar有限时，派生其global product下界
和正性。H逐处包含于unit lattice时，派生volume≤1；再在合法over-place selector
下证明abs(log volume)≤n*reference absLogQ，以及n>0时负平均log≥reference lhs。
来源为上述包含步骤与cor:cor312 3634–3650的符号转换；不是自由体积或显式目标
lower-bound参数。generic mono由actual产品消费者调用，产品下界由log消费者调用。

模型证据：现有scalarLattice_le_unitLattice加actual logValue norm<1证明
region≤unit，H=region满足两侧包含和finite Haar；未构造特定InitialThetaData。
Prologue-R5→R5，derive，owner Scene1；新增0Core假设、退休0字段、边界迁移0，
前置信任不增加。普通固定处重复tensor的测度传递闭合，不同untilts/Bloch–Kato、
paper carrier/maximal order/weighted normalization和实际theta hull包含仍open。
完整公共类型、动态负担及构建资源见log4 S1-BND-303。


2026-10-14 08:09:45 CST最终窄热构建9305/9305通过，耗时3:10.41，组采样
峰值25805288KiB（约24.610GiB），最大同时Lean workers=3，无Mathlib重编。
首轮whnf超时与两轮总耗时348.089s见log4；默认heartbeat重试通过。
182条公理报告仅含标准允许集合；SceneBounds385/182、总计1036/568。
新增十个公共声明通过，整体Scene1目标仍open。

## S1.304：actual integral hull/collation 与 Haar 定量消费者

`JT-SCENE1-LOCAL-TENSOR-INTEGRAL-HULL`，路径
`Act1Scene1/LocalCompletionTensorIntegralHull.lean`，定义actual tensor空间中
集合U的最小Z_p-submodule integralHull=span(U)和scalar pure generators。
七个定理证明最小性、hull(iUnion)=iSup(hull)、scalar generators的hull等于
actual scalar lattice、generator覆盖导出的lattice包含、unit包含、open及
compact。来源为Joshi III pr:convexes-and-hulls 3597–3609的Z_p-module hull
描述；由Mathlib独立本地重证，无参考代码复制/import。没有把span命名为已识别
的paper holomorphic hull，亦未提供direct-sum fields/maximal-order身份。

`JT-SCENE1-INITIAL-THETA-VBAD-COLLATED-INTEGRAL-HULL`，路径
`Act1Scene1/IutInitialThetaVBadCollatedIntegralHull.lean`，从actual VBad的
component subsets C(v,k)构造union的integralHull和直接Haar volume。六个定理
消费generic hull：collation iSup等式、unit upper、由generator覆盖派生whole
repeated log lattice包含及compactness，然后消费S1.303的Haar lower/log界。
来源为上述hull组织、le:volume-lemma3 3576–3583、contained-region volume
argument 3624–3631。量化下界和体积正性不是输入；C的actual generator覆盖、
component unit包含仍显式保留。索引κ任意，有限collation为特例。

模型域为actual D/合法ρ的普通固定处Fin n重复tensor；empty C没有自动coverage。
未构造特定D，未从不同untilts/theta/Bloch–Kato来源构造C，也未证明与paper
weighted volume规范化相同。Prologue-R5→R5，derive，owner Scene1；新增0Core
假设、退休0字段、迁移0，前置信任不增加。结构性integral hull和其定量消费者
负担闭合；整体Scene1数学门槛仍open。完整类型和资源见log4 S1-BND-304。


2026-10-14 08:21:58 CST最终热构建9307/9307通过，耗时3:19.87，进程组采样
峰值25870260KiB（约24.672GiB），最大同时Lean workers=3，无Mathlib重编。
首轮instance重名失败与两轮总耗时329.996s记录log4。199条公理报告仅含标准
允许集合；源码枚举SceneBounds402/199、全部家族1053/585。17个公共声明
通过、默认heartbeat；整体Scene1目标仍open。

## S1.305：字面 Corollary 3.12 显示式的符号排除证据

`JT-SCENE1-COR312-LITERAL-SOURCE-SIGN-AUDIT`，路径
`Act1Scene1/Corollary312SourceSignAudit.lean`，来源Joshi III cor:cor312
3647–3650、前文符号讨论3634–3645及volume lower bound 3617–3632。
一个definition直接取actual selected finite paper root norms的signed log和；
七个定理从actual产品∈(0,1)及log-product等式证明literal RHS=-sum(log)>0，
而negative-average abs log恒≤0，故任何实数volume/自然数n均不能满足这条
字面式。另证明现有Corollary312要求qLogSum≥0，并在qLogSum等于actual signed
log和时排除该target。无参考代码复制/import，自有完整proof term。

来源忠实度纠正：旧Corollary312/VolumeBridge记录的“exact analytic inequality
shape”不能作为当前完整来源验收证据。工程VolumeBound/QFamily选择
qLogTerm=-log(qFactor)，当前target RHS是sum(log(qFactor))，而原文显示式
是负sum(log(qFactor))。后者在contracting ordinary norms下严格为正，与
前文左右均负不相容；前者可由volume lower bound派生。未决定哪一source
解释或更正可作为最终目标，不改旧API，最终freeze义务仍open。

证据范围：给定actual D的selected products，不是特定D的构造；selected
carrier与paper V_p^oss/L'身份未闭合，亦未对所有非标准signed-log解释作
反例主张。Prologue-R5→R5，derive，owner Scene1；新增Core假设0、退休0字段、
迁移0，前置信任不增加。闭合符号排除，新增明确source sign复审义务；整体
Scene1目标未完成。完整类型、动态负担与资源见log4 S1-BND-305。


2026-10-14 08:28:52 CST首轮热构建9308/9308通过，耗时2:34.31，进程组采样
峰值25889992KiB（约24.691GiB），最大同时Lean workers=3，无Mathlib重编。
207条公理报告仅含标准允许集合；源码枚举SceneBounds410/207、总计1061/593。
八个公共声明通过、默认heartbeat；接受为负面证据，最终来源/符号freeze仍open。

## S1.306：fixed-moduli inverse-relative-degree tensor Haar

`JT-SCENE1-LOCAL-TENSOR-VOLUME-POWER`，路径
`Act1Scene1/LocalCompletionTensorVolumePower.lean`，消费actual tensor Haar
dimension-root公式，证明degreeVolume(scalarLattice)^d=prod(norm^(d/localDeg))。
来源是actual Haar/dimension和Joshi III ss:weighted-vol/eq:weights的比较；
独立本地证明，无参考代码复制/import，不把此数值幂视为新的additive measure。

`JT-SCENE1-INITIAL-THETA-FIXED-MODULI-TENSOR-VOLUME`，路径
`Act1Scene1/IutInitialThetaFixedModuliTensorVolume.lean`。给定actual moduli处v，
σ为其任意finite tuple of actual torsion over-places，packet的同prime性质直接
由liesOver派生。weight用实际relative completion algebra的finrank倒数定义；
比值与(0,1]性质由actual relative degree laws证明。scalarVolume从tensor
region Haar派生，非零contracting任意标量下等于inverse-relative-degree norm
产品。actual ordinary logValue region的volume为canonical relative root factor
的tuple cardinality次幂，严格正且不依赖σ/τ合法over-place tuple选择。
公共API为packet abbrev、四definition、六theorem，与generic theorem合计12项。

对应Joshi III eq:weights 3554–3557，common moduli localDeg条件在此域由固定v
构造满足；S1.293混合moduli degrees的障碍仍保留。源自同一actual D/torsion
field的不同over-places，不是different untilts；未构造特定D。choice-independent
只比较实数volume，没有跨tensor carriers的isometry或region identity。
raw completion norm convention与paper 1/f norm、maximal order、weighted
thetaVolume/carrier身份仍须复审。Prologue-R5→R5，derive，owner Scene1；
新增Core假设0、退休0字段、迁移0，前置信任不增加。完整签名、动态边界与资源
见log4 S1-BND-306；S1.305 source sign复审及整体Scene1目标继续open。


2026-10-14 08:36:58 CST首轮热构建9310/9310通过，耗时3:07.47，进程组采样
峰值25875620KiB（约24.677GiB），最大同时Lean workers=3，无Mathlib重编。
219条公理报告仅含标准允许集合；源码枚举SceneBounds422/219、总计1073/605。
十二个公共声明通过、默认heartbeat；common-v relative-weight Haar呈现闭合，
整体Scene1目标仍open。

## S1.307：actual tensor order normalization 与 residue-field algebra decomposition

`JT-SCENE1-LOCAL-TENSOR-ORDER-NORMALIZATION`，路径
`Act1Scene1/LocalCompletionTensorOrder.lean`。从Mathlib PiTensorProduct为实际
completion tensor提供CommRing/Q_p algebra/Z_p restricted algebra，证明纯张量
乘法、unit lattice含1和乘法封闭，构造有限unitSubalgebra。已有actual unit
lattice的finite-module证明推出其元素IsIntegral；直接定义normalization为
Z_p integralClosure，派生unit≤normalization及normalization开放、闭合。
没有将unit order与其normalization等同，也未假定normalization紧致。

`JT-SCENE1-LOCAL-TENSOR-RESIDUE-DECOMPOSITION`，路径
`Act1Scene1/LocalCompletionTensorResidueDecomposition.lean`。由actual finite
characteristic-zero completion extensions证明formally unramified tensor，进而
reduced；actual有限张量基给Artinian。构造residueDecomposition为Q_p-algebra
等价到MaximalSpectrum上的quotient产品，证明evaluate=quotient和quotient
images共同决定tensor元素。Mathlib Artinian/Module.lean:516的实例保证该
MaximalSpectrum有限，624的equivPi是finite product of residue fields。
residue-field norms/normalization有限性与compactness尚未构造。

经逐文件许可证审查移植Integral.lean/MaximalOrder.lean中的restricted algebra、
unit-order乘法/finite integrality、formal-unramified tensor论证。参考快照
07cb1da58f6d428a670dbb5dd6093d428bcbcdd8；两文件原提交
b76207ab8955e68a7408d5d2a770b75a30c3bebf，Git作者Christian Merten，文件作者
The iut contributors，Apache-2.0原头与通知保留，登记LICENSES.md。改写为
actual completion factors，不复制reference junk quotients、hull/volume fields，
无Iut import或参考依赖。来源解释包括IUT IV Prop1.2/order normalization和
Joshi III direct-sum fields 3590–3595；不接受参考工程最终3.12结论。

Prologue-R5→R5，derive，owner Scene1；新增Core假设0、退休0字段、边界迁移0，
前置信任不增加。闭合actual tensor algebra/order integrality与代数field产品
分解。尚未证明paper norms、maximal-order Haar normalization或theta hull身份；
完整Scene1/Corollary3.12仍open。完整公共类型和资源见log4 S1-BND-307。


2026-10-14 08:45:37 CST首轮热构建9312/9312通过，耗时2:44.51，进程组采样
峰值25871000KiB（约24.673GiB），最大同时Lean workers=3，无Mathlib重编。
239条公理报告仅含标准允许集合；源码枚举SceneBounds442/239、总计1093/625。
二十个公共声明通过、默认heartbeat；normalization compact/paper hull身份及
整体Scene1目标仍open。


## S1.308：actual normalization finite/compact 与 Haar 比较

`JT-SCENE1-LOCAL-TENSOR-NORMALIZATION-COMPACT`，路径
`Act1Scene1/LocalCompletionTensorNormalizationCompact.lean`，给quotient补齐
实际Z_p/Q_p scalar tower；使用finite separable residue fields的integral closure
Noetherian性和actual residue分解构造injective normalization map，证明
normalization为有限Z_p模。有限span有界、finite generators的image span给
normalization有界；已有closed与actual finite-dimensional proper topology给compact。
经复制前逐文件审查移植reference MaximalOrder.lean 240–335论证，原提交
b76207ab8955e68a7408d5d2a770b75a30c3bebf，快照
07cb1da58f6d428a670dbb5dd6093d428bcbcdd8；Git作者Christian Merten，文件
作者The iut contributors，Apache-2.0版权通知和来源头保留，LICENSES.md登记。
无reference import/dependency、无junk quotient或自由volume合同移植。

`JT-SCENE1-LOCAL-TENSOR-NORMALIZATION-HAAR`，路径
`Act1Scene1/LocalCompletionTensorNormalizationHaar.lean`，原创定义实际compact
open normalization的PositiveCompacts和normalized Haar。证明该measure在
normalization处为1、旧unit-lattice Haar在normalization处的mass属于[1,∞)，
并由Haar唯一性证明每个Set上old Haar=normalizationMass*new Haar。该倍率
保留两integral structures的区别，不假定unit lattice=normalization。

Prologue-R5→R5，derive，owner Scene1；新增Core假设0、退休字段0、迁移0，
前置信任不增加。闭合actual integral closure finite/bounded/compact和Haar倍率。
尚未证明paper norm、scaled maximal-order volume、residue norms/least hull、
thetaVolume身份或different untilt/Bloch–Kato来源；整体Scene1目标仍open。
完整类型、动态边界与资源见log4 S1-BND-308。


2026-10-14 09:00:25 CST最终热构建9314/9314通过，耗时2:17.10，进程组采样
峰值25648552KiB（约24.460GiB），最大同时Lean workers=3，无Mathlib重编。
两次失败与三轮总耗时357.787s见log4；255条公理报告仅含标准允许集合。
源码枚举SceneBounds458/255、总计1109/641；16个公共声明通过、默认heartbeat。
actual normalization finite/compact及Haar倍率闭合，整体Scene1目标仍open。


## S1.309：scalar normalization 饱和与 degree Haar 公式

`JT-SCENE1-LOCAL-TENSOR-SCALAR-NORMALIZATION`，路径
`Act1Scene1/LocalCompletionTensorScalarNormalization.lean`，由actual tensor
multiplication证明scale(z)=乘以pure(z)，构造scalarNormalization=normalization
的scaleIntegral像。证明原scalar lattice包含其中、它对normalization乘法稳定、
并是包含原lattice的此类Z_p模块中最小者；contracting/integral z下它包含于
normalization，且非零z下compact。实际normalization Haar给det norm，新的
normalizationDegreeVolume在此扩大region上等于旧degreeVolume在原scalar
lattice上的值。来源为actual integral closure/scale/det/Haar和Joshi III
scalar maximal-order shape 3568–3574的比较；原创本地证明，无参考代码复制/import。

`JT-SCENE1-INITIAL-THETA-FIXED-MODULI-NORMALIZATION-VOLUME`，路径
`Act1Scene1/IutInitialThetaFixedModuliNormalizationVolume.lean`，从actual D、
同一moduli处的合法source tuple及ordinary logValue构造饱和region，用新的
normalization Haar定义corrected volume。三个定理消费generic degree identity
和S1.306消费者，证明等于旧unitVolume、canonical relative factor^card，且
不依赖合法over-place tuple选择。私有nonzero证明来自actual root，不增加假设。

Prologue-R5→R5，derive，owner Scene1；新增Core假设0、退休字段0、迁移0，
前置信任不增加。闭合scalar-region normalization-module最小扩大及其Haar
量化、实际log tuple消费者。不等同两integral structures或同一region的两Haar；
保持数值公式是region与measure同时调整。least property不提供任意U的least
componentwise principal hull，未识别paper residue norms/weighted volume/theta
loci、different untilts/Bloch–Kato/V_p^oss/L'；S1.305 sign freeze仍open。
完整类型、动态边界和资源见log4 S1-BND-309；整体Scene1目标未完成。


2026-10-14 09:14:24 CST最终热构建9316/9316通过，耗时3:07.46，进程组采样
峰值25848812KiB（约24.651GiB），最大同时Lean workers=3，无Mathlib重编。
两次失败与三轮总耗时337.388s见log4；271条公理报告仅含标准允许集合。
源码枚举SceneBounds474/271、总计1125/657；16个公共声明通过、默认heartbeat。
scalar normalization饱和/Haar identity及实际消费者闭合，整体Scene1目标仍open。


## S1.310：normalization 产品身份与 scalar residue principal 区域

`JT-SCENE1-LOCAL-TENSOR-NORMALIZATION-DECOMPOSITION`，路径
`Act1Scene1/LocalCompletionTensorNormalizationDecomposition.lean`，证明实际
Tensor元素IsIntegral Z_p当且仅当每个maximal residue坐标integral。逆向通过
finite product of residue integral closures中的tuple的integrality，再用actual
residueDecomposition的injective Z_p algebra map回传；不输入surjectivity证书。
构造normalizationResidueMap并证明bijective，得到normalizationDecomposition
为Z_p algebra等价到residue integral closures产品，逐坐标evaluate=quotient。
原创本地证明，无参考代码复制/import。

`JT-SCENE1-LOCAL-TENSOR-SCALAR-RESIDUE-REGION`，路径
`Act1Scene1/LocalCompletionTensorScalarResidueRegion.lean`。给定actual Packet
和nonzero factor tuple z，证明pure(z)unit，每个residue multiplier为unit/nonzero；
‖z_i‖≤1时multiplier integral。对所有actual tensor元素x证明
x∈scalarNormalization(z) iff每个坐标属于lambda_I*integralClosure_I，inverse
witness由residueDecomposition.symm构造；覆盖双向而非仅包含。来源比较为
Joshi III 3568–3574的componentwise principal-region形状。

Prologue-R5→R5，derive，owner Scene1；新增Core假设0、退休0字段、迁移0，
前置信任不增加。闭合actual normalization产品身份和scalar-region exact形状。
O_I此处是actual integralClosure，尚未证明residue-field unit norm ball身份；
也未给任意U的least hull存在、different untilt/Bloch–Kato/theta loci来源、paper
V_p^oss/L'/weighted-volume或最终source sign freeze。整体Scene1目标仍open。
完整公共类型、动态边界及资源见log4 S1-BND-310。


2026-10-14 09:32:40 CST最终热构建9318/9318通过，耗时2:45.69，进程组采样
峰值25882652KiB（约24.684GiB），最大同时Lean workers=3，无Mathlib重编。
两次失败与三轮总耗时314.494s见log4；282条公理报告仅含标准允许集合。
源码枚举SceneBounds485/282、总计1136/668；11个公共声明通过、默认heartbeat。
normalization产品身份和scalar componentwise形状闭合，整体Scene1目标仍open。


## S1.311：actual residue spectral norm 与 unit/radius ball 区域

`JT-SCENE1-LOCAL-TENSOR-RESIDUE-SPECTRAL-NORM`，路径
`Act1Scene1/LocalCompletionTensorResidueNorm.lean`，提供actual residue field与
finite Q_p module instances，定义spectralNorm，证明nonnegative/zero/one/
multiplicative/nonzero/positive/base-norm extension/inverse laws。minpoly与
Z_p coeff lifts证明IsIntegral Z_p iff norm≤1，显式构造spectral NormedField，
并证明其closed unit ball=actual integral closure。不无证明等同tensor coordinate
或quotient topology，也不识别paper C_p绝对值归一化。

经复制前许可证审查移植reference ResidueField.lean 89–146；原提交
fe96f99cae5c6d48d25113163f1b9b388fc35814，快照
07cb1da58f6d428a670dbb5dd6093d428bcbcdd8，Git作者Christian Merten，文件作者
The iut contributors，Apache-2.0来源与版权通知保留、LICENSES.md登记。
改为actual completion tensor residue fields，无reference import/dependency；
不复制junk quotient、free volume字段或arbitrary least-hull代码。

`JT-SCENE1-LOCAL-TENSOR-RESIDUE-BALL-REGIONS`，路径
`Act1Scene1/LocalCompletionTensorResidueBallRegions.lean`，消费S1.310的component
integrality/scalar principal iff，证明normalization membership iff全部residue
norm≤1；scalarNormalization membership iff各residue norm≤对应multiplier norm。
反向principal-region证书由nonzero multiplier的inverse实际构造，两边均证明。
来源比较为Joshi III 3568–3574，尚未构造arbitrary U的least hull。

Prologue-R5→R5，derive，owner Scene1；新增Core假设0、退休字段0、迁移0，
前置信任不增加。闭合actual residue spectral norm与O_I unit-ball身份和实际
region双向radius判据；discrete value group、topology transfer、least hull、
paper normalization/theta loci/untilt/Bloch–Kato/V_p^oss/L'与最终source sign
freeze仍open。完整公共类型、动态边界与资源见log4 S1-BND-311。


2026-10-14 09:49:08 CST最终热构建9320/9320通过，耗时2:40.77，进程组采样
峰值25890852KiB（约24.691GiB），最大同时Lean workers=3，无Mathlib重编。
首轮metric选择失败与两轮总耗时234.175s见log4；299条公理报告仅含允许集合。
源码枚举SceneBounds502/299、总计1153/685；17个公共声明通过、默认heartbeat。
actual spectral unit ball和region判据闭合，整体Scene1目标仍open。


## S1.312：actual discrete spectral radii 与 integral principal hull

`JT-SCENE1-LOCAL-TENSOR-RESIDUE-DISCRETE-RADII`，路径
`Act1Scene1/LocalCompletionTensorResidueNormDiscrete.lean`，定义actual residue
finrank的factorial exponent；由minpoly常数项spectral formula和p-adic valuation
证明非零元素norm^exponent=p^integer。再用Int bounded least existence构造任意
positive radius以上的least attainable norm，无discreteness/least radius输入。

`JT-SCENE1-LOCAL-TENSOR-PRINCIPAL-RADIUS-MINIMUM`，路径
`Act1Scene1/LocalCompletionTensorPrincipalRegions.lean`，证明tensor unit iff各
residue coordinates非零，principalRegion(a)=a*normalization的双向radius判据。
选择各坐标least norm并用actual residueDecomposition.symm回组unit a，给出
least principal region whose radii dominate正family M。integral U⊆normalization
且each-coordinate有非零点时，coordinate supremum有界正、构造包含U的least
principal hull，并与1候选比较派生a integral。不把sup positivity或least hull作
自由输入。paper比较来源为Joshi III componentwise shape 3568–3574。

两文件经逐文件许可证复核移植reference ResidueField.lean 202–235/240–313，
原提交fe96f99cae5c6d48d25113163f1b9b388fc35814，快照
07cb1da58f6d428a670dbb5dd6093d428bcbcdd8，Git作者Christian Merten，文件作者
The iut contributors；Apache-2.0来源头及版权通知保留，LICENSES.md登记。
least integral-U消费者为本地构造，无reference import/dependency。

Prologue-R5→R5，derive，owner Scene1；新增Core假设0、退休字段0、迁移0，
前置信任不增加。闭合actual discrete radii和上述integral-domain least hull。
一般bounded U的residue bounds、positive Haar推出coordinate nonzero与compact/
open hull measure消费者仍需证明；paper theta/untilt/Bloch–Kato/V_p^oss/L'/norm/
weighted-volume与最终source sign freeze仍open。完整签名和资源见log4 S1-BND-312。


2026-10-14 10:06:49 CST最终热构建9322/9322通过，耗时2:17.47，进程组采样
峰值25803108KiB（约24.608GiB），最大同时Lean workers=3，无Mathlib重编。
首轮失败与两轮总耗时246.909s见log4；307条公理报告仅含标准允许集合。
源码枚举SceneBounds510/307、总计1161/693；8个公共声明通过、默认heartbeat。
actual discrete radii和条件integral least principal hull闭合，整体Scene1目标仍open。


## S1.313：一般 bounded positive-Haar tensor region 的 least principal hull

`JT-SCENE1-LOCAL-TENSOR-BOUNDED-RESIDUES`，路径
`Act1Scene1/LocalCompletionTensorResidueBounds.lean`，从actual unit lattice邻域
与unit≤normalization派生normalization含正半径球；scalar contraction把任意
bounded U送入normalization，spectral base extension给所有residue norm的统一界。
不输入spectral与tensor拓扑比较证书。

`JT-SCENE1-LOCAL-TENSOR-HAAR-RESIDUE-WITNESSES`，路径
`Act1Scene1/LocalCompletionTensorHaarSubspaces.lean`，证明actual proper Q_p
subspace的normalization Haar测度为0；positive Haar U不可能包含于任一maximal
ideal，因此每residue coordinate有非零点，不作为额外输入。

`JT-SCENE1-LOCAL-TENSOR-BOUNDED-LEAST-HULL`，路径
`Act1Scene1/LocalCompletionTensorBoundedHull.lean`，从unit multiplier构造actual
Q_p principal linear equivalence，证明principal region compact/open与positive
finite Haar。coordinate sup用上述uniform bounds及nonzero witnesses消费S1.312
least radii，构造任意bounded positive normalization-Haar U的least principal
hull，对所有unit principal candidates最小。不再限制U⊆normalization。

经逐文件许可证审查改写reference Hull.lean，原提交
fe96f99cae5c6d48d25113163f1b9b388fc35814，快照07cb1da58f6d428a670dbb5dd6093d428bcbcdd8，
Git作者Christian Merten，文件作者The iut contributors，Apache-2.0来源头及
通知保留，LICENSES.md登记；无Iut import/参考依赖。paper比较为Joshi III
3568–3574的componentwise principal形状，不接受参考最终3.12结论。

Prologue-R5→R5，derive，owner Scene1；新增Core假设0、退休字段0、迁移0，前置
信任不增加。閉合actual bounded positive-Haar least hull与topology/Haar输出。
未构造真实theta locus U或untilt/Bloch–Kato输入，paper norm/weighted-volume/
V_p^oss/L'/global thetaVolume及source sign freeze仍open；完整记录见S1-BND-313。


2026-10-14 10:29:56 CST最终热构建9325/9325通过，耗时2:15.12，进程组采样
峰值25858352KiB（约24.660GiB），最大同时Lean workers=3，无Mathlib重编。
三次失败与四轮总耗时392.991s见log4；317条公理报告仅含标准允许集合。
源码枚举SceneBounds520/317、总计1171/703；10个公共声明通过、默认heartbeat。
actual bounded positive-Haar least hull及拓扑/测度性质闭合，整体Scene1目标仍open。


## S1.314：chosen actual hull、scalar identity 与 fixed-moduli Haar 下界

`JT-SCENE1-LOCAL-TENSOR-CHOSEN-LEAST-HULL`，路径
`Act1Scene1/LocalCompletionTensorChosenHull.lean`，从S1.313实际exists选择unit
multiplier，leastHull定义为actual principalRegion。证明region包含、compact/open/
positive finite Haar、对任何principal候选最小、region单调性、所有least principal
表示给同一Set，principal region为fixed point。该选择不输入hull certificate。

`JT-SCENE1-LOCAL-TENSOR-SCALAR-HULL-VOLUME`，路径
`Act1Scene1/LocalCompletionTensorScalarHullVolume.lean`，证明scalarNormalization
恰为pure(z)乘normalization，且actual scalar lattice compact/positive Haar。
任何principal region包含该scalar lattice时，也包含其normalization饱和区域；
因此chosen leastHull(scalarLattice)=scalarNormalization。实际normalization Haar
degree-volume的单调性与S1.309身份推出：scalar lattice⊆bounded正Haar U时，
old scalar degreeVolume≤new normalization degreeVolume(leastHull U)。

`JT-SCENE1-INITIAL-THETA-FIXED-MODULI-LEAST-HULL-VOLUME`，路径
`Act1Scene1/IutInitialThetaFixedModuliHullVolume.lean`，直接用实际chosen hull的
normalization degree Haar再取moduli localDeg幂定义volume；ordinary actual log
lattice⊆U时，派生canonical relative root factor^card≤volume。hU/hpos/hregion
仍是显式几何条件，未识别paper theta U或不同untilts。

三个叶子为原创proof terms，无新参考代码复制/import；来源比较Joshi III
le:volume-lemma3 3576–3583和contained-region 3624–3631。Prologue-R5→R5，derive，
owner Scene1；新增Core假设0、退休字段0、迁移0，前置信任不增加。闭合chosen
hull法律/scalar hull exact身份和actual local量化消费者。paper C_p norm/weighted
volume、theta/untilt/Bloch–Kato/V_p^oss/L'、global grouping/transfer、source sign
freeze与joint真实模型仍open。完整类型和资源见log4 S1-BND-314。


2026-10-14 10:46:00 CST最终熱构建9328/9328通过，耗时3:09.71，进程组采样
峰值25890028KiB（约24.691GiB），最大同时Lean workers=3，无Mathlib重编。
首轮失败与两轮总耗时293.586s见log4；337条公理报告仅含标准允许集合。
源码枚举SceneBounds540/337、总计1191/723；20个公共声明通过、默认heartbeat。
chosen hull/scalar identity及actual local relative-volume下界闭合，整体Scene1仍open。


## S1.315：exact actual VBad chosen hull Haar 全局下界

`JT-SCENE1-LOCAL-TENSOR-HULL-NORMALIZATION-BOUNDS`，路径
`Act1Scene1/LocalCompletionTensorHullNormalizationBounds.lean`，证明normalization
中的区域normalizationDegreeVolume≤1，U⊆normalization时leastHull(U)也包含其中；
leastHull的normalizationDegreeVolume严格正由actual positive finite Haar派生。

`JT-SCENE1-INITIAL-THETA-VBAD-CHOSEN-HULL-VOLUME`，路径
`Act1Scene1/IutInitialThetaVBadChosenHullVolume.lean`，从actual D、每VBad处上的
合法Fin n over-place tuple及actual bounded positive-Haar U构造local chosen hull，
将local Haar dimension根的localDeg幂按exact VBad取乘积，再按moduli global
finrank根归一化，直接定义global volume。ordinary actual log lattice包含于U时，
逐项消费S1.314的relative factor^card下界，得到canonical normalized VBad root
product^n≤volume；正性独立派生。U位于normalization时得volume≤1，然后由
exact VBad root negative-log身份得absLog(volume)≤n*reference absLogQ及n>0时
negative-average≥reference lhs。未以q-pilot/自由thetaVolume字段定义volume。

本单元原创，无参考复制/import；来源比较Joshi III multiplicative adelic volume
3624–3631与3634–3645 sign讨论。Prologue-R5→R5，derive，owner Scene1；新增Core
假设0、退休字段0、迁移0，前置信任不增加。actual同处集/同重数/同degree的局部
hull到全局q-pilot数值传递闭合。paper theta loci/U/τ_j、different untilts/Bloch–Kato、
paper C_p norm/weighted-volume/V_p^oss/L'身份、source sign freeze/joint真实模型及
完整Corollary3.12仍open；完整公共类型和资源见log4 S1-BND-315。


2026-10-14 11:07:36 CST最终热构建9330/9330通过，默认heartbeat；耗时2:42.94，进程组采样
峰值25826624KiB（约24.630GiB），最大同时Lean workers=3，无Mathlib重编。
347条公理报告仅含标准允许集合；十个新增公共声明通过。源码枚举SceneBounds
550/347、全家族1201/733。四轮总monitor耗时533.584s及失败原因见log4 S1.315。
actual VBad local hull→global relative-degree q-pilot消费者闭合，整体Scene1仍open。


## S1.316：actual tensor hull/order conversion criterion

`JT-SCENE1-LOCAL-TENSOR-HULL-ORDER-AUDIT`，路径
`Act1Scene1/LocalCompletionTensorHullOrderAudit.lean`，对actual nonzero scalar
lattice证明其principal normalization hull与最小Z_p-submodule integralHull
相等当且仅当tensor unit order=normalization；该order身份也恰等价于actual
normalizationMass=1。实际Haar的scalar normalization扩张系数为normalizationMass。
证明使用scale map injectivity、scalar hull exact身份及open nonempty difference
的正Haar，不以equal mass推出任意measurable集合相等。

`JT-SCENE1-INITIAL-THETA-FIXED-MODULI-HULL-ORDER-AUDIT`，路径
`Act1Scene1/IutInitialThetaFixedModuliHullOrderAudit.lean`，从actual D和共同moduli
place上合法over-place tuple派生ordinary log region的compact/positive normalization
Haar，实际chosen regionHull无需自由boundedness或measure字段。将两hull等价
判据接到该actual region；normalizationMass≠1时两种hull不同。

来源为Joshi III pr:convexes-and-hulls 3597–3609及principal component hull
3568–3574、Haar normalization3495–3498。原创无参考代码复制/import。Prologue
R5→R5，derive，owner Scene1；新增Core假设0、退休0、迁移0，前置信任不增加。
本结果为exact criterion；尚未构造proper-order具体packet/特定D，不声称完整
论文反例，也不识别ordinary log/BK/theta/untilt。不得据此无条件把此前integralHull消费者视为principal normalization hull；
order身份判据只针对scalar lattice，其他collated region需分别审查。其余paper norm/carrier/volume、
source sign/target freeze和joint真实模型仍open。完整类型与资源见log4 S1-BND-316。


2026-10-14 11:27:24 CST最终里程碑热构建9331/9331通过，耗时1:38.45，进程组采样峰值
17632192KiB（约16.815GiB），同时Lean workers峰值2。
先前check家族9308/9308通过，耗时3:08.96，峰值9386392KiB（约8.952GiB）。
十二个公共声明通过；359条公理报告仅标准允许集合。失败及三轮monitor总耗时
368.061s见log4 S1.316；无Mathlib重编。条件性scalar-order转换义务
显式登记，未当作实际paper反例；整体Scene1仍open。


## S1.317：normalization-stable generated hull and actual log collation

`JT-SCENE1-LOCAL-TENSOR-ATTAINED-RESIDUE-MAXIMUM`，路径
`Act1Scene1/LocalCompletionTensorResidueMaximum.lean`，由actual discrete
spectral value与uniform boundedness证明bounded tensor set的每个非零coordinate
范数最大值达到；无需compactness或外给extremum certificate。

`JT-SCENE1-LOCAL-TENSOR-NORMALIZATION-MODULE-HULL`，路径
`Act1Scene1/LocalCompletionTensorNormalizationHull.lean`，normalizationHull
定义为actual normalization环上的Submodule.span。位于normalization的residue idempotents与
逐coordinate最大值重组unit multiplier，证明它等于bounded positive-Haar U
的actual least principal hull。integralHull预处理不改变此normalization span；
未假定unit order=normalization，也未沿用“都是Z_p module所以相等”的推断。

`JT-SCENE1-INITIAL-THETA-COLLATED-NORMALIZATION-HULL`，路径
`Act1Scene1/IutInitialThetaFixedModuliCollatedNormalizationHull.lean`，从actual D、
共同moduli v的合法tuple及C的union构造normalization-module collation。
ordinary log scalar generators的coverage派生integral span正Haar，C位于
normalization派生其boundedness；构造的region等于该integral span的true
principal hull，故compact/positive finite Haar；得到canonical relativeFactor^card
的corrected normalization volume下界及unit上界。coverage和unit containment
仍为显式几何来源义务，不构造真实theta/BK/different-untilt证书。

来源为Joshi III3568–3574、3597–3609、3624–3631与本工程已证实际代数/谱范数/Haar。
本单元原创，无新参考代码复制/import。Prologue-R5→R5，derive，owner Scene1；
新增Core假设0、退休字段0、迁移0，前置信任不增加。S1.316 scalar hull合并的
order身份判据保留，本路径通过normalization saturation解决，无需增加order
identity假设。paper norm/处集/weighted thetaVolume、source sign/target freeze、
joint真实模型及最终Corollary3.12仍open。完整类型与资源见log4 S1-BND-317。


2026-10-14 11:54:05 CST显式里程碑热构建9334/9334通过，耗时1:44.95，组RSS采样峰值
17650708KiB（约16.833GiB），同时Lean workers峰值2。
先前check家族9311/9311通过，耗时2:41.55，峰值9390424KiB（约
8.955GiB）；23公共声明覆盖，382条公理报告仅标准允许集合。
四轮总monitor耗时523.607s与失败原因见log4 S1.317；无Mathlib重编。
actual normalization-stable collation→principal hull→local量化桥闭合，整体Scene1仍open。


## S1.318：original collation principal hull and actual global Haar volume

`JT-SCENE1-INITIAL-THETA-COLLATED-PRINCIPAL-HULL-LAWS`，路径
`Act1Scene1/IutInitialThetaCollatedPrincipalHullLaws.lean`，证明original C union
包含于normalization-module region，且任意principal region包含original union时
也包含该region；generator coverage/hunit从S1.317派生其unit multiplier principal
形状，因此它是original union的least principal hull，而非仅integral span的hull。
不要求original union positive Haar，不引入order=normalization证书。

`JT-SCENE1-INITIAL-THETA-VBAD-COLLATED-NORMALIZATION-VOLUME`，路径
`Act1Scene1/IutInitialThetaVBadCollatedNormalizationVolume.lean`，从actual D、
每exact VBad处的合法Fin n tuple及actual collation C构造per-place region。
volume为actual normalization Haar dimension root的localDeg幂在exact VBad上的
乘积，再取moduli global finrank根。original-union least-principal形状派生
每处positive finite Haar，hgen/hunit接入canonical relativeFactor^n下界；从同处集
的canonical normalized VBad root product得到global positivity/lower/upper及
absLog≤n*reference absLogQ，n>0时negative-average≥reference lhs。

来源为Joshi III3568–3574、3624–3631与本工程actual normalization span、VBad
q-pilot accounting。原创无新参考代码复制/import。Prologue-R5→R5，derive，
owner Scene1；新增Core假设0、退休字段0、迁移0，前置信任不增加。hgen/hunit
仍为explicit geometric输入，非真实theta/BK/τ_j/untilt来源证明。本global体积
使用explicit relative-degree数值修正，不宣称paper weighted thetaVolume或
V_p^oss/L'身份；source sign/target freeze、joint真实模型及完整3.12仍open。
完整类型与资源见log4 S1-BND-318。


2026-10-14 12:10:08 CST显式里程碑热构建9336/9336通过，耗时1:40.73，组RSS采样峰值
17628672KiB（约16.812GiB），同时Lean workers峰值2。
先前check家族9313/9313通过，耗时2:45.44、组RSS峰值9372536KiB（约
8.938GiB）。十二个公共声明覆盖，394条公理报告仅标准允许集合；
源码枚举SceneBounds597/394、全家族1248/780。三轮monitor总耗时
446.484s与失败原因见log4 S1.318，无Mathlib重编。
original collation→principal hull→actual VBad global量化桥闭合；共同moduli tuple
不识别mixed-moduli prime-fiber tensor grouping，整体Scene1仍open。


## S1.319：constructed ordinary-log collation and exact global hull calibration

`JT-SCENE1-LOCAL-TENSOR-ORDINARY-LOG-GENERATORS`，路径
`Act1Scene1/LocalCompletionTensorLogGenerators.lean`，定义actual log-image pure
tensor generators：scalar z_i乘normalizedLog(b_i)，所有b_i norm≤1。由actual
p-adic log小球满射证明恰等scalarGenerators，integral span等scalarLattice，
normalization span等scalarNormalization；integral scalars保证generators位于unitLattice。
无外给surjectivity、hull或measure certificate。

`JT-SCENE1-INITIAL-THETA-VBAD-LOG-GENERATED-HULL`，路径
`Act1Scene1/IutInitialThetaVBadLogGeneratedHull.lean`，actual D/合法共同moduli tuple
的canonical q-root ordinary log scalars代入上述构造，C为Unit-indexed具体log-image
集合。generator coverage和normalization containment均派生，而非输入。其actual
collated principal hull逐处等scalarNormalization，actual Haar global volume精确
等normalized VBad relative rootProduct^n；派生positive/unit bound、negative log与
abs log=n*reference absLogQ，n>0时negative-average精确等reference lhs。
volume先由actual Haar定义再计算，未以q-pilot定义。

来源比较Joshi III3474–3478 multiplicative log-shell图、3568–3574 hull及3624–3631
volume。原创无新参考代码复制/import。Prologue-R5→R5，derive，owner Scene1；
本ordinary-log实例消除外给hgen/hunit两certificate，新增Core假设0、退休Core字段0、
迁移0，前置信任不增加。本构造不是真实different-untilt/Bloch–Kato/theta来源模型；
paper norm/carrier/weighted-volume、mixed-moduli grouping、source sign/target freeze
和joint真实Scene1模型仍open。完整公共类型与资源见log4 S1-BND-319。


2026-10-14 12:23:28 CST里程碑热构建9338/9338通过，耗时1:41.35，组RSS采样峰值
17628312KiB（约16.812GiB），同时Lean workers峰值2。
check家族9315/9315首轮成功，耗时3:09.39、峰值9382676KiB（约
8.948GiB）。17公共声明覆盖，411条公理报告仅标准允许集合；
源码枚举SceneBounds614/411、全家族1265/797。两轮monitor总耗时
290.905s见log4 S1.319，无失败或Mathlib重编。
actual ordinary-log collation校准模型闭合，真实paper theta/BK/untilt模型仍open。


## S1.320：selected unweighted root estimate from actual hull comparison

`JT-SCENE1-INITIAL-THETA-VBAD-PAPER-ROOT-PRODUCT-BOUND`，路径
`Act1Scene1/IutInitialThetaVBadPaperRootProductBound.lean`，消费actual D的strict
representative ramification gap及两侧negative-log身份，证明actual selected paper
rootProduct严格小于canonical normalized VBad relative rootProduct；n>0的幂比较。
严格性由actual D.global.bad_nonempty及q-root ramification派生，无extra证书。

`JT-SCENE1-INITIAL-THETA-VBAD-HULL-PAPER-BOUND`，路径
`Act1Scene1/IutInitialThetaVBadHullPaperBound.lean`，把S1.318 actual collation hull
下界传到selected unweighted paper product^n（严格下界）及negative-average
大于-selected positive paper sum、等价地大于selected signed log sum。后者是
negative-log约定下的数值形状，不是S1.305所排除的literal minus-log RHS。
S1.319 ordinary-log model的negative-average与signed log sum之差精确为
selected paper sum-reference absLogQ，且严格为正。

来源为Joshi III3617–3631乘积估计、3634–3645 sign讨论和本工程actual
representative ramification/negative-log/Haar定理。原创无新参考代码复制/import。
Prologue-R5→R5，derive，owner Scene1；新增Core假设0、退休字段0、迁移0，
前置信任不增加。归一化非等式不阻止one-sided estimate；不虚构去权等式。
actual selected carrier不识别paper V_p^oss/L'；paper norm/weighted thetaVolume、
真实theta/BK/untilt、mixed-moduli grouping、source sign/target freeze及joint
真实Scene1模型仍open。完整公共类型与资源见log4 S1-BND-320。


2026-10-14 12:37:52 CST里程碑热构建9340/9340通过，耗时1:45.89，组RSS采样峰值
17583492KiB（约16.769GiB），同时Lean workers峰值2。
check家族9318/9318首轮成功，耗时3:29.45、峰值9369468KiB（约
8.935GiB）。七公共定理覆盖，418条公理报告仅标准允许集合；
源码枚举SceneBounds621/418、全家族1272/804。两轮monitor总耗时
315.979s见log4 S1.320，无失败或Mathlib重编。
单向selected paper lower-estimate桥闭合，paper身份/source符号/整体Scene1仍open。


## S1.321：actual weighted log-measure transfer and old contract assembly audit

`JT-SCENE1-INITIAL-THETA-VBAD-ROOT-PRODUCT-CONTRACTING`，路径
`Act1Scene1/IutInitialThetaVBadRootProductContracting.lean`，由actual D.global.bad_nonempty
及逐处relative root factor∈(0,1)推出raw/normalized VBad product<1，再由精确
negative-log身份推出reference absLogQ>0，无外给非空或正性certificate。

`JT-SCENE1-INITIAL-THETA-VBAD-HULL-LOG-MEASURE-TRANSFER`，路径
`Act1Scene1/IutInitialThetaVBadHullLogTransfer.lean`，packetLogWeight实际定义为
placeWeight(v)/tensor finrank，其中placeWeight=localDeg/global finrank；它不是
inertDeg/global finrank的qPilotWeight。local packetLogVolume=log(actual
normalization Haar(region).toReal)。从positive finite measure与global Haar product
证明log(global volume)=ΣpacketLogWeight*packetLogVolume，权重严格正、local log≤0，
因此总log≤0。未假设或输入transfer身份，也未宣称paper weighted-volume identity。

`JT-SCENE1-INITIAL-THETA-ACTUAL-HULL-TRANSFER-AUDIT`，路径
`Act1Scene1/IutInitialThetaActualHullTransferAudit.lean`，ordinary-log构造模型在n>0
时actual logVolume<0；当前Scene1 logVolume≥0故二者不同。即使只接收packet/hull
weights非负及link.logVolume=actual logMeasure，也不存在当前VolumeTransfer。
排除不依赖thetaBase norm身份；源于旧transfer漏去local log-measure的当前表达式。

来源比较Joshi III3495–3557 Haar/log weighted products及3634–3645 signs。原创
无新参考代码复制/import。Prologue-R5→R5，derive，owner Scene1；新增Core假设0、
退休字段0、迁移0，前置信任不增加。保留旧API，未反转符号或取reciprocal；
source驱动的Core transfer修订和真实theta/BK/untilt、paper norm/carrier/weighted
volume、mixed-moduli grouping及目标冻结仍open。完整类型与资源见log4 S1-BND-321。


2026-10-14 13:53:52 CST最终里程碑9343/9343通过，耗时1:45.95，组RSS采样峰值
17635932KiB（约16.819GiB），同时Lean workers峰值2。
check家族9321/9321通过，耗时3:26.78、峰值9386384KiB（约
8.952GiB）。十三公共声明覆盖；431条公理报告仅标准允许集合。
源码枚举SceneBounds634/431、全家族1285/817。十轮monitor总耗时1250.743s，
八次失败及profiler定位见log4 S1.321；无Mathlib重编。generic计算def边界解决
actual Haar深展开；数学定义不变。actual weighted log-transfer和旧Core身份排除
闭合，source驱动transfer修订/整体Scene1仍open。


## S1.322：actual negative-log cost and legacy normalization consumer

`JT-SCENE1-INITIAL-THETA-VBAD-HULL-NEGATIVE-LOG-COST`，路径
`Act1Scene1/IutInitialThetaVBadHullLogCost.lean`，定义cost=-log(actual global hull
Haar volume)，localCost=packetLogWeight*(-packetLogVolume)，证明finite transfer、
local/global非负、volume=exp(-cost)及cost≤n*selectedPaperSum。ordinary-log模型
cost=n*reference absLogQ，n>0严格正。定义直接来自actual Haar，无自由cost字段。

`JT-SCENE1-INITIAL-THETA-ACTUAL-HULL-COST-BRIDGE`，路径
`Act1Scene1/IutInitialThetaActualHullCostBridge.lean`，旧exp(-link.logVolume)
normalization及thetaVolume=actual hull volume推出link.logVolume=actual cost，
反向由cost/volume身份构造normalization。显式length、cost及qLogSum=actual selected
paperSum身份下，actual cost上界构造Corollary312TransferLogBound，再由旧消费者
推导multiplicative lower bound；不再输入target-equivalent transfer inequality。

来源比较Joshi III3495–3557、3634–3645及本工程已证Haar log transfer/旧normalization。
原创无新参考代码复制/import。Prologue-R5→R5，derive，owner Scene1；新增Core假设0、
退休Core字段0、迁移0，前置信任不增加。本桥外给TransferLogBound字段1改由proof
派生；原旧API保留。S1.321 signed-logVolume身份排除仍有效，不排除经来源审查的
negative-log cost身份路径。旧Scene1及cost/length/qSum共同满足模型仍open；本结果
不自动将Core packetWeight等同actual degree weights。真实theta/BK/untilt、paper
norm/carrier/weighted-volume、mixed-moduli grouping及source sign/target freeze仍open。
完整类型与资源见log4 S1-BND-322。


2026-10-14 14:18:14 CST最终里程碑9345/9345通过，耗时1:40.86，组RSS采样峰值
17606568KiB（约16.791GiB），同时Lean workers峰值2。
check家族9323/9323首轮通过，耗时3:25.24、峰值9368424KiB（约
8.934GiB）。十三公共声明覆盖，444条公理报告仅标准允许集合；
源码枚举SceneBounds647/444、全家族1298/830，两轮monitor总耗时306.605s见
log4 S1.322，无失败或Mathlib重编。实际cost与legacy normalization/transfer的
条件桥闭合，真实联合模型及整体Scene1仍open。


## S1.323：exact VBad selected carrier and same-support hull accounting

`JT-SCENE1-INITIAL-THETA-VBAD-SELECTED-PAPER-ACCOUNTING`，路径
`Act1Scene1/IutInitialThetaVBadSelectedPaperAccounting.lean`，sourceAt为actual
ModuliSelectedSourceEquiv在VBad上的restriction；定义selectedFinset为其finite image，
证明sourceAt injective/liesOver、sourceEquiv bijection、card精确相同及包含于完整
odd-support selected carrier。paperTerm=-log(actualPaperRootNorm(sourceAt v))、paperSum
和rootProduct在恰VBad选定处集上计算，证明negative-log product身份。reference
absLogQ恰为同VBad支撑上representativeCoefficient*paperTerm之和；每coef<1、term>0
及D.global.bad_nonempty推出reference<paperSum，故rootProduct<normalizedVBad product。

`JT-SCENE1-INITIAL-THETA-VBAD-SELECTED-HULL-BOUND`，路径
`Act1Scene1/IutInitialThetaVBadSelectedHullBound.lean`，连接actual collation principal
hull，n>0时same-support selected rootProduct^n<actual volume、negative-average>
-same-support paperSum及cost<n*same-support paperSum，不使用较大odd-support和。

来源Joshi III1028–1055 section/locus、3617–3631 product估计及本工程actual
VBad/moduli/selected/ramification/Haar定理。原创无新参考代码复制/import。
Prologue-R5→R5，derive，owner Scene1；新增Core假设0、退休字段0、迁移0，
前置信任不增加。paper完整odd semistable section locus可能大于actual VBad
restriction，未假定其相等；本结果关闭restriction内部重数及q-term会计，不能
勾选完整paper V_p^oss/L' gate。真实theta/BK/untilt、paper norm/weighted-volume、
mixed-moduli grouping、source sign/target freeze及joint真实模型仍open。
完整类型与资源见log4 S1-BND-323。


2026-10-14 14:39:09 CST最终里程碑9347/9347通过，耗时1:39.64，组RSS采样峰值
17640304KiB（约16.823GiB），同时Lean workers峰值2。
check家族9325/9325通过，耗时3:23.92、峰值9376128KiB（约
8.942GiB）。21公共声明覆盖，465条公理报告仅标准允许集合；
源码枚举SceneBounds668/465、全家族1319/851。三轮monitor总耗时401.178s与
首轮subtype错误见log4 S1.323，无Mathlib重编。同VBad选定carrier的精确accounting
及hull量化桥闭合，完整paper carrier/整体Scene1仍open。


## S1.324：exact omitted selected q-log contribution and coverage criterion

`JT-SCENE1-INITIAL-THETA-VBAD-SELECTED-SUPPORT-DEFECT`，路径
`Act1Scene1/IutInitialThetaVBadSelectedSupportDefect.lean`。fullSelectedFinset是actual
完整odd moduli support经selected source equivalence的image，membership恰等已有
完整selected q-root source set。restricted selectedFinset包含于它；两finite carrier
相等当且仅当actual VBad moduli finset等于完整odd moduli support，使用injection/card
证明，不接收coverage。omittedPaperSum为full minus restricted finite sdiff上的
actual corrected q-root negative-log term之和；full paperSum=restricted paperSum+
omittedPaperSum，每项严格正，故omitted=0 iff coverage。完整/限制的paperSum及
rootProduct相等各当且仅当coverage；缺处条件下sum严格不等。

来源Joshi III1028–1055完整section odd semistable locus及3617–3631有限q乘积，
与本工程actual selected source/card/negative-log/Haar accounting。原创无参考代码
复制/import。Prologue-R5→R5，derive，owner Scene1；新增Core假设0、退休字段0、
迁移0，前置信任不增加。此为coverage必要充分条件，未构造缺处具体D，也未
证明任意actual VBad都完整；不勾选完整paper carrier身份gate。真实theta/BK/untilt、
paper norm/weighted-volume、mixed-moduli grouping、source sign/target freeze和
joint模型仍open。完整类型与资源见log4 S1-BND-324。


2026-10-14 15:01:44 CST最终里程碑9348/9348通过，耗时1:39.28，组RSS采样峰值
17514192KiB（约16.703GiB），同时Lean workers峰值2。
check家族9326/9326通过，耗时2:34.92、峰值9374596KiB（约
8.940GiB）。15公共声明覆盖，480条公理报告仅标准允许集合；
源码枚举SceneBounds683/480、全家族1334/866。三轮monitor总耗时359.799s及
首轮sum_coe_sort错误见log4 S1.324，无Mathlib重编。coverage/遗漏量判据闭合，
actual覆盖证明/完整paper来源身份及整体Scene1仍open。


## S1.325：complete initial-theta restriction and conditional missing-support model

`JT-SCENE1-INITIAL-THETA-RESTRICT-BAD-PLACES`，路径
`Act1Scene1/IutInitialThetaRestrictBadPlaces.lean`。从actual D和nonempty W⊆D.VBad
重建完整InitialThetaData：global、prime的residueChar/q-order/local Tate条件、
TateFamily及Galois laws、orbicurve/covers/epsilon、valuation section和local theta
conditions逐项限制。F/Fbar/E、torsionBasis/representation、section及global covers
保留。restriction不是较弱替代carrier，输出完整InitialThetaData；证明VBad/rep/
section投影身份。原创重构已移植的本地字段，没有新参考代码复制或外部import。

`JT-SCENE1-INITIAL-THETA-RESTRICTED-SUPPORT-WITNESS`，路径
`Act1Scene1/IutInitialThetaRestrictedSupportWitness.lean`。证明完整odd multiplicative
support在restriction下保持；给原D中两个不同bad places，构造singleton D'并证明
另一place仍在完整odd support却不在VBad。S1.324 criterion派生D' coverage失败、
omittedPaperSum>0，输出存在完整typed InitialThetaData有缺处和正遗漏的witness。

来源为actual InitialThetaData全字段及Joshi III1028–1055完整section odd semistable
locus比较。Prologue-R5→R5，derive，owner Scene1；新增Core假设0、退休字段0、
迁移0，前置信任不增加。结果为conditional countermodel construction：要求已有
actual D内two distinct bad places，未构造特定D，也不声称无条件counterexample。
完整paper identity必须来源补证或修订数据模型；真实theta/BK/untilt、norm/volume、
mixed-moduli grouping、source sign/target freeze及joint模型仍open。完整types、
restriction构造和资源见log4 S1-BND-325。


2026-10-14 15:45:25 CST最终里程碑9350/9350通过，耗时1:41.91，组RSS采样峰值
17636008KiB（约16.819GiB），同时Lean workers峰值2。
check家族9328/9328通过，耗时2:30.49、峰值9374420KiB（约
8.940GiB）。十公共声明覆盖，490条公理报告仅标准允许集合；
源码枚举SceneBounds693/490、全家族1344/876。五轮monitor总耗时607.892s与
前三轮字段/instance/subtype错误见log4 S1.325，无Mathlib重编。完整restriction及
conditional missing-support witness闭合，实际two-place模型存在性/整体Scene1仍open。


## S1.326：actual ordinary-log hull volume on complete odd support

`JT-SCENE1-INITIAL-THETA-FULL-SUPPORT-LOG-HULL`，路径
`Act1Scene1/IutInitialThetaFullSupportLogHull.lean`。从actual D和n，由完整moduli
selected source equivalence自动选择每处Fin n重复tuple及proved liesOver。ordinary
normalized-log image generators、normalization span及actual scalarNormalization
identity均构造/证明，region compact且位于normalization。global volume直接定义为
actual Haar dimension根的localDeg幂在完整odd support的乘积，再取moduli global
finrank根；证明volume=normalized full relativeRootProduct^n、positive/unit upper及
negative log/abs log=n*fullBaseSum。没有外给tuple、C、hgen/hunit或VBad coverage。

`JT-SCENE1-INITIAL-THETA-FULL-SUPPORT-HULL-PAPER-BOUND`，路径
`Act1Scene1/IutInitialThetaFullSupportHullPaperBound.lean`。由实际strict fullBaseSum<
full selected paperSum，得到full selected corrected rootProduct<normalized full
relativeRootProduct；n>0时其n次幂严格小于actual full-support Haar hull volume。
negative-average=-fullBaseSum> -full selected paperSum，无VBad=full coverage输入。

来源Joshi III1028–1055完整section odd semistable、3474–3631 log-shell/hull/volume
与本工程actual full root/Haar/accounting。原创无新参考代码复制/import。
Prologue-R5→R5，derive，owner Scene1；新增Core假设0、退休字段0、迁移0，前置
信任不增加。S1.324/325排除VBad任意缩小后的无证coverage；本路径直接构造完整
支撑而非添加coverage。重复ordinary completions/logs不识别不同untilts/BK/theta；
paper weighted-volume/norm、mixed-moduli grouping、source sign/target freeze及joint
真实模型仍open，不以该校准模型勾选整体gate。完整types/资源见log4 S1-BND-326。

验证：check家族9330/9330通过，715条输出逐名核对；收尾显式Axioms/Scene1
聚合9352/9352通过，512条公理报告只含propext、Classical.choice、Quot.sound。
22新公共声明全部审计。最终time-v wall=1:38.96、monitor99.046s，组RSS峰值
17633956KiB（约16.817GiB），time-v单进程最大8268512KiB；资源精确值以log4
S1.326表为准。三轮monitor总耗时408.756s，无Mathlib重编；整体Scene1仍open。


## S1.327：full-support paper-corrected relative weighted Haar blocks

`JT-SCENE1-INITIAL-THETA-FULL-SUPPORT-PAPER-WEIGHTED-VOLUME`，路径
`Act1Scene1/IutInitialThetaFullSupportPaperWeightedVolume.lean`。来源Joshi III
ss:weighted-vol/le:volume-lemma2/eq:weights（3520–3557）。以S1.326 actual
full-support normalization hull的local Haar degree volume为起点，按选定完成处
的inertDeg取根；完整odd moduli support上作乘积，不加global degree root。
证明local volume=corrected paper root norm^(n*inverse relative completion degree)，
并逐名构造实际finrank inverse weights∈(0,1]。完整selected root carrier经实际
equivalence重索引，推出完整unweighted selected product^n≤volume及
negative-average≥-selected paperSum。negative log精确=n*weightedPaperSum，
该和使用corrected paper norms和relative weights，未把它改称fullBaseSum。

volume定义于canonical fixed-moduli block presentation，未构造mixed-moduli
单一tensor上的presentation-independent weighted measure，未识别不同untilts、
Bloch-Kato/theta loci、论文L' carrier或最终thetaVolume。S1.293的mixed-moduli
raw-norm descent负面证据及S1.305的source sign问题继续保持；旧API声明不变。
原创，无新外部源码复制/import。Prologue-R5→R5，derive，owner Scene1；
新增Core假设0、退休字段0、迁移0，前置信任不增加。完整公共类型和资源见
log4 S1-BND-327；整体Scene1仍open。

验证：check家族9331/9331成功（735条输出逐名核对）；显式Axioms/Scene1
聚合9353/9353通过，532条公理报告仅含propext、Classical.choice、Quot.sound。
20新公共声明全部覆盖；最终time-v wall=1:39.88、monitor99.989s，
组RSS峰值17551020KiB（16.738GiB），time-v单进程最大8269424KiB。
三轮monitor总耗时362.343s，首次失败与修复见log4 S1.327；无Mathlib重编。


## S1.328：one standard-point tensor witness suffices for normalization hull volume

`JT-SCENE1-LOCAL-TENSOR-SINGLE-WITNESS-HULL`，路径
`Act1Scene1/LocalCompletionTensorWitnessHull.lean`。原创证明normalization span
of singleton {a}=principalRegion a，无unit或Haar输入；因而nonzero pure tensor
在任意U中即推出scalarNormalization⊆normalizationHull U。若U⊆normalization，
则hull open/compact且positive finite Haar，并给出scalar lattice degree-volume
下界。没有要求U包含全部scalarGenerators，也未把结论搬给Z_p integralHull。

`JT-SCENE1-INITIAL-THETA-FULL-SUPPORT-WITNESS-HULL`，路径
`Act1Scene1/IutInitialThetaFullSupportWitnessHull.lean`。actual D完整odd support上
canonical ordinary-log tensor的IsUnit由qroot非零派生。每处该单一witness属于
collation及collation⊆normalization即给出实际紧致positive-Haar hull。按S1.327
selected inertDeg修正局部Haar degree volume并取完整乘积，证明canonical block
volume≤collated hull volume≤1、selected paperRootProduct^n≤volume、
abs log≤n*weightedPaperSum和negative-average≥-完整selected paperSum。

来源Joshi III principal hull（3568–3574）、th:thetam-construction（3296–3346）
及form2证明（3624–3631）的standard-point tensor witness。原创，无新参考源码
复制/import。Prologue-R5→R5，derive，owner Scene1；新增Core假设0、退休字段0、
迁移0，前置信任不增加。新路径将全族generator coverage减为single witness
membership，旧API声明保持。真实BK/theta/different-untilt身份及witness成员、
mixed-moduli grouping、paper L'/thetaVolume/source sign/final target及joint
真实模型仍open；不以此条件性consumer误勾整体gate。完整类型/资源见log4 S1-BND-328。

联合模型补充：actual singletonCollation每处只包含constructed log tensor；
witness_mem_base_region及singletonCollation_laws自动给出hw/hunit，
singleton_region_eq_base和singleton_volume_eq_base精确回到S1.327模型。
体积计算在generic correctedVolume def中完成，actual caller复用，默认heartbeat。

验证：check家族9333/9333通过（762条输出逐名核对）；显式Axioms/Scene1
聚合9355/9355通过，559条公理报告仅含propext、Classical.choice、Quot.sound，
27新公共声明全部覆盖。最终time-v wall=1:41.84、monitor102.027s，
组RSS峰值17565116KiB（16.751GiB），time-v单进程最大8270444KiB。
五轮monitor总耗时671.589s，前三轮elaboration错误/修复详见log4 S1.328，
默认heartbeat，无Mathlib重编；singleton联合模型闭合，整体Scene1仍open。


## S1.329：literal p* ordinary principal-unit logarithm and the same actual hull

`JT-SCENE1-LOCAL-PSTAR-LOG`，路径`Act1Scene1/LocalPadicPaperLog.lean`。
来源Joshi III 3160–3175的p*=p（奇素数）/4（2处），3190–3226的
principal units与eq:bloch-kato-log-class、le:elem-lemma。构造ordinary
paperNormalizedLog=log(1+pStar*y)/pStar，证明pStar非零、norm(pStar)=norm(2p)、
主单位norm(u-1)<1且非零，以及integral y的log范数等y范数；不构造BK class。

`JT-SCENE1-LOCAL-TENSOR-EQUAL-NORM-HULL`，路径
`Act1Scene1/LocalCompletionTensorEqualNormHull.lean`。逐factor nonzero scalars
同范数给相同integral balls、相同scalarLattice及scalarNormalization。以本工程
actual closed balls、normalization span和principal hull证明，不假定标量值相等。

`JT-SCENE1-INITIAL-THETA-PSTAR-LOG-WITNESS-HULL`，路径
`Act1Scene1/IutInitialThetaPaperLogWitnessHull.lean`。actual D完整odd support上
构造1+pStar*qroot、ordinary logarithm除pStar及pure tensor witness；其singleton
normalization hull=原2p ordinary-log hull。normalization saturation保留任意
collation的region/volume，含p* witness即可派生旧witness在saturation中的成员，
复用S1.328完整corrected relative-weight volume与negative-average下界。
p* singletonCollation自动满足hw/hunit；真实BK/theta/different-untilt身份及
paper L'/thetaVolume、mixed-moduli grouping/descent、source sign/final target
和joint真实模型仍open。尤其norm/hull相等不表示两个log元素相等或BK comparison
已证明。三个叶子为原创，无新外部源码复制/import；不改旧高扇出LocalPadicLog或
Prologue/参考声明。Prologue-R5→R5，derive，owner Scene1；新增Core假设0、
退休字段0、迁移0，前置信任不增加。完整types及资源见log4 S1-BND-329。

验证：check家族9336/9336成功（792条输出逐名核对）；显式Axioms/Scene1
聚合9358/9358通过，589条公理报告仅含propext、Classical.choice、Quot.sound。
30新公共声明完整覆盖。最终time-v wall=1:42.86、monitor103.245s，
组RSS峰值17569024KiB（16.755GiB），time-v单进程最大8272128KiB。
四轮monitor总耗时485.402s，前两轮scope/rewrite错误及修复详见log4 S1.329；
默认heartbeat，无Mathlib重编，整体Scene1仍open。


## S1.330：compatible local principal-unit roots and algebraic Kummer cocycle

`JT-SCENE1-LOCAL-KUMMER-ROOT-TOWER`，路径
`Act1Scene1/LocalKummerRootTower.lean`。来源Joshi III 3190–3208的compatible
p^n roots与standard algebraic Kummer ratio。给定非零a和positive p，在
algebraically closed extension中递归选择每层p-th root，构造RootTower；证明
root_n^(p^n)=embedded a及root_n≠0。Galois ratio σ(root_n)/root_n位于
μ_(p^n)，层间p-power相容。构造cyclotomicTateGroup作为compatible roots-of-unity
sequences的实际subgroup，派生Galois MulDistribMulAction，并证明ratio map是
Mathlib groupCohomology.IsMulCocycle₁。该声明是underlying multiplicative group
上的代数cocycle，不是continuous cohomology或H^1_e class。

`JT-SCENE1-INITIAL-THETA-PRINCIPAL-UNIT-KUMMER`，路径
`Act1Scene1/IutInitialThetaPrincipalUnitKummer.lean`。每个actual full-support
source s的localField为torsion completion，closure为其AlgebraicClosure；
以S1.329 actual p* principal unit作为a，主单位非零由norm(u-1)<1证明，
p由residueChar_prime自动给出。root tower、power law及inverse-limit group-valued
Kummer cocycle全由D+s构造，无caller roots/cocycle证书，不用全局Fbar代替
局部closure。

IUT参考LocalConditions只登记continuous Kummer seam，没有可移植的BK构造；
本单元原创，无新外部源码复制/import。Prologue-R5→R5，derive，owner Scene1；
新增Core假设0、退休字段0、迁移0，前置信任不增加。continuity、continuous
cohomology/H^1_e、crystalline/Frobenius、BK/ordinary-log comparison、different
untilts及joint真实Scene1模型仍open。精确types及热构建资源见log4 S1-BND-330。

验证：check家族9338/9338成功（819条输出逐名核对）；显式Axioms/Scene1
聚合9360/9360通过，616条公理报告仅含propext、Classical.choice、Quot.sound，
27新公共审计名完整覆盖。最终time-v wall=1:47.15、monitor107.648s，
组RSS峰值17611104KiB（16.795GiB），time-v单进程最大8273316KiB。
四轮monitor总耗时433.594s；前两轮错误/修复见log4 S1.330。默认heartbeat，
无Mathlib重编；actual root tower/algebraic cocycle闭合，连续/BK身份仍open。


## S1.331：Krull-continuous Kummer cocycles in the inverse-limit topology

`JT-SCENE1-LOCAL-KUMMER-CONTINUITY`，路径
`Act1Scene1/LocalKummerContinuity.lean`。来源Joshi III 3190–3208的local
compatible roots/Kummer construction以及Krull topology。cyclotomicTateGroup
取discrete level units product的induced topology，派生topological-group
structure；不是把整个Tate group设成discrete。integral extension中evaluation
由open stabilizer证明locally constant，各层ratio/μ-character/unit-coordinate
locally constant，推出Kummer cocycle到inverse-limit subgroup连续。Galois作用
在离散level units上由open stabilizer连续，再通过product/subspace推出Tate
coefficient action联合连续。提供continuous-map cocycle及IsMulCocycle₁。

`JT-SCENE1-INITIAL-THETA-CONTINUOUS-KUMMER`，路径
`Act1Scene1/IutInitialThetaContinuousKummer.lean`。同一actual D/full-support
source s的S1.330 cocycle，每层locally constant、整体continuous，构造
continuousCocycle并消费其IsMulCocycle₁；无需caller topology/continuity证书。

原创，无新参考代码复制/import。不改旧API/Prologue或reference模块。
Prologue-R5→R5，derive，owner Scene1；新增Core假设0、退休字段0、迁移0，
前置信任不增加。continuous cohomology class及H^1_e/crystalline/Frobenius、
BK/ordinary-log comparison、different untilts/j² scaling、mixed-moduli
grouping、paper thetaVolume/source sign/final target及joint真实模型仍open。
完整types及热构建资源见log4 S1-BND-331。按本轮用户指令，推送后暂停。

验证：check家族9340/9340成功（835条输出逐名核对）；显式Axioms/Scene1
聚合9362/9362通过，632条公理报告仅含propext、Classical.choice、Quot.sound，
16新公共声明完整覆盖。最终time-v wall=1:42.45、monitor102.573s，
组RSS峰值17632976KiB（16.816GiB），time-v单进程最大8273760KiB。
三轮monitor总耗时365.802s，首次elaboration错误及修复见log4 S1.331。
默认heartbeat，无Mathlib重编；actual continuity闭合，continuous H^1_e/BK
身份仍open。本单元推送后按用户要求暂停。


## S1.332：Continuous Kummer classes independent of root choice

- `JT-SCENE1-LOCAL-KUMMER-COHOMOLOGY`：`Act1Scene1/LocalKummerCohomology.lean`。
  Joshi III 3190–3208；对Krull Galois群到inverse-limit Tate group的continuous
  cocycles按multiplicative coboundary取商，构造continuousH1及其class。
  两根塔S/R的逐层比值是兼容单位根系，给c_S/c_R的显式coboundary witness，
  从而同一nonzero a的根塔选择不影响类。
- `JT-SCENE1-INITIAL-THETA-KUMMER-CLASS`：`Act1Scene1/IutInitialThetaKummerClass.lean`。
  同一actual D/full-support s的p*-principal unit，消费前轮continuous cocycle，
  构造其continuousH1 class并证明对任意compatible root tower相等。

原创，无参考源码复制/import；derived，owner Scene1。Prologue-R5→R5；
新增Core假设0、退休/迁移0，前置信任不增加。商仅为continuous H1的集合载体，
未赋商拓扑或Z_p module；H^1_e/crystalline/Frobenius、BK/log comparison、
different untilts/j²及joint真实模型仍open。完整types及构建资源见log4 S1-BND-332。

用户2026-10-14解释决定：S1.305/qLogTerm显示式符号差异在收到作者邮件回复
前暂按笔误处理，不作为等待期间的工作阻塞项。保留原负面证据，保持既有
volume-derived目标符号；其他来源身份/目标冻结义务不据此关闭。


验证：Check.SceneBounds9342/9342通过，850条check逐名核对；显式Axioms/
Scene1聚合9364/9364成功，647条公理报告逐名核对，仅含propext、
Classical.choice、Quot.sound，15新公共声明check/axiom覆盖完整。
最终time-v wall=1:55.22、monitor115.690s，组RSS峰值17643620KiB
（16.826GiB），time-v单进程最大8274644KiB。三轮monitor合计388.509s，
首轮elaboration错误与修复见log4 S1.332；Mathlib未重编、默认heartbeat。
continuous H1类与根塔选择独立性已闭合，H^1_e/BK身份及完整Scene1仍open。


## S1.333：Kummer classes in standard continuous cohomology

- `JT-SCENE1-CONTINUOUS-H1-HOMOGENEOUS`：`Act1Scene1/ContinuousH1Homogeneous.lean`。
  Mathlib齐次continuous cochain complex的一次crossed-homomorphism bridge，
  F(g,h)=f(h)-f(g)，对角作用invariant且dF=0；continuous orbit给boundary，
  coboundary-related cocycles给相同standard class。
- `JT-SCENE1-LOCAL-KUMMER-MATHLIB-COHOMOLOGY`：`Act1Scene1/LocalKummerMathlibCohomology.lean`。
  actual inverse-limit Tate group的Additive continuous Z-linear TopRep，
  multiplicative cocycles转additive，并从explicit continuousH1商构造
  well-defined map到Mathlib continuousCohomology 1。
- `JT-SCENE1-INITIAL-THETA-MATHLIB-KUMMER`：`Act1Scene1/IutInitialThetaMathlibKummer.lean`。
  Joshi III 3190–3208，actual D/full-support s的p* principal unit standard
  cohomology class，直接代表身份及根塔选择独立性消费者。

冻结Mathlib已有ContCohomology.Basic/LowDegree；LowDegree目前仅有H0/invariants
识别，此处提供缺少的H1 bridge。原创，无参考源码复制/import；精确导入已缓存
模块，不重编Mathlib。Prologue-R5→R5，derive，owner Scene1，Core假设新增0、
退休/迁移0，前置信任不增加。standard ambient continuousH1不等于H^1_e，
crystalline/Frobenius/BK/log comparison及joint真实Scene1模型仍open。
完整types、动态边界及资源见log4 S1-BND-333。


验证：Check.SceneBounds9345/9345通过，871条check逐名核对；显式Axioms/
Scene1聚合9367/9367成功，668条公理报告逐名核对，仅含propext、
Classical.choice、Quot.sound。21新公共声明check/axiom完整覆盖。
最终time-v wall=1:49.04、monitor109.519s，组RSS峰值17537968KiB
（16.726GiB），time-v单进程最大8276048KiB。八轮monitor总耗时801.481s，
六轮elaboration错误及修复、全部资源见log4 S1.333；默认heartbeat，未重编
Mathlib。standard ambient class已构造，H^1_e/BK与完整Scene1仍open。


## S1.334：Multiplicative Kummer map and scalar laws for actual units

- `JT-SCENE1-CONTINUOUS-H1-LINEARITY`：`Act1Scene1/ContinuousH1Linearity.lean`。
  齐次cochain/cycle/class构造保加法，目标仍为Mathlib标准continuousH1。
- `JT-SCENE1-LOCAL-KUMMER-MULTIPLICATIVITY`：`Act1Scene1/LocalKummerMultiplicativity.lean`。
  Joshi III 3190–3208标准Kummer构造的乘法法律。根塔逐层相乘，cocycle相乘，
  standard classes相加；chosen roots不要求相乘，canonical root tower由已证
  choice independence对齐。得到Kˣ到Multiplicative(standard continuousH1)
  的实际群同态，unit powers对应natural scalar multiples。
- `JT-SCENE1-INITIAL-THETA-KUMMER-POWERS`：`Act1Scene1/IutInitialThetaKummerPowers.lean`。
  actual D/full-support s的p* principal unit由已证非零包装为unit，旧standard
  class等于Kummer同态值；任意n及literal p*次幂的class=标量倍数。

原创，无参考源码复制/import；精确生产叶子imports，无新Mathlib import。
Prologue-R5→R5，derive，owner Scene1；新增Core假设0、退休/迁移0，前置信任
不增加。此为乘幂/整数标量会计，不是p*可除性或BK/log comparison。
H^1_e/crystalline/Frobenius、rational coefficient comparison、different untilts、
paper thetaVolume及joint真实Scene1模型仍open。完整types及资源见log4 S1-BND-334。


验证：Check.SceneBounds9348/9348通过，887条check逐名核对；显式Axioms/
Scene1聚合9370/9370成功，684条公理报告逐名核对，仅含propext、
Classical.choice、Quot.sound。16新公共声明check/axiom完整覆盖。
最终time-v wall=1:53.63、monitor113.859s，组RSS峰值17649940KiB
（16.832GiB），time-v单进程最大8276960KiB；三轮monitor合计419.220s。
首轮引理namespace错误及修复、全部资源见log4 S1.334；默认heartbeat、
Mathlib未重编。乘法性/自然数幂标量关系闭合，H^1_e/BK及完整Scene1仍open。


## S1.335：Continuous Z_p Tate coefficients and actual Kummer classes

- `JT-SCENE1-LOCAL-KUMMER-PADIC-MODULE`：`Act1Scene1/LocalKummerPadicModule.lean`。
  Joshi III 3190–3208的Z_p(1)系数；r作用的第n层是x_n^val(toZModPow n r)。
  Mathlib residue compatibility给层相容，有限阶power periodicity给module法律；
  PadicInt valuation ball→p^n ideal证明residue locally constant，进而作用联合
  连续。底层Tate group及乘积子空间拓扑保留，natural scalar等于旧pow，
  Galois action与padic scalar commute。
- `JT-SCENE1-LOCAL-KUMMER-PADIC-COHOMOLOGY`：`Act1Scene1/LocalKummerPadicCohomology.lean`。
  Z_p-linear continuous Tate TopRep、同一cocycle的standard Z_p continuousH1
  class，按coboundary不变，旧explicit quotient well-defined映入Z_p版本。
- `JT-SCENE1-INITIAL-THETA-PADIC-KUMMER`：`Act1Scene1/IutInitialThetaPadicKummer.lean`。
  actual D/full-support s的p* principal-unit Z_p coefficient class，直接代表
  身份及根塔选择独立性；素数Fact由actual residueChar_prime派生。

原创，无参考源码复制/import；新增Mathlib精确RingHoms导入，仅读取缓存olean。
Prologue-R5→R5，derive，owner Scene1，Core假设新增0、退休/迁移0，前置信任
不增加。未给整数版本与Z_p版本的coefficient-change同构，未构造Q_p(1)、
H^1_e/crystalline/Frobenius/BK/log比较，joint真实Scene1模型仍open。
完整types、动态边界及资源见log4 S1-BND-335。


验证：Check.SceneBounds9351/9351一次通过，910条check逐名核对；显式
Axioms/Scene1聚合9373/9373成功，707条公理报告逐名核对，仅含propext、
Classical.choice、Quot.sound。23新公共声明check/axiom完整覆盖。
最终time-v wall=1:46.76、monitor107.032s，组RSS峰值17644184KiB
（16.827GiB），time-v单进程最大8278028KiB；两轮monitor合计330.460s，
无失败尝试。默认heartbeat、未重编Mathlib。continuous Z_p module及实际
Z_p ambient class已闭合；Q_p(1)/H^1_e/BK及完整Scene1仍open。资源见log4 S1.335。


## S1.336：Primitive compatible roots and a topological Tate basis

- `JT-SCENE1-LOCAL-KUMMER-PRIMITIVE-TOWER`：`Act1Scene1/LocalKummerPrimitiveTower.lean`。
  Joshi III 3190–3208 Z_p(1)结构。algebraically closed/CharZero Ω中选primitive
  p-root，再取其compatible p-power roots，得到第n层exact order p^n的实际
  Tate generator，caller不供应根或basis。
- `JT-SCENE1-LOCAL-KUMMER-TATE-BASIS`：`Act1Scene1/LocalKummerTateBasis.lean`。
  任意Tate sequence逐层写成该generator幂，primitive order给相容exponents，
  PadicInt.ofIntSeq给p-adic exponent；scalarMap injective/surjective。
  Z_p compact、Tate product-subspace Hausdorff，推出continuous linear equivalence。
- `JT-SCENE1-INITIAL-THETA-TATE-COORDINATES`：`Act1Scene1/IutInitialThetaTateCoordinates.lean`。
  actual D/full-support s的local closure使用同一真实topological Z_p basis；
  principal-unit cocycle的坐标连续并有重构等式，不是BK logarithm。

原创，无参考源码复制/import；精确Mathlib imports均仅读取匹配缓存。
Prologue-R5→R5，derive，owner Scene1，Core假设新增0、退休/迁移0，前置信任
不增加。该basis为拓扑正确Q_p(1)扩张提供前提；Q_p系数、H^1_e/BK/log比较、
different untilts及joint真实Scene1模型仍open。完整types及资源见log5 S1-BND-336。

验证：Check.SceneBounds9354/9354成功，936条check逐名匹配；显式
Axioms.SceneBounds/Scene1聚合9376/9376成功，733条公理报告逐名匹配，
仅含propext、Classical.choice、Quot.sound。26新公共声明check/axiom完整覆盖。
最终time-v wall=1:50.52、monitor110.800s，组RSS峰值17560568KiB
（16.747GiB），time-v单进程最大8279100KiB；含4次失败在内的
六次monitor合计708.411s，所有资源及修复明细见log5 S1.336。默认heartbeat、
Mathlib未重编；topological Z_p basis与actual坐标闭合，完整Scene1仍open。


## S1.337：Cyclotomic character and rational Kummer realization

- `JT-SCENE1-LOCAL-KUMMER-CYCLOTOMIC-CHARACTER`：`Act1Scene1/LocalKummerCyclotomicCharacter.lean`。
  从实际 Tate action 和 S1.336 连续基导出 ℤₚ 单位值特征，证明乘法、连续性和
  scalar action 公式，不接收外给 character。
- `JT-SCENE1-LOCAL-KUMMER-RATIONAL-COHOMOLOGY`：`Act1Scene1/LocalKummerRationalCohomology.lean`。
  通常拓扑 ℚₚ 上按该 character 作用；实际 Tate group 到此坐标模型的加法系数映射
  为单射、连续、ℤₚ 线性和 equivariant，其像 ℚₚ-span 为全体。将实际 continuous
  cocycle 推入标准 rational H¹，coboundary 不改变类。
- `JT-SCENE1-INITIAL-THETA-RATIONAL-KUMMER`：`Act1Scene1/IutInitialThetaRationalKummer.lean`。
  actual principal unit 的 rational cocycle 等于旧 integral 坐标的包含，标准 rational
  class 与兼容根塔选择无关。

来源：Joshi III 3190–3236，尤其 ℤₚ(1) 类和后续 ℚₚ(1) BK exponential 的系数转换。
原创连接证明，无参考源码复制/import；不增加 Mathlib imports 闭包以外的依赖。
本单元使用所构造基的坐标模型，未声明标准 ℤₚ H¹ 到 ℚₚ H¹ 的完整系数变换函子、
该函子的单射性、H¹ₑ/crystalline/Frobenius 身份或 BK/log 比较。
Prologue-R5→R5，derive，owner Scene1；新增 Core 假设/退休/转入/取出均 0。
边界记录见 log5 S1-BND-337；验证状态待构建。

验证：Check.SceneBounds9357/9357成功，970条check逐名匹配；显式
Axioms.SceneBounds/Scene1聚合9379/9379成功，767条公理报告逐名匹配，
仅含propext、Classical.choice、Quot.sound。34新增公开声明check/axiom全部覆盖。
standard cochain universe 由 ContinuousLinearEquiv.ulift 搬运同一 p-adic 表示，
不改变底层 ℚₚ 拓扑或新增数学假设。六次构建（四次失败）累计772.747秒，
组RSS峰值16.837GiB；明细见 Scene1进度总览 的 S1.337 变化卡。默认heartbeat
未改、Mathlib未重编；H¹ₑ/BK及完整Scene1仍open。


## S1.338：Standard semilinear H1 coefficient change

- `JT-SCENE1-CONTINUOUS-H1-SEMILINEAR`：`Act1Scene1/ContinuousH1Semilinear.lean`。
  不同标量环间的连续半线性等变映射逐点作用于标准齐次 cochains，证明保持
  closed cochains 与 boundaries，经实际 homology cokernel 下降为标准 H¹ 映射。
- `JT-SCENE1-LOCAL-KUMMER-COEFFICIENT-CHANGE`：`Act1Scene1/LocalKummerCoefficientChange.lean`。
  将已有 integral coefficient map 代入通用构造；证明与旧 explicit cocycle 商
  的有理类构造相容，并证明非零 ℤₚ scalar 消去的类有零 rational 像。
- `JT-SCENE1-INITIAL-THETA-COEFFICIENT-CHANGE`：`Act1Scene1/IutInitialThetaCoefficientChange.lean`。
  actual rationalClass 等于 actual standard padicClass 的系数变换。

Joshi III 3214–3236 的 integral/rational H¹ 比较所需连接；原创，不复制或导入
参考源码。仅精确导入已缓存 ContinuousLinearMap.Restrict；Mathlib 不改。
Prologue-R5→R5，derive，owner Scene1；Core 假设/退休/迁移增量均 0。
未声明 H¹ 系数映射单射、H¹ₑ/BK 身份或完整真实模型；边界见 log5 S1-BND-338。
验证状态待构建；进度和构建资源见 Scene1进度总览。

验证：Check.SceneBounds9360/9360成功，995条check逐名匹配；显式
Axioms.SceneBounds/Scene1聚合9382/9382成功，792条公理报告逐名匹配，
仅含propext、Classical.choice、Quot.sound。25新增公开声明check/axiom完整覆盖。
四次构建（两次失败）累计558.348秒，组RSS峰值16.828GiB；资源和修复明细
见 Scene1进度总览 的 S1.338 变化卡。默认heartbeat、Mathlib、依赖和工具链
未改。标准 H¹ 系数映射及 actual 类相容闭合；非零 torsion 的排除为条件性，
未构造 actual 无条件反例；H¹ₑ/BK与完整Scene1仍open。


## S1.339：Ordinary p-adic logarithm homomorphism and actual unit laws

- `JT-SCENE1-LOCAL-PADIC-LOG-HOMOMORPHISM`：`Act1Scene1/LocalPadicLogHomomorphism.lean`。
  逐段适配 `refer/iut/Iut/Concrete/LocalConstruct/PadicLog.lean` 的 Limit 段，
  binomial/Pochhammer/Tannery 推出已定义 ordinary log 的乘法、幂、逆和单位根消失。
  原提交 `bc1c6e6c7ac4bcf0c363b9b1bbe9b6d7bc35bf9c`，Git 作者 Christian Merten，
  文件作者与版权 The iut contributors；参考快照 `07cb1da58f6d428a670dbb5dd6093d428bcbcdd8`
  上该路径 diff 为空。复制前核查双方 Apache-2.0 LICENSE，保留通知与 provenance。
  不复制 `import Mathlib`、参考 namespace、surjectivity/compactness/volume；
  只导入匹配缓存的精确 Mathlib 模块。
- `JT-SCENE1-INITIAL-THETA-PRINCIPAL-UNIT-LOG-LAWS`：
  `Act1Scene1/IutInitialThetaPrincipalUnitLogLaws.lean`；原创 actual 消费者，
  证明 principal unit log 非零、幂/逆/归一化幂律及 unit 无限阶；定义原 rational
  class 的 (p*)⁻¹ 倍并证明标量还原，不声称论文 ξ 或 BK log 身份。

来源作用为 Joshi III 3190–3236 的 principal-unit/log 比较前提。Prologue-R5→R5，
derive，owner Scene1；Core 假设/退休/迁移增量均 0。实际 cohomology 类非零、
H¹ₑ/BK、different untilts、descent、paper volume 与联合模型仍 open。
验证状态待完整家族及收尾验收；边界见 log5 S1-BND-339，资源见进度总览。

验证：完整 Check.SceneBounds9362/9362成功，1016条check逐名匹配；
显式 Axioms.SceneBounds/Scene1聚合9384/9384成功，813条公理报告逐名匹配，
仅含propext、Classical.choice、Quot.sound。21新增公开声明check/axiom完整覆盖。
五次构建（两次失败、一次中间模块成功）累计624.594秒，组RSS峰值16.794GiB；
准确资源与修复明细见进度总览 S1.339。Mathlib/工具链/依赖及默认heartbeat
未改；ordinary log 与 actual 单位公式闭合，H¹ₑ/BK及完整Scene1仍open。


## S1.340：Standard H1 representatives and actual Kummer zero criteria

- `JT-SCENE1-CONTINUOUS-H1-RECOGNITION`：`Act1Scene1/ContinuousH1Recognition.lean`。
  从标准 homology 的 quotient/cokernel 提取代表；闭 cochain F 给 f(g)=F(1,g)，
  证明 crossed law、代表恢复、零性与 coboundary 方程的充要性。
- `JT-SCENE1-LOCAL-KUMMER-H1-EQUIVALENCE`：`Act1Scene1/LocalKummerH1Equivalence.lean`。
  已有 toPadicH1 对旧 continuous cocycle 商是集合双射；构造 padicH1Equiv。
  不声称旧商具有未构造的拓扑/模块，也不声称 integral→rational 映射单射。
- `JT-SCENE1-INITIAL-THETA-KUMMER-ZERO-CRITERIA`：
  `Act1Scene1/IutInitialThetaKummerZeroCriteria.lean`；实际 integral/rational 类
  为零当且仅当其实际 cocycle 满足相应 coboundary 方程。

Joshi III 3190–3236 的实际 Kummer 类比较所需识别；原创，无参考源码复制/import，
无新增 Mathlib 导入。Prologue-R5→R5，derive，owner Scene1，Core 假设/退休/迁移
增量均 0。类非零、H¹ₑ/BK 及完整真实模型仍 open；边界见 log5 S1-BND-340。
验证状态待构建，资源见 Scene1进度总览。

验证：Check.SceneBounds9365/9365成功，1037条check逐名匹配；显式
Axioms.SceneBounds/Scene1聚合9387/9387成功，834条公理报告逐名匹配，
仅含propext、Classical.choice、Quot.sound。21新增公开声明check/axiom完整覆盖。
三次构建（一次失败）累计436.873秒，组RSS峰值16.841GiB；资源明细见总览
S1.340。Mathlib/工具链/依赖和默认heartbeat未改；集合双射及零性判据闭合，
实际类非零、H¹ₑ/BK与完整Scene1仍open。


## S1.341：Integral Kummer vanishing and root descent

- `JT-SCENE1-LOCAL-KUMMER-ROOT-DESCENT`：`Act1Scene1/LocalKummerRootDescent.lean`。
  coboundary 修正根塔后每层实际 Galois 固定，InfiniteGalois 的 fixed-field
  theorem 给基域 preimage，algebraMap 单射证明其兼容。反向用基域 tower
  的零 cocycle 及 rootChange。标准 integral 类零 iff 基域 compatible tower。
- `JT-SCENE1-INITIAL-THETA-KUMMER-ROOT-DESCENT`：
  `Act1Scene1/IutInitialThetaKummerRootDescent.lean`；actual principal unit
  类零 iff actual local-field compatible tower，类零给每一有限层根；明确
  某层无根条件下给类非零。

Joshi III 3190–3208 的实际 Kummer 类及其非零证明所需的代数下降接口；原创，
无参考源码复制/import。精确导入 Mathlib.FieldTheory.Galois.Infinite，读取
匹配缓存。Prologue-R5→R5，derive，owner Scene1，Core 假设/退休/迁移增量 0。
尚未证明 actual 无根或类非零；rational 类及 H¹ₑ/BK/最终 volume 仍 open。
边界见 log5 S1-BND-341，验证待构建，资源见进度总览。

验证：Check.SceneBounds9367/9367成功，1048条check逐名匹配；显式
Axioms.SceneBounds/Scene1聚合9389/9389成功，845条公理报告逐名匹配，
仅含propext、Classical.choice、Quot.sound。11新增公开声明check/axiom完整覆盖。
三次构建（一次失败）累计431.577秒，组RSS峰值16.832GiB；明细见总览S1.341。
Mathlib/工具链/依赖和默认heartbeat未改；根塔下降判据闭合，actual 类非零
和完整Scene1仍open。


## S1.342：Discrete local-field root obstruction and integral Kummer nonvanishing

- `JT-SCENE1-LOCAL-PADIC-LOG-BOUNDED`：`Act1Scene1/LocalPadicLogBounded.lean`。
  选段移植 `refer/iut/Iut/Concrete/LocalConstruct/PadicLog.lean` 的 discrete norm gap
  和 uniform principal log bound；原提交 `bc1c6e6c7ac4bcf0c363b9b1bbe9b6d7bc35bf9c`，
  Git 作者 Christian Merten，文件作者/版权 The iut contributors，参考快照
  `07cb1da58f6d428a670dbb5dd6093d428bcbcdd8` 路径 diff 为空。核查双方
  Apache-2.0 LICENSE，保留通知与 provenance；不复制参考 import Mathlib/namespace。
- `JT-SCENE1-LOCAL-PADIC-KUMMER-NONVANISHING`：
  `Act1Scene1/LocalPadicKummerNonvanishing.lean`；原创 residue CharP/Frobenius
  推出 p-power roots principal；uniform log bound 排除非零 log 元素无限可除；
  消费 S1.341 根下降推出 integral Kummer 类非零。
- `JT-SCENE1-INITIAL-THETA-INTEGRAL-KUMMER-NONZERO`：
  `Act1Scene1/IutInitialThetaIntegralKummerNonzero.lean`；actual D+s 非零 log
  给某一层无根、无基域 compatible tower 和 actual standard padicClass 非零。

来源作用为 Joshi III 3190–3236 的实际 Kummer 类非退化性。Prologue-R5→R5，
derive，owner Scene1；Core 假设/退休/迁移增量 0。rational 类非零、H¹ₑ/BK
及完整真实模型仍 open，边界见 log5 S1-BND-342，验证待构建，资源见总览。

验证：Check.SceneBounds9370/9370一次成功，1057条check逐名匹配；显式
Axioms.SceneBounds/Scene1聚合9392/9392成功，854条公理报告逐名匹配，
仅含propext、Classical.choice、Quot.sound。9新增公开声明check/axiom完整覆盖。
两次构建均成功，累计332.967秒，组RSS峰值16.802GiB；跨午夜准确资源见
总览S1.342。Mathlib/工具链/依赖及默认heartbeat未改。actual integral 类非零
已闭合；rational 类非零、H¹ₑ/BK和完整Scene1仍open。


## S1.343：Actual rational Kummer nonvanishing

- `JT-SCENE1-LOCAL-KUMMER-TOWER-POWERS`：root tower power construction and cocycle power law.
- `JT-SCENE1-LOCAL-KUMMER-RATIONAL-DENOMINATOR`：rational coboundary denominator clearing gives an integral p-power class zero.
- `JT-SCENE1-LOCAL-PADIC-RATIONAL-KUMMER-NONVANISHING`：nonzero log contradiction proves rational class nonzero.
- `JT-SCENE1-INITIAL-THETA-RATIONAL-KUMMER-NONZERO`：actual D+s rational and normalized classes nonzero.

原创连接，无参考源码复制/import；消费 S1.342 integral nonzero and S1.338 coefficient map.
Prologue-R5→R5，derive，owner Scene1；Core 假设/退休/迁移增量 0。H¹ₑ/BK、
different untilts、descent、paper volume and joint model remain open.
边界见 log5 S1-BND-343；Checks.SceneBounds 1065/1065、Axioms.SceneBounds
862/862 逐名匹配，Scene1 聚合构建通过，公理仅含标准允许集合。actual
`rationalClass` 与 `normalizedRationalClass` 非零已验收；完整资源和失败尝试
见 `docs/Scene1进度总览.md`；数学提交 `8d73c998cd496701fb05a535cd70fea6dbe4c4ea`
已推送并与 `origin/main` 一致。

## S1.344：Actual integral Kummer non-torsion

- `JT-SCENE1-INITIAL-THETA-INTEGRAL-KUMMER-NONTORSION`：
  `Act1Scene1/IutInitialThetaIntegralKummerNonTorsion.lean`；actual
  `padicClass` 不被任意非零 `ℤₚ` 标量杀死。

消费 S1.338 coefficient-change 等式与 S1.343 rational nonvanishing；原创
actual 适配，无参考源码复制/import。Prologue-R5→R5，derive，owner Scene1；
Core 假设/退休/迁移增量均 0。全局 H¹ 无 torsion、H¹ₑ/BK、different
untilts、descent、paper volume 和联合模型仍 open。
验证：Checks.SceneBounds 1066/1066、Axioms.SceneBounds 863/863 逐名匹配，
Scene1 聚合构建通过，公理仅含标准允许集合；资源见 `docs/Scene1进度总览.md`。
数学提交 `2708a6543acb79eea1b56dbe714e75e18d420f57` 已推送并与 `origin/main` 一致。

## S1.345：Canonical actual source versus mass-one paper representative certificate

- `JT-SCENE1-INITIAL-THETA-PAPER-REPRESENTATIVE-NONEXISTENCE`：
  `Act1Scene1/IutInitialThetaPaperRepresentativeNonexistence.lean`；证明
  canonical actual source 与当前 mass-one paper representative/section-link
  accounting certificate 组合不相容。

消费 actual canonical q-pilot、selected q-root paper sum 和 S1.283 strict
ramification gap；原创冲突适配，无参考源码复制/import。Prologue-R5→R5，derive，
owner Scene1；Core 假设/退休/迁移增量均 0。该结果要求修订 carrier、weight 或
term 语义后再继续 G3，不构造 paper `L'` representatives，也不涉及 H¹ₑ/BK。
验证：Checks.SceneBounds 1067/1067、Axioms.SceneBounds 864/864 逐名匹配，
Scene1 聚合通过，公理仅含标准允许集合；资源见 `docs/Scene1进度总览.md`。
数学提交 `9a791ea33819691bf56dcf6f4569346c026c963f` 已推送并与 `origin/main` 一致。

## S1.347：Canonical actual q-pilot VBad strict bound

- `JT-SCENE1-INITIAL-THETA-CANONICAL-VBAD-SUBPROBABILITY-BOUND`：
  `Act1Scene1/IutInitialThetaCanonicalVBadSubprobabilityBound.lean`；证明
  canonical degree-one q-pilot `absLogQ` 严格小于 actual VBad selected paper sum。

消费 VBad coefficient-weighted accounting、strict gap 与 canonical reference
equality；原创适配，无参考源码复制/import。Prologue-R5→R5，derive，owner Scene1；
Core 假设/退休/迁移增量均 0。VBad carrier 与论文 `V_p^oss/L'`、thetaVolume 和
联合模型仍 open。验证：Checks.SceneBounds 1069/1069、Axioms.SceneBounds 866/866
逐名匹配，Scene1 聚合通过，公理仅含标准允许集合；资源见总览。
数学提交 `f3395ee456e1b7ea09cd7bbe44dbd2c85eff03df` 已推送并与 `origin/main` 一致。

## S1.348：Canonical actual VBad coefficient-weighted accounting

- `JT-SCENE1-INITIAL-THETA-CANONICAL-VBAD-COEFFICIENT-ACCOUNTING`：
  `Act1Scene1/IutInitialThetaCanonicalVBadCoefficientAccounting.lean`；证明
  canonical degree-one q-pilot `absLogQ` 等于 actual VBad selected paper terms
  的代表系数加权和。

消费 actual VBad weighted identity 与 canonical reference equality；原创适配，
无参考源码复制/import。Prologue-R5→R5，derive，owner Scene1；Core 假设/退休/
迁移增量均 0。mass-one certificate 已排除，paper carrier、thetaVolume 和联合
模型仍 open。验证：Checks.SceneBounds 1070/1070、Axioms.SceneBounds 867/867，
Scene1 聚合通过，公理仅含标准允许集合；资源见总览。
数学提交 `35bbfdd` 已推送并与 `origin/main` 一致。

## S1.349：Canonical actual VBad generated-hull cost bridge

- `JT-SCENE1-INITIAL-THETA-CANONICAL-VBAD-COST-BRIDGE`：
  `Act1Scene1/IutInitialThetaCanonicalVBadCostBridge.lean`；证明 canonical
  degree-one q-pilot `absLogQ = generated-hull cost / n`。

消费 canonical reference equality 与 actual VBad generated-hull ordinary cost
identity；原创适配，无参考源码复制/import。Prologue-R5→R5，derive，owner Scene1；
Core 假设/退休/迁移增量均 0。该 cost 不等同 Core `thetaVolume`，paper theta/BK/
untilt 联合模型仍 open。验证：Checks.SceneBounds 1071/1071、Axioms.SceneBounds
868/868，Scene1 聚合通过，公理仅含标准允许集合；资源见总览。
数学提交 `55de57b64568b1418a7be9371131fa6e81f8d006` 已推送并与 `origin/main` 一致。

## S1.350：Canonical actual q-pilot and thetaVolume exponential bridge

- `JT-SCENE1-INITIAL-THETA-CANONICAL-VBAD-THETAVOLUME-BRIDGE`：
  `Act1Scene1/IutInitialThetaCanonicalVBadThetaVolumeBridge.lean`；在显式
  `thetaVolume = actual VBad collated hull volume` 与 volume normalization 条件下，证明
  `thetaVolume = exp (-(n * canonicalAbsLogQ))`。

消费 S1.349 canonical generated-hull cost bridge 与 `Corollary312VolumeNormalization`；
原创条件桥，无参考源码复制/import。Prologue-R5→R5，derive，owner Scene1；Core
假设/退休/迁移增量均 0。actual hull volume 条件尚未从真实 paper theta/different-untilt
模型推出，不构造 BK 身份。验证：Checks.SceneBounds 1072/1072、Axioms.SceneBounds
869/869，Scene1 聚合通过，公理仅含标准允许集合；资源见 `docs/Scene1进度总览.md`。
数学提交 `79c41a1` 已推送并与 `origin/main` 一致。

## S1.351：Canonical actual q-pilot to qProduct lower-bound bridge

- `JT-SCENE1-INITIAL-THETA-CANONICAL-VBAD-QPRODUCT-BRIDGE`：
  `Act1Scene1/IutInitialThetaCanonicalVBadQProductBridge.lean`；在 actual hull
  volume、显式 q-family、`ellStar = n` 和 selected paper q-sum accounting 条件下，证明
  `exp (-(n * canonicalAbsLogQ)) ≥ qProduct`。

消费 S1.350 canonical thetaVolume exponential bridge、actual VBad collation 的
generator/normalization 条件和 q-family lower-bound consumer；原创适配，无参考源码
复制/import。Prologue-R5→R5，derive，owner Scene1；Core 假设/退休/迁移增量均 0。
不识别真实 paper theta/BK/different-untilt 身份。验证：Checks.SceneBounds 1073/1073、
Axioms.SceneBounds 870/870，Scene1 聚合通过，公理仅含标准允许集合；资源见
`docs/Scene1进度总览.md`。数学提交 `e599709` 已推送并与 `origin/main` 一致。

## S1.352：Conditional canonical Corollary 3.12 consumer

- `JT-SCENE1-INITIAL-THETA-CANONICAL-COR312-BRIDGE`：
  `Act1Scene1/IutInitialThetaCanonicalCorollary312Bridge.lean`；在显式 actual hull、
  q-family、q-sum、normalization 和 side conditions 下得到 `Corollary312`。

消费 S1.351 canonical qProduct lower-bound bridge 与既有 normalized q-family consumer；
原创条件装配，无参考源码复制/import。Prologue-R5→R5，derive，owner Scene1；Core
假设/退休/迁移增量均 0。真实 paper theta/BK/different-untilt 输入仍未构造。验证：
Checks.SceneBounds 1074/1074、Axioms.SceneBounds 871/871，Scene1 聚合通过，公理仅含
标准允许集合；资源见 `docs/Scene1进度总览.md`。数学提交 `e349ee0` 已推送并与
`origin/main` 一致。

## S1.353：Canonical Tate-family q-pilot bundle

- `JT-SCENE1-INITIAL-THETA-CANONICAL-TATE-QPILOT-DATA`：
  `Act1Scene1/IutInitialThetaCanonicalTateQPilotData.lean`；由 link Tate family
  与实际 `iutInitialThetaTateParameterData D` 等式派生 q-pilot source、carrier 和
  degree-one weighted normalization。

消费 `ofInitialThetaCanonicalTateData` 与现有 normalization audit；原创适配，无参考
源码复制/import。Prologue-R5→R5，derive，owner Scene1；Core 假设/退休/迁移增量均 0。
不构造 analytic packet/hull/volume/accounting，也不识别 paper theta/BK/different-untilt。
验证：Checks.SceneBounds 1075/1075、Axioms.SceneBounds 872/872，Scene1 聚合通过，
公理仅含标准允许集合；资源见 `docs/Scene1进度总览.md`。数学提交 `abb5cd5` 已推送
并与 `origin/main` 一致。

## S1.354：Canonical Tate-only q-order alignment

- `JT-SCENE1-INITIAL-THETA-CANONICAL-TATE-QORDER`：
  `Act1Scene1/IutInitialThetaCanonicalTateQPilotData.lean`；证明 Tate-only q-pilot
  source 的每个 q-order 等于 actual `InitialThetaData.prime.qOrder`。

消费 Tate-only source adapter、actual place carrier、canonical parameter theorem 和
completion q-order theorem；原创适配，无参考源码复制/import。Prologue-R5→R5，derive，
owner Scene1；Core 假设/退休/迁移增量均 0。未构造 reference absLogQ 总和桥或 paper
theta/BK/different-untilt 身份。验证：Checks.SceneBounds 1076/1076、Axioms.SceneBounds
873/873，Scene1 聚合通过，公理仅含标准允许集合；资源见 `docs/Scene1进度总览.md`。
数学提交 `d88a1fe` 已推送并与 `origin/main` 一致。

## S1.355：Tate-only q-pilot reference absLogQ bridge

- `JT-SCENE1-INITIAL-THETA-CANONICAL-TATE-QPILOT-REFERENCE`：
  `Act1Scene1/IutInitialThetaCanonicalTateQPilotReferenceBridge.lean`；证明 Tate-only
  Scene1 q-pilot `absLogQ` 等于 actual reference `InitialThetaData` q-pilot `absLogQ`。

消费 S1.353 Tate-only bundle、S1.354 q-order alignment、actual finite carrier 和
reference q-pilot definition；原创适配，无参考源码复制/import。Prologue-R5→R5，derive，
owner Scene1；Core 假设/退休/迁移增量均 0。未构造 paper 未加权 accounting、theta/BK/
different-untilt 身份。验证：Checks.SceneBounds 1077/1077、Axioms.SceneBounds 874/874，
Scene1 聚合通过，公理仅含标准允许集合；资源见 `docs/Scene1进度总览.md`。数学提交
`4dcd2e3` 已推送并与 `origin/main` 一致。

## S1.346：Canonical actual q-pilot strict subprobability bound

- `JT-SCENE1-INITIAL-THETA-CANONICAL-SUBPROBABILITY-BOUND`：
  `Act1Scene1/IutInitialThetaCanonicalSubprobabilityBound.lean`；把 canonical
  degree-one Scene1 q-pilot `absLogQ` 严格界于 actual selected paper sum 以下。

消费 q-pilot/reference actual equality 与 S1.283 strict representative gap；
原创 canonical bundle 适配，无参考源码复制/import。Prologue-R5→R5，derive，
owner Scene1；Core 假设/退休/迁移增量均 0。S1.345 mass-one certificate 已排除；
G3 的 revised paper representative semantics、thetaVolume 和联合真实模型仍 open。
验证：Checks.SceneBounds 1068/1068、Axioms.SceneBounds 865/865 逐名匹配，
Scene1 聚合通过，公理仅含标准允许集合；资源见 `docs/Scene1进度总览.md`。

## S1.356：Canonical Tate qLogSum target accounting

- source-id: `JT-SCENE1-INITIAL-THETA-CANONICAL-TATE-QPILOT-TARGET-ACCOUNTING`
- declaration: `Corollary312Scene1QPilotData.qLogSum_eq_absLogQ`、
  `qLogSum_eq_reference_ofCanonicalInitialThetaTateData`，文件
  `Act1Scene1/IutInitialThetaCanonicalTateQPilotTargetAccounting.lean`。

原创适配，消费 Tate q-family、source-index bridge 和 S1.355；无参考源码复制/import。
证明 target qLogSum 与 q-pilot/reference absLogQ 相等；paper 未加权 accounting 另有义务。
Prologue-R5→R5；derive；owner Scene1；Core 假设/退休/迁移增量均 0。
Checks.SceneBounds 1079/1079、Axioms.SceneBounds 876/876；Scene1 聚合通过。
资源见总览。数学提交 `eb46941` 已推送。

## S1.357：Canonical target / selected paper sum incompatibility

- source-id: `JT-SCENE1-CANONICAL-TARGET-PAPER-SUM-INCOMPATIBILITY`
- declarations: `canonicalTateTarget_qLogSum_lt_selectedPaperSum`、
  `canonicalTateTarget_selectedPaperAccounting_impossible`、
  `canonicalLinkTarget_selectedPaperAccounting_impossible`，文件
  `Act1Scene1/IutInitialThetaCanonicalTargetPaperSumAudit.lean`。

原创组合证明，消费 S1.356 target/reference equality 与 S1.283 strict ramification gap；
无参考源码复制/import。canonical degree-one 来源条件已推出 target qLogSum 严格小于
selected paper sum，因此 S1.351–352 额外要求的 `hq` 等式不可能满足。两者公开签名保留，
其“条件性完成”解释由本条及 log5 S1-BND-357 纠正为“输入不相容”；不是原论文反例。
后续须保留实际权重并修订下游会计。Prologue-R5→R5；derive；owner Scene1；Core
假设/退休/迁移增量均 0；最终闸门仍 0/4。Checks.SceneBounds 1082/1082、
Axioms.SceneBounds 879/879 与 trace 逐名匹配；Scene1 聚合通过，公理仅含标准允许集合。
数学提交 `824a5a2`；资源及失败尝试见总览。

## S1.358：Canonical raw accounting and hull consumer without preassembled base

- `JT-SCENE1-CANONICAL-TATE-RAW-ACCOUNTING-WITHOUT-BASE`：
  `Act1Scene1/IutInitialThetaCanonicalRawTargetAccounting.lean`，泛化 actual source/reference
  finite-sum bridge，不依赖完整 Scene1 base 或 degree-one；target qLogSum 保留数域次数。
- `JT-SCENE1-CANONICAL-RAW-HULL-CONSUMER`：
  `Act1Scene1/IutInitialThetaCanonicalRawHullConsumer.lean`，从实际 Haar 界与 raw accounting
  推导 transfer、qProduct 下界及当前 raw `Corollary312`，不接收目标等价估计或 accounting。

消费本工程 actual Tate adapter、q-order alignment、raw degree accounting 和 actual
collated hull Haar 估计；原创泛化与组合，无参考源码复制/import。共同真实模型和论文
carrier/norm/volume identity 仍 open。Prologue-R5→R5，derive，owner Scene1；Core
假设/退休/迁移增量均 0；最终闸门仍 0/4。Checks.SceneBounds 1087/1087、
Axioms.SceneBounds 884/884 与 trace 逐名匹配，Scene1 聚合通过；仅使用标准允许公理。
数学提交 `c335975`；资源及失败尝试见总览。

## S1.359：Ordinary logarithm on the principal-unit rational Kummer image

- `JT-SCENE1-PRINCIPAL-KUMMER-IMAGE-LOGARITHM`：
  `Act1Scene1/LocalKummerImageLogarithm.lean`，构造 rational Kummer hom、实际 principal-unit
  子群及其 H¹ 像，证明 log 的代表无关性并下降为该像上的加法同态。
- `JT-SCENE1-INITIAL-THETA-KUMMER-IMAGE-LOGARITHM`：
  `Act1Scene1/IutInitialThetaKummerImageLogarithm.lean`，actual rationalClass 的像成员
  以及 imageLog 值为 p* 乘 ordinary log witness。

来源需求为 Joshi III 3190–3236；证明消费本工程 ordinary log 乘法律、standard rational
cohomology 和一般局部 rational Kummer 非零定理。原创组合，无参考源码复制/import。
此实际像尚未识别为 H¹ₑ，像上的普通 log 尚未识别为 BK log；连续、单射、满射和
ℚₚ 线性未证明，p* 除法是否留在像中未断言。Prologue-R5→R5，derive，owner Scene1；
Core 假设/退休/迁移增量均 0；最终闸门仍 0/4。Checks.SceneBounds 1099/1099、
Axioms.SceneBounds 896/896 与 trace 逐名匹配，Scene1 聚合通过；仅使用标准允许公理。
数学提交 `71406a8`；资源及失败尝试见总览。

## S1.360：Kernel of the principal-unit rational Kummer image logarithm

- `JT-SCENE1-PRINCIPAL-KUMMER-IMAGE-LOG-KERNEL`：
  `Act1Scene1/LocalKummerImageLogKernel.lean`，从实际 p-power 差商极限及小球保范数，
  证明 log 核为 p-power 单位根；与 rational Kummer 核比较，推出 image log 单射。
- 同时在 S1.359 两个 image-log 叶子追加自然数倍及 actual n 倍类的求值会计，
  延续原 source-id，不改变既有签名。

来源为 Joshi III 3190–3236 的 Kummer/log 比较需求；证明消费本工程已经验证的极限、
小球 log 和 rational cohomology 群律；原创组合，无参考源码复制/import。
结论只在 principal-unit Kummer 像内；不证明全局 H¹ 系数映射单射或 H¹ₑ/BK 身份、
连续、满射、ℚₚ 线性或 p* 除法的像成员。Prologue-R5→R5，derive，owner Scene1；Core
假设/退休/迁移增量均 0；最终闸门仍 0/4。Checks.SceneBounds 1105/1105、Axioms.SceneBounds 902/902 与 trace 逐名匹配，Scene1 聚合通过；
仅使用标准允许公理。数学提交 `c4ab12b`，资源及失败尝试见总览。

## S1.361：Paper-normalized log witness in ordinary log-shell

- source-id: `JT-SCENE1-PAPER-LOG-WITNESS-LOG-SHELL`
- declarations: `LocalPadicLog.paperNormalizedLog_mem_logShell`、
  `PaperLogWitnessHull.value_mem_logShell`，文件
  `Act1Scene1/IutInitialThetaPaperLogShellBridge.lean`。

原创局部组合证明，消费 existing p*-normalized ordinary log、ordinary log-shell、
`padicLog_pow` 和 actual qroot norm bound；无参考源码复制/import。奇素数通过平方
principal unit 对齐 `p*` 与 shell 的 `2p` 归一化，p=2 直接化简。只证明 ordinary
carrier 成员关系，不识别 H¹ₑ/BK、paper theta locus、different-untilt 或 thetaVolume。
Prologue-R5→R5；derive；owner Scene1；Core 假设/退休/转入/取出增量均 0；最终闸门仍 0/4。
Checks.SceneBounds 1107/1107、Axioms.SceneBounds 904/904 与 trace 逐名匹配；Scene1
聚合通过，公理仅含标准允许集合。资源及失败尝试见总览。


## S1.362：Paper witness tensor log-shell carrier

- source-id: `JT-SCENE1-PAPER-WITNESS-TENSOR-LOG-SHELL`
- declaration: `PaperLogWitnessHull.witness_mem_tensorLogShell`，文件
  `Act1Scene1/IutInitialThetaPaperWitnessTensorLogShell.lean`。

消费 S1.361 factorwise paper-normalized log-shell 成员关系、actual full-support witness
和 tensor lattice API；原创组合，无参考源码复制/import。证明 actual pure tensor witness
属于 ordinary tensor `tensorLogShell`，但不识别 H¹ₑ/BK、paper theta locus、different-untilt
或 thetaVolume。Prologue-R5→R5；derive；owner Scene1；Core 假设/退休/迁移增量均 0；
最终闸门仍 0/4。Checks.SceneBounds 1108/1108、Axioms.SceneBounds 905/905 与 trace
逐名匹配；Scene1 聚合通过，公理仅含标准允许集合。资源及失败尝试见总览。

## S1.363：p-power saturated Kummer image

- `JT-SCENE1-PRINCIPAL-KUMMER-P-SATURATED-LOG`：
  `Act1Scene1/LocalKummerSaturatedLogarithm.lean`，在 standard rational H¹ 内定义
  p-power 饱和子群，构造清分母的 ordinary log 加法映射并证明其单射。
- `JT-SCENE1-INITIAL-THETA-NORMALIZED-SATURATED-KUMMER-LOG`：
  `Act1Scene1/IutInitialThetaSaturatedKummerLog.lean`，证明 actual normalizedRationalClass
  属于该饱和子群，并定义其饱和载体。

消费 S1.359 image log、S1.360 核比较及 p* 标量还原；无参考源码复制/import。实际
normalized class 的 ordinary witness 求值仍未在默认 heartbeat 下闭合，因此不宣称该等式。
不识别 H¹ₑ/BK、原像除法封闭、连续、满射或 ℚₚ scalar closure。Prologue-R5→R5；derive；
owner Scene1；Core 假设/退休/迁移增量均 0；最终闸门仍 0/4。Checks.SceneBounds
1118/1118、Axioms.SceneBounds 915/915 与 trace 逐名匹配；资源及失败尝试见总览。

## S1.364：Actual normalized saturated Kummer log evaluation

- `PrincipalUnitKummer.normalizedRationalClass_saturatedLogGraph` 与
  `PrincipalUnitKummer.normalizedSaturatedClass_saturatedImageLog_eq_value`：
  `Act1Scene1/IutInitialThetaSaturatedKummerLog.lean`，用 p-power 清分母 graph
  证明 actual normalized class 的 saturated log 等于 `PaperLogWitnessHull.value`。

消费 S1.359 的 image log、S1.360 的单射核比较和 S1.363 的饱和载体成员；无参考源码
复制/import。局部 theorem 使用 `maxHeartbeats 1000000` 仅缓解 dependent graph
elaboration，不改变全局配置或数学假设。仍不识别 H¹ₑ/BK，不证明原像除法封闭、连续、
满射或 ℚₚ scalar closure。Prologue-R5→R5；derive；owner Scene1；Core 假设/退休/迁移
增量均 0；最终闸门仍 0/4。Checks.SceneBounds 1120/1120、Axioms.SceneBounds 917/917
与 trace 逐名匹配；数学提交 `5655baf` 已推送；资源见总览。

## S1.365：Integral tensor hull inside the tensor log-shell

- `LocalCompletion.Packet.integralHull_le_tensorLogShell`：对实际 tensor 中任意
  `U ⊆ tensorLogShell`，证明其 `ℤ_[p]` integral span 仍包含于 `tensorLogShell`。
- `PaperLogWitnessHull.witness_integralHull_le_tensorLogShell`：将该 carrier inclusion
  接到 actual singleton paper witness hull。

原创 carrier 组合，无参考源码复制/import。只使用 Submodule span 闭包和 S1.362 的
actual witness membership；不识别 normalization hull、paper theta locus、H¹ₑ/BK 或 volume。
Prologue-R5→R5；derive；owner Scene1；Core 假设/退休/迁移增量均 0；最终闸门仍 0/4。
Checks.SceneBounds 1122/1122、Axioms.SceneBounds 919/919；数学提交 `4f39dc3` 已推送；
S1.365 热构建耗时 115.38s，最大 RSS 8,294,872 kB。

## S1.366：Actual paper witness integral hull inside the unit lattice

- `PaperLogWitnessHull.witness_integralHull_le_unitLattice`：由 actual paper
  normalized log 的范数等式和 q-root 的严格 contracting 界，将 singleton
  `integralHull` 放入对应 tensor packet 的 `unitLattice`。

原创 carrier 推论，无参考源码复制/import。它消费实际 `paperNormalizedLog` 范数和
S1.365 之前的 integral-hull API；不识别 normalization hull、paper theta locus、H¹ₑ/BK
或 volume。Prologue-R5→R5；derive；owner Scene1；Core 假设/退休/迁移增量均 0；
最终闸门仍 0/4。
Checks.SceneBounds 1123/1123、Axioms.SceneBounds 920/920；数学提交 `79cd9c5` 已推送；
S1.366 窄审计与 Scene1 聚合耗时 164.60s，最大 RSS 8,295,668 kB，9420 个 Lake 任务。

## S1.367：Actual paper witness integral hull in the combined carrier

- `PaperLogWitnessHull.witness_integralHull_le_unitLattice_inf_tensorLogShell`：
  合并 S1.365 的 tensor log-shell 包含和 S1.366 的 unit-lattice 包含，得到
  singleton actual paper witness hull 位于两者的 `Submodule.inf` 中。

原创组合定理，无参考源码复制/import。它只重用两个已证 carrier inclusion；不识别
normalization hull、paper theta locus、H¹ₑ/BK 或 volume。Prologue-R5→R5；derive；owner
Scene1；Core 假设/退休/迁移增量均 0；最终闸门仍 0/4。
Checks.SceneBounds 1124/1124、Axioms.SceneBounds 921/921；数学提交 `05465c0` 已推送；
S1.367 窄审计与 Scene1 聚合耗时 160.84s，最大 RSS 8,295,280 kB，9420 个 Lake 任务。

## S1.368：Bounded actual paper witness integral hull

- `PaperLogWitnessHull.witness_integralHull_isBounded`：消费 actual
  `unitLattice_isBounded` 与 S1.366 的 carrier inclusion，证明 singleton paper
  witness 的 `integralHull` bounded。

原创 boundedness 推论，无参考源码复制/import。只提供 bounded carrier 输入，不把它
升级为 compact、normalization hull、paper theta locus、H¹ₑ/BK 或 volume。Prologue-R5→R5；
derive；owner Scene1；Core 假设/退休/迁移增量均 0；最终闸门仍 0/4。
Checks.SceneBounds 1125/1125、Axioms.SceneBounds 922/922；数学提交 `c7a6dfc` 已推送；
S1.368 窄审计与 Scene1 聚合耗时 156.00s，最大 RSS 8,295,068 kB，9420 个 Lake 任务。

## S1.369：Actual paper witness integral hull inside normalization

- `PaperLogWitnessHull.witness_integralHull_le_normalization`：将 S1.366 的
  actual unit-lattice carrier inclusion 沿 `unitLattice_le_normalization` 传到实际
  normalization submodule。

原创 carrier 组合，无参考源码复制/import。它只证明 normalization 的包含，不识别
normalization hull、paper theta locus、H¹ₑ/BK 或 volume。Prologue-R5→R5；derive；owner
Scene1；Core 假设/退休/迁移增量均 0；最终闸门仍 0/4。
Checks.SceneBounds 1126/1126、Axioms.SceneBounds 923/923；数学提交 `3f5285a` 已推送；
S1.369 窄审计与 Scene1 聚合耗时 164.33s，最大 RSS 8,295,088 kB，9420 个 Lake 任务。

## S1.370：Normalization hull containment for the actual integral witness hull

- `PaperLogWitnessHull.witness_integralHull_normalizationHull_subset_normalization`：
  将 S1.369 的 actual integral-hull normalization inclusion 传入现有
  `normalizationHull_subset_normalization`，得到其 normalization hull 的 containment。

原创消费者组合，无参考源码复制/import。它不识别 normalization hull 等式、paper theta
locus、H¹ₑ/BK 或 volume。Prologue-R5→R5；derive；owner Scene1；Core 假设/退休/迁移增量均 0；
最终闸门仍 0/4。
Checks.SceneBounds 1127/1127、Axioms.SceneBounds 924/924；数学提交 `606d075` 已推送；
S1.370 窄审计与 Scene1 聚合耗时 168.22s，最大 RSS 8,295,904 kB，9420 个 Lake 任务。

## S1.371：Positive finite Haar for the actual integral-witness normalization hull

- `PaperLogWitnessHull.witness_integralHull_normalizationHull_haar_pos_lt_top`：
  对 actual singleton paper witness 的 `normalizationHull (integralHull {witness})`
  证明 normalization Haar 严格正且小于 `⊤`。

该定理消费 actual factor witness 非零性、S1.369 normalization carrier 和现有
`normalizationHull_haar_pos_lt_top_of_pure_mem`；无参考源码复制/import。它只提供实际
measure 输入，不识别 paper thetaVolume、H¹ₑ/BK 或最终 volume accounting。Prologue-R5→R5；
derive；owner Scene1；Core 假设/退休/迁移增量均 0；最终闸门仍 0/4。
Checks.SceneBounds 1128/1128、Axioms.SceneBounds 925/925；数学提交 `afa7b14` 已推送；
S1.371 窄审计与 Scene1 聚合耗时 155.00s，最大 RSS 8,295,172 kB，9420 个 Lake 任务。

## S1.372：Positive normalization-degree volume for the actual witness hull

- `PaperLogWitnessHull.witness_integralHull_normalizationDegreeVolume_pos`：
  将 S1.371 的正有限 normalization Haar 转成 actual
  `normalizationDegreeVolume` 的严格正性。

原创数值消费者组合，无参考源码复制/import。它不识别 paper thetaVolume、H¹ₑ/BK、
different-untilt 或最终 volume accounting。Prologue-R5→R5；derive；owner Scene1；
Core 假设/退休/迁移增量均 0；最终闸门仍 0/4。
Checks.SceneBounds 1129/1129、Axioms.SceneBounds 926/926；数学提交 `cf5b3a0` 已推送；
S1.372 窄审计与 Scene1 聚合耗时 153.75s，最大 RSS 8,295,240 kB，9420 个 Lake 任务。

## S1.373：Upper bound for the actual witness degree volume

- `PaperLogWitnessHull.witness_integralHull_normalizationDegreeVolume_le_one`：
  由 S1.370 的 normalization-hull containment 和 `normalizationDegreeVolume_le_one`
  得到 actual witness hull 的 degree volume `≤ 1`。

原创消费者组合，无参考源码复制/import。与 S1.372 合成 actual volume 的 `(0,1]`
输入；不识别 paper thetaVolume、H¹ₑ/BK 或最终 volume accounting。Prologue-R5→R5；
derive；owner Scene1；Core 假设/退休/迁移增量均 0；最终闸门仍 0/4。
Checks.SceneBounds 1130/1130、Axioms.SceneBounds 927/927；数学提交 `e3c525a` 已推送；
S1.373 窄审计与 Scene1 聚合耗时 156.31s，最大 RSS 8,295,268 kB，9420 个 Lake 任务。

## S1.374：Nonpositive log of the actual witness hull degree volume

- `PaperLogWitnessHull.witness_integralHull_normalizationDegreeVolume_log_nonpos`：
  由 S1.372 的正性和 S1.373 的 `≤ 1` 上界，证明 actual normalization-hull degree
  volume 的实数对数不正。

这是 actual normalization-hull 的符号结果，不是论文 qLogTerm 符号裁决；用户决定的
“暂按笔误处理”保持不变。无参考源码复制/import；不识别 paper thetaVolume、H¹ₑ/BK 或
最终 volume accounting。Prologue-R5→R5；derive；owner Scene1；Core 假设/退休/迁移增量均 0；
最终闸门仍 0/4。
Checks.SceneBounds 1131/1131、Axioms.SceneBounds 928/928；数学提交 `3fd0470` 已推送；
S1.374 窄审计与 Scene1 聚合耗时 157.34s，最大 RSS 8,295,344 kB，9420 个 Lake 任务。

## S1.375：Nonnegative negative-log of the actual witness hull volume

- `PaperLogWitnessHull.witness_integralHull_normalizationDegreeVolume_negLog_nonneg`：
  将 S1.374 的 actual log-volume 非正性改写为 negative-log 非负性。

这是 actual volume transfer 的符号输入，不是论文 qLogTerm 裁决；用户决定的暂按笔误
处理保持不变。无参考源码复制/import；不识别 paper thetaVolume、H¹ₑ/BK 或最终 accounting。
Prologue-R5→R5；derive；owner Scene1；Core 假设/退休/迁移增量均 0；最终闸门仍 0/4。
Checks.SceneBounds 1132/1132、Axioms.SceneBounds 929/929；数学提交 `26cb12c` 已推送；
S1.375 窄审计与 Scene1 聚合耗时 157.91s，最大 RSS 8,295,368 kB，9420 个 Lake 任务。

## S1.376：Scalar-lattice volume lower bound for the actual witness hull

- `PaperLogWitnessHull.witness_integralHull_degreeVolume_le_normalizationHull_degreeVolume`：
  对 actual paper witness 的 factor scalar lattice，证明其 `degreeVolume` 不超过
  `normalizationHull (integralHull {witness})` 的 `normalizationDegreeVolume`。

消费现有 pure-witness hull volume lemma，无参考源码复制/import。该不等式不识别 paper
thetaVolume、H¹ₑ/BK 或最终 volume accounting。Prologue-R5→R5；derive；owner Scene1；
Core 假设/退休/迁移增量均 0；最终闸门仍 0/4。
Checks.SceneBounds 1133/1133、Axioms.SceneBounds 930/930；数学提交 `3d0242b` 已推送；
S1.376 窄审计与 Scene1 聚合耗时 158.00s，最大 RSS 8,295,432 kB，9420 个 Lake 任务。

## S1.377：Actual normalization-hull negative-log comparison

| source-id | declaration | fidelity / boundary | model evidence | status |
| --- | --- | --- | --- | --- |
| `JT-SCENE1-PAPER-WITNESS-NORMALIZATION-NEGLOG-COMPARISON` | `PaperLogWitnessHull.witness_integralHull_normalizationHull_negLog_le_scalarLattice_negLog` | actual witness normalization-hull versus scalar-lattice negative-log comparison；Scene1/Derived | S1.372 actual degree-volume positivity and S1.376 actual degree-volume lower bound; `Real.log_le_log` and `neg_le_neg` | proved / accepted |

该定理不识别 paper thetaVolume、H¹ₑ/BK、different-untilt 或最终 accounting；qLogTerm
符号差异继续按用户决定暂作笔误。Checks.SceneBounds 1134/1134、Axioms.SceneBounds
931/931，Scene1 聚合通过，公理白名单仍为 `propext`、`Classical.choice`、`Quot.sound`。
叶文件成功构建耗时 `101.35s`、峰值 `8,279,716 kB`；三目标热构建耗时 `156.22s`、
峰值 `8,296,204 kB`、9420 个 Lake 任务；本单元累计含两次失败尝试为 `461.91s`。

## S1.378：Actual integral-hull normalization-hull identity

| source-id | declaration | fidelity / boundary | model evidence | status |
| --- | --- | --- | --- | --- |
| `JT-SCENE1-PAPER-WITNESS-INTEGRAL-NORMALIZATION-HULL-IDENTITY` | `PaperLogWitnessHull.witness_integralHull_normalizationHull_eq_base` | actual integral-hull normalization-hull carrier identity；Scene1/Derived | `LocalCompletion.Packet.normalizationHull_integralHull` and `PaperLogWitnessHull.witness_hull_eq_base` | proved / accepted |

该定理只把 actual `normalizationHull (integralHull {witness})` 重写为既有
`FullSupportThetaLogHull.region`，不识别 paper thetaVolume、H¹ₑ/BK、different-untilt
或最终 accounting。Checks.SceneBounds 1135/1135、Axioms.SceneBounds 932/932，
Scene1 聚合通过，公理白名单仍为 `propext`、`Classical.choice`、`Quot.sound`。
热构建耗时 `208.14s`、峰值 `8,295,596 kB`、9420 个 Lake 任务。

## S1.379：Actual normalization degree-volume identity

| source-id | declaration | fidelity / boundary | model evidence | status |
| --- | --- | --- | --- | --- |
| `JT-SCENE1-PAPER-WITNESS-NORMALIZATION-DEGREE-VOLUME-IDENTITY` | `PaperLogWitnessHull.witness_integralHull_normalizationDegreeVolume_eq_base` | actual normalization degree-volume identity；Scene1/Derived | S1.378 carrier equality and functional congruence of `normalizationDegreeVolume` | proved / accepted |

该定理只把 S1.378 的 actual carrier identity 提升为同一 packet 上的数值 volume identity，
不识别 paper thetaVolume、H¹ₑ/BK、different-untilt 或最终 accounting。Checks.SceneBounds
1136/1136、Axioms.SceneBounds 933/933，Scene1 聚合通过，公理白名单仍为 `propext`、
`Classical.choice`、`Quot.sound`。热构建耗时 `206.74s`、峰值 `8,295,616 kB`、9420 个 Lake 任务。

## S1.380：Actual local volume relative-factor identity

| source-id | declaration | fidelity / boundary | model evidence | status |
| --- | --- | --- | --- | --- |
| `JT-SCENE1-PAPER-WITNESS-LOCAL-VOLUME-RELATIVE-FACTOR` | `PaperLogWitnessHull.witness_integralHull_localVolume_eq_relativeFactor_pow` | actual local volume to relative q-root factor identity；Scene1/Derived | S1.379 numerical volume identity and `FullSupportThetaLogHull.localVolume_eq_relativeFactor_pow` | proved / accepted |

该定理只把 actual block volume 的 local-degree 幂接到 relative q-root factor 的 `n` 次幂，
不识别 paper thetaVolume、H¹ₑ/BK、different-untilt 或最终 accounting。Checks.SceneBounds
1137/1137、Axioms.SceneBounds 934/934，Scene1 聚合通过，公理白名单仍为 `propext`、
`Classical.choice`、`Quot.sound`。热构建耗时 `207.39s`、峰值 `8,295,684 kB`、9420 个 Lake 任务。

## S1.381：Actual raw full-support volume product

| source-id | declaration | fidelity / boundary | model evidence | status |
| --- | --- | --- | --- | --- |
| `JT-SCENE1-PAPER-WITNESS-RAW-FULL-SUPPORT-PRODUCT` | `PaperLogWitnessHull.witness_integralHull_localVolume_product_eq_relativeQRootProduct_pow` | actual raw full-support volume product；Scene1/Derived | S1.380 local identity, `Finset.prod_pow`, and the raw relative q-root product definition | proved / accepted |

该定理保持未做 global degree root 的 raw product 形式，不识别 paper thetaVolume、H¹ₑ/BK、
different-untilt 或最终 accounting。Checks.SceneBounds 1138/1138、Axioms.SceneBounds
935/935，Scene1 聚合通过，公理白名单仍为 `propext`、`Classical.choice`、`Quot.sound`。
热构建耗时 `214.48s`、峰值 `8,295,760 kB`、9420 个 Lake 任务。

## S1.382：Actual global degree normalization

| source-id | declaration | fidelity / boundary | model evidence | status |
| --- | --- | --- | --- | --- |
| `JT-SCENE1-PAPER-WITNESS-GLOBAL-DEGREE-NORMALIZATION` | `PaperLogWitnessHull.witness_integralHull_globalVolume_eq_normalizedRelativeQRootProduct_pow` | actual global degree-normalized volume identity；Scene1/Derived | S1.381 raw product, normalized relative product definition, and `Real.rpow_pow_comm` | proved / accepted |

该定理只处理 actual raw product 与全局 finrank 实幂的交换，不识别 paper thetaVolume、
H¹ₑ/BK、different-untilt 或最终 accounting。Checks.SceneBounds 1139/1139、Axioms.SceneBounds
936/936，Scene1 聚合通过，公理白名单仍为 `propext`、`Classical.choice`、`Quot.sound`。
首次 API 适配失败后，修正构建耗时 `216.49s`、峰值 `8,295,832 kB`、9420 个 Lake 任务。

## S1.383：Actual global volume/full-support alignment

| source-id | declaration | fidelity / boundary | model evidence | status |
| --- | --- | --- | --- | --- |
| `JT-SCENE1-PAPER-WITNESS-FULL-SUPPORT-VOLUME-ALIGNMENT` | `PaperLogWitnessHull.witness_integralHull_globalVolume_eq_fullSupport_volume` | actual global volume presentation alignment；Scene1/Derived | S1.382 normalized product identity and `FullSupportThetaLogHull.volume_eq_normalizedFullRootProduct_pow` | proved / accepted |

该定理只把 actual global normalized volume 对齐为 full-support global volume，不识别 paper
thetaVolume、H¹ₑ/BK、different-untilt 或最终 accounting。Checks.SceneBounds 1140/1140、
Axioms.SceneBounds 937/937，Scene1 聚合通过，公理白名单仍为 `propext`、`Classical.choice`、
`Quot.sound`。热构建耗时 `216.76s`、峰值 `8,296,428 kB`、9420 个 Lake 任务。

## S1.384：Actual global volume negative-log identity

| source-id | declaration | fidelity / boundary | model evidence | status |
| --- | --- | --- | --- | --- |
| `JT-SCENE1-PAPER-WITNESS-GLOBAL-VOLUME-NEGLOG` | `PaperLogWitnessHull.witness_integralHull_globalVolume_negLog_eq_mul_fullBaseSum` | actual global volume negative-log identity；Scene1/Derived | S1.383 actual/full-support alignment and full-support negative-log formula | proved / accepted |

该定理只把 actual global volume 的 negative log 表达为 full-base q-pilot log sum，不识别
paper thetaVolume、H¹ₑ/BK、different-untilt 或最终 accounting。Checks.SceneBounds 1141/1141、
Axioms.SceneBounds 938/938，Scene1 聚合通过，公理白名单仍为 `propext`、`Classical.choice`、
`Quot.sound`。热构建耗时 `212.96s`、峰值 `8,296,440 kB`、9420 个 Lake 任务。

## S1.385：Actual global volume absolute-log identity

| source-id | declaration | fidelity / boundary | model evidence | status |
| --- | --- | --- | --- | --- |
| `JT-SCENE1-PAPER-WITNESS-GLOBAL-VOLUME-ABSLOG` | `PaperLogWitnessHull.witness_integralHull_globalVolume_absLog_eq_mul_fullBaseSum` | actual global volume absolute-log identity；Scene1/Derived | S1.383 actual/full-support alignment and full-support absolute-log formula | proved / accepted |

该定理只补充 actual global volume 的 absolute-log 表达，不识别 paper thetaVolume、H¹ₑ/BK、
different-untilt 或最终 accounting。Checks.SceneBounds 1142/1142、Axioms.SceneBounds 939/939，
Scene1 聚合通过，公理白名单仍为 `propext`、`Classical.choice`、`Quot.sound`。
热构建耗时 `221.22s`、峰值 `8,296,000 kB`、9420 个 Lake 任务。

## S1.386：Actual global negative-log reference lower bound

| source-id | declaration | fidelity / boundary | model evidence | status |
| --- | --- | --- | --- | --- |
| `JT-SCENE1-PAPER-WITNESS-REFERENCE-ABSLOG-LOWER-BOUND` | `PaperLogWitnessHull.witness_integralHull_globalVolume_negLog_ge_mul_referenceAbsLogQ` | actual global negative-log versus reference absLogQ lower bound；Scene1/Derived | S1.384 actual negative-log identity and `iutInitialThetaReferenceAbsLogQ_le_fullBaseSum` | proved / accepted |

该定理只建立 actual volume 到 reference q-pilot 的下界，不把 reference q-pilot 识别为 paper
target 或 thetaVolume，也不引入 H¹ₑ/BK、different-untilt 或最终 accounting。Checks.SceneBounds
1143/1143、Axioms.SceneBounds 940/940，Scene1 聚合通过，公理白名单仍为 `propext`、
`Classical.choice`、`Quot.sound`。两次失败尝试后成功构建耗时 `217.85s`、峰值
`8,296,220 kB`、9420 个 Lake 任务；本单元累计 `488.32s`。

## S1.387：Actual global negative-log strict selected-paper upper bound

| source-id | declaration | fidelity / boundary | model evidence | status |
| --- | --- | --- | --- | --- |
| `JT-SCENE1-PAPER-WITNESS-GLOBAL-VOLUME-SELECTED-PAPER-UPPER-BOUND` | `PaperLogWitnessHull.witness_integralHull_globalVolume_negLog_lt_mul_selectedPaperSum` | actual global negative-log strict comparison with the selected paper sum；Scene1/Derived | S1.384 actual negative-log identity, `iutInitialThetaFullBaseQPilotLogSum_lt_selectedPaperSum`, and positive `n` | proved / accepted |

该定理只在 `0 < n` 下证明 ordinary actual witness-hull global negative log 严格小于
`(n : ℝ) * iutInitialThetaSelectedQRootPaperSum D`。它不把该 volume 识别为论文
thetaVolume，不构造 H¹ₑ/BK、different-untilt 或真实联合模型，也不关闭任何最终闸门。
Prologue-R5→R5；derive；owner Scene1；Core 假设/退休/转入/取出增量均 0。
首次类型不匹配失败后，Checks.SceneBounds 1144/1144、Axioms.SceneBounds 941/941
与 Scene1 聚合通过，公理仅含 `propext`、`Classical.choice`、`Quot.sound`。
修正后三目标热构建耗时 `220.64s`、峰值 RSS `8,296,100 kB`、9420 个 Lake 任务；
本单元累计 `356.65s`。未冷建、清缓存或重编 Mathlib。

## S1.388：Actual global selected-root product lower bound

| source-id | declaration | fidelity / boundary | model evidence | status |
| --- | --- | --- | --- | --- |
| `JT-SCENE1-PAPER-WITNESS-GLOBAL-VOLUME-SELECTED-ROOT-PRODUCT-LOWER-BOUND` | `PaperLogWitnessHull.witness_integralHull_globalVolume_selectedPaperRootProduct_pow_lt` | actual global volume strictly dominates the selected paper root-product power；Scene1/Derived | S1.383 actual/full-support volume identity and `FullSupportThetaLogHull.selectedPaperRootProduct_pow_lt_volume` | proved / accepted |

该定理只在 `0 < n` 下把 selected paper root-norm product 的 `n` 次幂接到 actual
witness-hull global volume。它不把该 volume 识别为论文 thetaVolume，不构造 H¹ₑ/BK、
different-untilt 或真实联合模型，也不关闭任何最终闸门。Prologue-R5→R5；derive；
owner Scene1；Core 假设/退休/转入/取出增量均 0。首次精确导入遗漏失败后，
Checks.SceneBounds 1145/1145、Axioms.SceneBounds 942/942 与 Scene1 聚合通过，公理仅含
`propext`、`Classical.choice`、`Quot.sound`。修正后三目标热构建耗时 `226.52s`、
峰值 RSS `8,296,116 kB`、9420 个 Lake 任务；本单元累计 `356.05s`。未冷建、清缓存或
重编 Mathlib。

## S1.389：Actual global volume positivity

| source-id | declaration | fidelity / boundary | model evidence | status |
| --- | --- | --- | --- | --- |
| `JT-SCENE1-PAPER-WITNESS-GLOBAL-VOLUME-POSITIVITY` | `PaperLogWitnessHull.witness_integralHull_globalVolume_pos` | strict positivity of the actual global witness-hull volume；Scene1/Derived | S1.383 actual/full-support volume identity and `FullSupportThetaLogHull.volume_pos` | proved / accepted |

该定理只为 actual witness-hull global volume 提供严格正性，供后续实对数和指数消费者
使用；不识别论文 thetaVolume，不构造 H¹ₑ/BK、different-untilt 或真实联合模型，且不关闭
任何最终闸门。Prologue-R5→R5；derive；owner Scene1；Core 假设/退休/转入/取出增量均 0。
Checks.SceneBounds 1146/1146、Axioms.SceneBounds 943/943 与 Scene1 聚合通过，公理仅含
`propext`、`Classical.choice`、`Quot.sound`。一次热构建耗时 `221.24s`、峰值 RSS
`8,296,188 kB`、9420 个 Lake 任务；未冷建、清缓存或重编 Mathlib。

## S1.390：Actual global volume upper bound

| source-id | declaration | fidelity / boundary | model evidence | status |
| --- | --- | --- | --- | --- |
| `JT-SCENE1-PAPER-WITNESS-GLOBAL-VOLUME-UPPER-BOUND` | `PaperLogWitnessHull.witness_integralHull_globalVolume_le_one` | actual global witness-hull volume is at most one；Scene1/Derived | S1.383 actual/full-support volume identity and `FullSupportThetaLogHull.volume_le_one` | proved / accepted |

该定理只证明 actual witness-hull global volume `≤ 1`，与 S1.389 的正性合成 `(0,1]`；
不识别论文 thetaVolume，不构造 H¹ₑ/BK、different-untilt 或真实联合模型，也不关闭任何最终
闸门。Prologue-R5→R5；derive；owner Scene1；Core 假设/退休/转入/取出增量均 0。
Checks.SceneBounds 1147/1147、Axioms.SceneBounds 944/944 与 Scene1 聚合通过，公理仅含
`propext`、`Classical.choice`、`Quot.sound`。一次热构建耗时 `212.45s`、峰值 RSS
`8,296,200 kB`、9420 个 Lake 任务；未冷建、清缓存或重编 Mathlib。

## S1.391：Actual global volume log nonpositivity

| source-id | declaration | fidelity / boundary | model evidence | status |
| --- | --- | --- | --- | --- |
| `JT-SCENE1-PAPER-WITNESS-GLOBAL-VOLUME-LOG-NONPOSITIVE` | `PaperLogWitnessHull.witness_integralHull_globalVolume_log_nonpos` | nonpositive real logarithm of the actual global witness-hull volume；Scene1/Derived | S1.389 positivity, S1.390 upper bound, and `Real.log_nonpos` | proved / accepted |

该定理只把 actual volume 的 `(0,1]` 范围转成 log 非正性，不识别论文 thetaVolume，不构造
H¹ₑ/BK、different-untilt 或真实联合模型，也不关闭任何最终闸门。Prologue-R5→R5；derive；
owner Scene1；Core 假设/退休/转入/取出增量均 0。Checks.SceneBounds 1148/1148、
Axioms.SceneBounds 945/945 与 Scene1 聚合通过，公理仅含 `propext`、`Classical.choice`、
`Quot.sound`。一次热构建耗时 `213.47s`、峰值 RSS `8,296,780 kB`、9420 个 Lake 任务；
未冷建、清缓存或重编 Mathlib。

## S1.396：Actual global negative-log/absolute-log reverse bridge

| source-id | declaration | fidelity / boundary | model evidence | status |
| --- | --- | --- | --- | --- |
| `JT-SCENE1-PAPER-WITNESS-GLOBAL-VOLUME-NEGLOG-ABSLOG-REVERSE-BRIDGE` | `PaperLogWitnessHull.witness_integralHull_globalVolume_negLog_eq_absLog` | reverse equality between actual global negative log and absolute log；Scene1/Derived | S1.393 absolute-log/negative-log bridge and symmetry | proved / accepted |

该定理只重排 actual volume 的两种符号表达，不识别论文 thetaVolume，不构造 H¹ₑ/BK、
different-untilt 或真实联合模型，也不关闭任何最终闸门。Prologue-R5→R5；derive；owner
Scene1；Core 假设/退休/转入/取出增量均 0。Checks.SceneBounds 1153/1153、Axioms.SceneBounds
950/950 与 Scene1 聚合通过，公理仅含 `propext`、`Classical.choice`、`Quot.sound`。
一次热构建耗时 `227.62s`、峰值 RSS `8,296,508 kB`、9420 个 Lake 任务；未冷建、清缓存或
重编 Mathlib。

| `JT-SCENE1-PAPER-WITNESS-GLOBAL-VOLUME-NEGAVERAGE-NORMALIZATION` | `PaperLogWitnessHull.witness_integralHull_globalVolume_negAverageAbsLog_le_neg_referenceAbsLogQ`; `PaperLogWitnessHull.witness_integralHull_globalVolume_negAverageAbsLog_gt_neg_selectedPaperSum` | normalized negative-average bounds for the actual global witness-hull volume；Scene1/Derived | S1.386/S1.387 global negative-log bounds, S1.396 reverse bridge, and positive natural-number cancellation | proved / accepted |

该单元显式保持 `negativeAverageAbsLog ≤ -referenceAbsLogQ` 与
`-selectedPaperSum < negativeAverageAbsLog` 的方向，不把 qLogTerm 符号差异接入 actual API；
不识别论文 thetaVolume，不构造 H¹ₑ/BK、different-untilt 或最终 accounting。Prologue-R5→R5；
derive；owner Scene1；Core 假设/退休/转入/取出增量均 0。Checks.SceneBounds 1155/1155、
Axioms.SceneBounds 952/952 与 Scene1 聚合通过，公理仅含 `propext`、`Classical.choice`、
`Quot.sound`。修正后热构建耗时 `243.717s`、过程组峰值 `25,894,920 KiB`、单进程峰值
`8,296,536 KiB`、9420 个 Lake 任务；未冷建、清缓存或重编 Mathlib。

| `JT-SCENE1-INITIAL-THETA-NORMALIZED-SATURATED-KUMMER-NONZERO` | `PrincipalUnitKummer.normalizedSaturatedClass_ne_zero`; `PrincipalUnitKummer.normalizedSaturatedClass_saturatedImageLog_ne_zero` | nonzero actual normalized class in the p-power saturated principal-unit Kummer carrier and nonzero saturated ordinary-log value；Scene1/Derived | S1.343 actual normalized rational-class nonvanishing, S1.364 saturated-log value equation, and `PaperLogWitnessHull.value_ne_zero` | proved / accepted |

| `JT-SCENE1-INITIAL-THETA-NORMALIZED-SATURATED-KUMMER-NONTORSION` | `PrincipalUnitKummer.normalizedSaturatedClass_nsmul_ne_zero` | nonzero natural multiples of the actual normalized saturated class；Scene1/Derived | S1.398 saturated-log nonzero, saturated image-log injectivity, and characteristic-zero natural-cast nonvanishing；S1.399 full audit 1158/955 | proved / accepted |

| `JT-SCENE1-INITIAL-THETA-NORMALIZED-SATURATED-KUMMER-ZSMUL-NONTORSION` | `PrincipalUnitKummer.normalizedSaturatedClass_zsmul_ne_zero` | nonzero integer multiples of the actual normalized saturated class；Scene1/Derived | S1.399 natural-multiple nonzero input, saturated image-log value equation, and characteristic-zero integer-cast nonvanishing | proved / accepted |

| `JT-SCENE1-INITIAL-THETA-NORMALIZED-RATIONAL-KUMMER-ZSMUL-NONTORSION` | `PrincipalUnitKummer.normalizedRationalClass_zsmul_ne_zero` | nonzero integer multiples of the actual normalized rational H¹ class；Scene1/Derived | S1.400 saturated-class integer nontorsion and subtype coercion compatibility | proved / accepted |

| `JT-SCENE1-INITIAL-THETA-RATIONAL-KUMMER-ZSMUL-NONTORSION` | `PrincipalUnitKummer.rationalClass_zsmul_ne_zero` | nonzero integer multiples of the actual unnormalized rational H¹ Kummer class；Scene1/Derived | S1.401 normalized rational-class integer nontorsion, `scale_normalizedRationalClass`, and nonzero paper scale | proved / accepted |

| `JT-SCENE1-H1E-BK-FORMAL-SOURCE-AVAILABILITY-AUDIT` | `refer/iut/**/*.lean` source-availability result (no declaration) | negative source evidence for H¹ₑ/BK/crystalline/Frobenius formalization；Scene1 boundary | targeted `rg` audit of reference Lean tree; paper index `index-Arithmetic Teichmuller Spaces 3.md:632–636` identifies external dependencies and no internal proof label | accepted negative evidence；H¹ₑ/BK remains open |

| `JT-ATS-PROLOGUE-OBLIGATIONS-SORRY-CONSTRUCTORS` | `Prologue/Obligations/Constructors.lean` placeholder constructors (rejected) | negative source evidence；the four constructors use `sorry` and are excluded from Scene1 | Constructors.lean:11–34; Scene1 plan §0.3/§4 and V1 no-`sorryAx` policy | rejected as inadmissible source |

| `JT-SCENE1-ACTUAL-HULL-VOLUMETRANSFER-SIGN-OBSTRUCTION` | `Scene1Input.logVolume_ne_log_actualHull`; `not_VolumeTransfer_of_actualHull_logVolume` | actual ordinary-log hull cannot fill current `VolumeTransfer.logVolume` under nonnegative weights；Scene1/Derived | `VBadThetaLogCollation.log_volume_neg` and `VolumeTransfer.transferred_volume` sign contradiction | proved negative evidence；transfer carrier/sign review required |

该单元只保留 actual saturated carrier 的非零性，不将其识别为 H¹ₑ、不提供 BK/log 比较或全局
系数映射单射。Prologue-R5→R5；derive；owner Scene1；Core 假设/退休/转入/取出增量均 0。

## S1.392：Actual global volume negative-log nonnegativity

| source-id | declaration | fidelity / boundary | model evidence | status |
| --- | --- | --- | --- | --- |
| `JT-SCENE1-PAPER-WITNESS-GLOBAL-VOLUME-NEGLOG-NONNEGATIVE` | `PaperLogWitnessHull.witness_integralHull_globalVolume_negLog_nonneg` | nonnegative negative logarithm of the actual global witness-hull volume；Scene1/Derived | S1.391 log nonpositivity and `neg_nonneg.mpr` | proved / accepted |

该定理只把 actual volume 的 log 非正性改写为 negative log 非负性，不识别论文 thetaVolume，
不构造 H¹ₑ/BK、different-untilt 或真实联合模型，也不关闭任何最终闸门。Prologue-R5→R5；
derive；owner Scene1；Core 假设/退休/转入/取出增量均 0。Checks.SceneBounds 1149/1149、
Axioms.SceneBounds 946/946 与 Scene1 聚合通过，公理仅含 `propext`、`Classical.choice`、
`Quot.sound`。一次热构建耗时 `222.46s`、峰值 RSS `8,296,312 kB`、9420 个 Lake 任务；
未冷建、清缓存或重编 Mathlib。

## S1.393：Actual global absolute-log to negative-log bridge

| source-id | declaration | fidelity / boundary | model evidence | status |
| --- | --- | --- | --- | --- |
| `JT-SCENE1-PAPER-WITNESS-GLOBAL-VOLUME-ABSLOG-NEGLOG-BRIDGE` | `PaperLogWitnessHull.witness_integralHull_globalVolume_absLog_eq_negLog` | absolute log equals negative log for the actual global witness-hull volume；Scene1/Derived | S1.391 log nonpositivity and `abs_of_nonpos` | proved / accepted |

该定理只在 actual volume 的 log 非正条件下桥接绝对对数和负对数，不识别论文 thetaVolume，
不构造 H¹ₑ/BK、different-untilt 或真实联合模型，也不关闭任何最终闸门。Prologue-R5→R5；
derive；owner Scene1；Core 假设/退休/转入/取出增量均 0。Checks.SceneBounds 1150/1150、
Axioms.SceneBounds 947/947 与 Scene1 聚合通过，公理仅含 `propext`、`Classical.choice`、
`Quot.sound`。一次热构建耗时 `223.31s`、峰值 RSS `8,296,604 kB`、9420 个 Lake 任务；
未冷建、清缓存或重编 Mathlib。

## S1.394：Actual global absolute-log reference lower bound

| source-id | declaration | fidelity / boundary | model evidence | status |
| --- | --- | --- | --- | --- |
| `JT-SCENE1-PAPER-WITNESS-GLOBAL-VOLUME-ABSLOG-REFERENCE-LOWER-BOUND` | `PaperLogWitnessHull.witness_integralHull_globalVolume_absLog_ge_mul_referenceAbsLogQ` | actual global absolute-log lower bound against reference absLogQ；Scene1/Derived | S1.386 negative-log/reference lower bound and S1.393 absolute-log/negative-log bridge | proved / accepted |

该定理不把 reference q-pilot 识别为 paper target 或 thetaVolume，不构造 H¹ₑ/BK、different-untilt
或最终 accounting，也不关闭任何最终闸门。Prologue-R5→R5；derive；owner Scene1；Core 假设/
退休/转入/取出增量均 0。前两次因声明顺序失败，修正后 Checks.SceneBounds 1151/1151、
Axioms.SceneBounds 948/948 与 Scene1 聚合通过，公理仅含 `propext`、`Classical.choice`、
`Quot.sound`。修正后三目标热构建耗时 `228.64s`、峰值 RSS `8,296,320 kB`、9420 个 Lake 任务；
本单元累计 `506.15s`。未冷建、清缓存或重编 Mathlib。

## S1.395：Actual global absolute-log strict selected-paper upper bound

| source-id | declaration | fidelity / boundary | model evidence | status |
| --- | --- | --- | --- | --- |
| `JT-SCENE1-PAPER-WITNESS-GLOBAL-VOLUME-ABSLOG-SELECTED-PAPER-UPPER-BOUND` | `PaperLogWitnessHull.witness_integralHull_globalVolume_absLog_lt_mul_selectedPaperSum` | actual global absolute-log strict upper bound against selected paper sum；Scene1/Derived | S1.385 absolute-log identity and strict full-base gap | proved / accepted |

该定理在 `0 < n` 下只消费 full-base 严格 gap，证明 actual absolute log 严格小于 selected
paper sum 的 `n` 倍；不识别论文 thetaVolume，不构造 H¹ₑ/BK、different-untilt 或真实联合
模型，也不关闭最终闸门。Prologue-R5→R5；derive；owner Scene1；Core 假设/退休/转入/取出增量均 0。
前三次证明脚手架失败已记录，修正后 Checks.SceneBounds 1152/1152、Axioms.SceneBounds 949/949
与 Scene1 聚合通过，公理仅含 `propext`、`Classical.choice`、`Quot.sound`。修正后三目标热构建
耗时 `216.59s`、峰值 RSS `8,296,384 kB`、9420 个 Lake 任务；本单元累计 `631.79s`。
未冷建、清缓存或重编 Mathlib。

## S1.406：实际 Haar 成本到有限 VolumeTransfer

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-ACTUAL-HULL-COST-TRANSFER` | `ActualHullCostTransfer.PositivePacket`, `packetHull`, `cost_eq_packetWeightSum`, `link`, `volumeTransfer`, `packetCollationHull`, `volume_eq_exp_neg_logVolume`; `actualCostLink_volumeNormalization`, `actualCostLink_transferLogBound` | S1.321 actual Haar weighted sum、S1.322 negative-log cost 和 S1.358 raw degree accounting；Joshi III 3495–3557、3634–3645。实际 packetWeight 是已构造 local Haar cost，去掉零项保持总和；collated hull 成本已纳入 packet，无额外 hull charge。ordinary-log collation 的几何条件由生产者证明。 | Scene1/Derived；proved / accepted；1173 checks、970 axiom prints 与 Scene1 聚合通过，公理仅含 Lean 标准三项 |

`ordinary_positivePacket_nonempty` 由正长度 actual cost 严格正性和有限求和证明
成本 carrier 非空，排除以全空 carrier 满足转移的退化路径。
该成本 carrier 是实际 Haar 会计适配器。它不识别论文 theta/untilt/volume，也不提供
theta/period 的真实联合满足模型；这些义务单独保留。Prologue-R5 和旧公开类型不变。

## S1.407：同一 InitialThetaData 的实际 hull/raw target 装配

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-CANONICAL-ACTUAL-HULL-DATA` | `CanonicalActualHull.length_pos`, `tuple_liesOver`, `toCanonicalInput`, `scene1Input`, `data`, `source`, `qFamily`, `qLogSum_eq_degree_mul_reference`, `volumeNormalization`, `transferLogBound`, `corollary312` | actual InitialThetaData Tate parameters/section，S1.406 Haar cost transfer，S1.358 raw degree accounting；Joshi III 1028–1055、3495–3557、3617–3645。tuple、Tate q-index/log terms、ordinary-log hull/cost 来自同一 D。一般数域 raw 次数保留。 | Scene1/Derived；proved conditional / accepted；1192 checks、989 axiom prints 与 Scene1 聚合通过；剩余 analytic laws 为显式条件 |

`AnalyticInput` 不包含 target、q-family、volume identity、transfer bound 或最终目标。
它保留 theta scaling、period/log-shell、cost/period normalization、height/perfectoid
法律，尚未从论文 theta/untilt 构造。此处不声称 VBad raw target 等于论文完整代表
处集、BK/thetaVolume 或一般数域 degree-normalized 目标，也不关闭最终闸门。

## S1.408：只接收实际 InitialThetaData 的 raw Haar 体积界

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-ACTUAL-RAW-VOLUME-BOUND` | `InitialThetaRawQ.logTerm_eq_order_term`, `logSum_eq_degree_mul_reference`, `reference_le_logSum`, `log_product_eq_neg_logSum`, `product_pow_le_actualVolume`, `negAverageAbsLog_actualVolume_ge_neg_logSum`; `CanonicalActualHull.raw_volume_bound` | actual Tate completion norm/order、residue degree、实际 finite q-pilot sum 和 ordinary-log Haar identity；Joshi III 3495–3557、3617–3645。数值定理独立于 theta/period/perfectoid/Scene1Input，保留一般数域次数。 | Scene1/Derived；proved / accepted；数值层、旧消费者、1206 checks、1003 axiom prints 和 Scene1 聚合通过，公理仅含 Lean 标准三项 |

S1.407 中的 length、section tuple、collation/cost/volume 定义移到数值模块，公开名称和
类型不变；accounting 和 Corollary312 proof term 直接消费独立数值生产者。其旧 Scene1
打包仍依赖 AnalyticInput，论文 theta/BK/untilt 及代表处/volume 身份仍未闭合。

## S1.409：饱和 Kummer ordinary-log 的满射及逆映射

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-SATURATED-KUMMER-LOG-EQUIVALENCE` | `LocalPadicLog.exists_prime_power_mul_eq_principalLog`, `saturatedImageLog_surjective`, `saturatedLogEquiv`, `saturatedExp`, `saturatedImageLog_saturatedExp`, `saturatedExp_saturatedImageLog`, `saturatedExp_eq_dividedKummerClass` | 已移植并独立证明的 `LocalPadicLogBall.exists_padicLog_eq`（原 iut PadicLog 来源和许可证见该文件头）、标准 rational Kummer p-power division；Joshi III 3212–3226。任意 y 缩入小球后实际构造单位及 divided Kummer 类。 | Scene1/Derived；proved / accepted；1214 checks、1011 axiom prints 与 Scene1 聚合通过，公理仅含 Lean 标准三项 |
| `JT-SCENE1-ACTUAL-SATURATED-EXP-WITNESS` | `PrincipalUnitKummer.saturatedExp_value_eq_normalizedSaturatedClass` | S1.364 actual saturated-log 求值与 S1.409 双侧逆；实际 ordinary witness 经逆映射回到原 normalized class。 | Scene1/Derived；proved / accepted；1214 checks、1011 axiom prints 与 Scene1 聚合通过，公理仅含 Lean 标准三项 |

该同构是实际 principal-unit Kummer 像的 p-power saturation 与局部完成域之间的加法
同构；H¹ₑ/BK 识别、ℚₚ scalar closure、连续性及论文 theta-volume 身份均继续 open。
没有从原文引入新的全局事实或将 ordinary-log 同构命名为 Bloch–Kato 同构。

## S1.410：ambient H¹ 标量作用下的饱和有理子模

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-SATURATED-KUMMER-RATIONAL-MODULE` | `LocalPadicLog.saturatedExpToRationalH1`, `saturatedExpToRationalH1_injective`, `saturatedKummerRatSubmodule`, `mem_saturatedKummerRatSubmodule_iff`, `ratCast_smul_mem_saturatedKummerImage`, `saturatedRatLogEquiv`, `saturatedRatLogEquiv_eq_imageLog` | S1.409 actual additive inverse、standard rational H¹ 的原 ℚₚ action 和 Mathlib `map_rat_smul`；Joshi III 3212–3226。restriction of scalars 后，inverse+inclusion 的 linear range 恰为既有饱和 carrier。 | Scene1/Derived；proved / accepted（有理 restriction 范围）；1221 checks、1018 axiom prints 和 Scene1 聚合通过，公理仅含 Lean 标准三项 |

只有标量环从 ℚₚ restriction 到 ℚ，原 H¹ 作用没有更换；线性 log 与旧 image log
在同一类上同值。非有理 ℚₚ scalar closure、拓扑比较、H¹ₑ/BK 及论文 volume 身份仍 open。

## S1.411：principal-unit p-adic 幂与 ordinary log 的极限公式

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-PRINCIPAL-UNIT-PADIC-POWER` | `LocalPadicLog.principal_appr_powers_cauchy`, `exists_principal_appr_power_limit`, `principalPadicPower`, `tendsto_principalPadicPower`, `norm_padicLog_sub_eq_of_dist_le`, `continuousAt_padicLog_principal`, `tendsto_padicInt_appr`, `padicLog_principalPadicPower` | actual p-power principal-unit convergence、小球 ordinary-log norm identity、Mathlib PadicInt.appr congruences；Joshi III 3212–3226。实际整数幂序列在原完成域取极限，log 标量公式使用原连续 ℚₚ action。 | Scene1/Derived；proved / accepted（单位侧）；1231 checks、1028 axiom prints 和 Scene1 聚合通过，公理仅含 Lean 标准三项 |

单位幂由实际整数幂极限定义；尚无 root-tower/cocycle 的 ℤₚ scalar comparison，
不能用此公式替代 H¹ 中的标量 closure 或 H¹ₑ/BK 身份。Prologue-R5 不变。

## S1.412：actual p-adic 幂的兼容根塔与 cocycle 比较

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-KUMMER-PADIC-POWER-TOWER` | `LocalKummer.PadicPowerTower.tail_powers_cauchy`, `correction`, `correction_principal`, `correction_zero`, `correction_step`, `tower`, `tower_ratio`, `tower_cocycle` | S1.411 actual integer-power limits、PadicInt.appr congruences 与原 RootTower；Joshi III 3190–3226。完成域中的尾指数幂极限提供 base-field correction，递推构成兼容根塔，逐坐标 ratio 对齐原 Tate padicPower。 | Scene1/Derived；proved / accepted（root tower/cocycle 范围）；1246 checks、1043 axiom prints 和 Scene1 聚合通过，公理仅含 Lean 标准三项 |

仅在原完成域取极限，Ω 不需要新增拓扑/完备性；根塔/cocycle 输入没有额外数学
certificate。尚未完成 standard H¹ scalar descent、ℚₚ closure、H¹ₑ/BK 或论文 theta 身份。

## S1.413：standard H¹ scalar descent 与实际 principal Kummer image closure

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-CONTINUOUS-H1-SCALAR` | `ContinuousH1Homogeneous.cocycle_smul_law`, `cycle_smul`, `classOf_smul` | standard homogeneous continuous cochain complex 与其原 scalar action；从 cycles 和 π 的 linearity 推出 crossed-homomorphism class scalar law。 | Scene1/Derived；proved / accepted；1254 checks、1051 axiom prints 和 Scene1 聚合通过，公理仅含 Lean 标准三项 |
| `JT-SCENE1-KUMMER-PADIC-POWER-CLASS` | `LocalKummer.PadicPowerTower.tower_padicAdditiveCocycle`, `tower_padicClass`, `tower_rationalClass`; `LocalPadicLog.principalKummerHom_principalPadicPower`, `padicInt_smul_mem_principalKummerImage` | S1.412 actual tower/cocycle、原 standardMap 半线性与 root-choice independence；Joshi III 3190–3226。image closure 的单位 preimage 为实际 principalPadicPower。 | Scene1/Derived；proved / accepted；1254 checks、1051 axiom prints 和 Scene1 聚合通过，公理仅含 Lean 标准三项 |

此处关闭 ℤₚ 标量比较，不替换 H¹ complex、类或 scalar action；ℚₚ closure、linear log、
H¹ₑ/BK、拓扑比较及论文 theta-volume 身份继续 open。

## S1.414：饱和 Kummer ℚₚ 子模与 ordinary-log 线性同构

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-SATURATED-KUMMER-PADIC-MODULE` | `LocalPadicLog.principalImagePadicSmul`, `padic_smul_mem_saturatedKummerImage`, `saturatedKummerPadicSubmodule`, `saturated_as_divided_image`, `principalImageLog_padicSmul`, `saturatedImageLog_padic_smul`, `saturatedPadicLog`, `saturatedPadicLogEquiv` | S1.411 unit log scalar formula、S1.413 actual Kummer ℤₚ comparison、既有 Qp 分母清除和 S1.409 log 双射；Joshi III 3212–3226。scalar action 始终是原 H¹ action；子模 carrier 等于原饱和子群。 | Scene1/Derived；proved / accepted；1262 checks、1059 axiom prints 和 Scene1 聚合通过，公理仅含 Lean 标准三项 |

线性 log 使用局部域既有 continuous Qp algebra action，toFun 等于旧 ordinary image log。
H¹ₑ/BK 及拓扑身份仍是独立义务；不能从本线性同构自动推断论文身份。

## S1.415：standard H¹ Hausdorff 与饱和 ordinary-log 连续线性同构

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-CONTINUOUS-H1-HAUSDORFF` | `ContinuousH1Hausdorff.evalZero`, `evalZero_injective`, `finiteDimensional_zero`, `t2_cocycles`, `boundaryRange_isClosed`, `t2_h1` | Mathlib homogeneous continuous cochains、kernel/cokernel 的原 subspace/quotient topology；单位元 evaluation 的单射使 degree zero 与 boundary range 有限维，有限维闭子空间给原 H¹ Hausdorff 性。 | Scene1/Derived；proved / accepted；两叶模块、Checks.SceneBounds 1274/1274、Axioms.SceneBounds 1071/1071 与 Scene1 聚合通过；公理仅含 propext、Classical.choice、Quot.sound |
| `JT-SCENE1-SATURATED-KUMMER-TOPOLOGY` | `LocalPadicLog.rationalH1_t2`, `saturatedPadicLogContinuousEquiv`, `saturatedPadicLogContinuousEquiv_apply`, `saturatedPadicLog_continuous`, `saturatedExpToPadicH1`, `saturatedExpToPadicH1_apply` | 实际 ULift ℚₚ 系数、S1.414 原 ambient linear log 和有限维线性映射连续性；相同 carrier 上的原 ordinary log 与 inverse 对既有拓扑连续。 | Scene1/Derived；proved / accepted；两叶模块、Checks.SceneBounds 1274/1274、Axioms.SceneBounds 1071/1071 与 Scene1 聚合通过；公理仅含 propext、Classical.choice、Quot.sound |

局部域 `[FiniteDimensional ℚₚ k]` 显式作为输入；没有搬运 H¹ 拓扑，亦没有把
T2Space 或 log 连续性作为外给证书。H¹ₑ/BK 及论文 theta/untilt/period 身份仍独立未闭合。

## S1.416：ordinary log-shell 与归一化 actual Kummer shell

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-KUMMER-LOG-SHELL` | `LocalPadicLog.logShell_padicInt_smul`, `logShellIntegralSubmodule`, `principalSaturatedClass`, `saturatedPadicLog_principalSaturatedClass`, `normalizedPrincipalSaturatedClass`, `saturatedPadicLog_normalizedPrincipalClass`, `normalizedKummerShell`, `mem_normalizedKummerShell_iff`, `normalizedKummerShellLogEquiv` | Joshi III 2843–2853、3212–3236；旧 ordinary log-shell、actual principal p-adic power 与 S1.414–415 原 saturated log。ℤₚ closure 由实际单位幂给出；shell 成员恰为 `(2p)⁻¹` 乘实际 principal Kummer 类；log 在原 topology 下限制为连续 ℤₚ 线性同构。 | Scene1/Derived；proved / accepted；三叶模块、Checks.SceneBounds 1294/1294、Axioms.SceneBounds 1091/1091 与 Scene1 聚合通过；公理仅含 propext、Classical.choice、Quot.sound |
| `JT-SCENE1-ACTUAL-KUMMER-LOG-SHELL` | `PrincipalUnitKummer.normalizedPadicClass`, `normalizedPadicClass_mem_logShell`, `normalizedShellClass`, `normalizedShellClass_log_eq_value`, `normalizedShellClass_exp_eq_class`, `normalizedPadicClass_has_paperPrincipalRepresentative` | 实际 completion 的已证 ℚₚ embedding/finite dimension/continuity 与旧 normalizedRationalClass、PaperLogWitnessHull.value。所有局部 scalar/finite/continuous 实例由实际 D 推出，无外加 comparison 证书；新适配原创，无参考代码复制。 | Scene1/Derived；proved / accepted；三叶模块、Checks.SceneBounds 1294/1294、Axioms.SceneBounds 1091/1091 与 Scene1 聚合通过；公理仅含 propext、Classical.choice、Quot.sound |
| `JT-SCENE1-KUMMER-LOG-SHELL-NORMALIZATION` | `LocalPadicLog.paperPrincipalLogShell`, `logShell_eq_paperPrincipalLogShell`, `paperPrincipalSaturatedClass`, `saturatedPadicLog_paperPrincipalClass`, `mem_normalizedKummerShell_iff_paperScale` | Joshi III 2843–2853、3160–3175、3226；p=2 时 2p=p*=4，奇 p 时 ℤₚ 中的 1/2 和实际 principal-unit 半次幂对齐两种 carrier；原 H¹ 中有实际 p*-divided principal representative。 | Scene1/Derived；proved / accepted；三叶模块、Checks.SceneBounds 1294/1294、Axioms.SceneBounds 1091/1091 与 Scene1 聚合通过；公理仅含 propext、Classical.choice、Quot.sound |

归一化沿用旧 ordinary shell 的 `2p`，并证明其 carrier 等于 p*-normalized principal-log image。
该 principal-log 表达尚未扩为全部 O* 上的 branch。该 shell 是原 saturated rational H¹ 中的实际
归一化 principal image；不据此声称其等于 integral H¹ 的像或交集、H¹ₑ 或 BK shell。
真实 period/Bcris、different-untilt、paper thetaVolume 与联合模型继续 open。

## S1.417：全部整数环单位的 log branch 与 p*-shell carrier

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-LOCAL-UNIT-PRINCIPAL-POWER` | `LocalPadicLog.unitIntegerRing`, `unitResidueField`, `unitResidueExponent`, `unitResidueExponent_pos`, `unitResidueExponent_coprime`, `integerUnit_pow_principal` | 有限剩余域乘法群、CharP 与 valuation integer ring；统一 N=#κ−1 为正且与 p 互素，全部整数环单位的 N 次幂为 principal。Joshi III 2843–2853。 | Scene1/Derived；proved / accepted；三叶模块、Checks.SceneBounds 1320/1320、Axioms.SceneBounds 1117/1117 与 Scene1 聚合通过；公理仅含 propext、Classical.choice、Quot.sound |
| `JT-SCENE1-INTEGER-UNIT-LOGARITHM` | `LocalPadicLog.integerUnit_kummer_mem_principalImage`, `integerUnitKummerHom`, `integerUnitKummerHom_surjective`, `integerUnitLog`, `integerUnitLog_of_principal`, `integerUnitLog_power_formula`, `principalToIntegerUnit`, `integerUnitKummerHom_principalToIntegerUnit`, `integerUnitLog_principalToIntegerUnit`, `integerUnitLog_has_principalRepresentative`, `integerUnitLog_continuous`, `paperIntegerUnitLogShell`, `logShell_eq_paperIntegerUnitLogShell` | 原 standard rational Kummer 类、actual principal ℤₚ power 与旧 principal image log；1/N∈ℤₚ 使全部 O* 的原 rational image 等于 principal image；连续加法 log 用固定幂公式验证，p*-scaled 全单位 image 等于旧 shell。 | Scene1/Derived；proved / accepted；三叶模块、Checks.SceneBounds 1320/1320、Axioms.SceneBounds 1117/1117 与 Scene1 聚合通过；公理仅含 propext、Classical.choice、Quot.sound |
| `JT-SCENE1-ACTUAL-COMPLETION-UNIT-LOGARITHM` | `LocalCompletion.integerResidue_finite`, `integerResidue_charP`, `unitLog`, `unitLog_of_principal`, `unitLog_power_formula`, `unitLog_continuous`, `logShell_eq_scaled_unitLog_image` | 已证实际 completion compact integer ring 与 residue-prime norm<1 给 finite/CharP 实例；全部有限处的 O* branch 与 shell 身份直接实例化，无 caller comparison 证书或参考源码复制。 | Scene1/Derived；proved / accepted；三叶模块、Checks.SceneBounds 1320/1320、Axioms.SceneBounds 1117/1117 与 Scene1 聚合通过；公理仅含 propext、Classical.choice、Quot.sound |

这里只延拓 O* 上的 log，不构造全部 k* 上带 log(p)=0 的 branch。O* 的 rational Kummer
image 相等不推出 integral H¹ 的像/交集、H¹ₑ/BK 或 period/theta/untilt 身份。

## S1.418：完整系数映射核、torsion quotient 和 actual lift 判据

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-KUMMER-COEFFICIENT-KERNEL` | `LocalKummer.Rational.padicClass_smul_eq_zero_of_coboundary`, `standardMap_eq_zero_iff_prime_power_torsion`, `standardMap_eq_iff_prime_power_difference`, `standardMap_eq_divided_iff`, `coefficientTorsion`, `mem_coefficientTorsion_iff`, `coefficientIntegralLinear`, `torsionFreeCoefficient`, `torsionFreeCoefficient_mk`, `torsionFreeCoefficient_injective` | Joshi III 3214–3236；原 standard coefficient map、S1.340 integral 代表满射、S1.343 arbitrary rational coboundary denominator clearing 与 S1.413 class scalar law。所有 integral H¹ 的 coefficient kernel 恰为 p-power torsion；原 rational action 的 restriction 给 quotient 上单射；divided-class lift iff 原 integral 类 modulo torsion 的除法。 | Scene1/Derived；proved / accepted；两叶模块、Checks.SceneBounds 1336/1336、Axioms.SceneBounds 1133/1133 与 Scene1 聚合通过；公理仅含 propext、Classical.choice、Quot.sound |
| `JT-SCENE1-ACTUAL-INTEGRAL-LIFT-CRITERION` | `PrincipalUnitKummer.integralLift_rationalClass_iff`, `integralLift_normalizedClass_iff`, `normalizedClass_has_integralLift_iff`, `torsionFreePadicClass`, `torsionFreePadicClass_map`, `torsionFreePadicClass_ne_zero` | actual padicClass、rationalClass、normalizedRationalClass 与完整 kernel/division criterion；normalized integral lift 的存在性被等价为 p*-divisibility modulo p-power torsion；actual class 在 quotient 中非零。原创适配，无参考源码复制。 | Scene1/Derived；proved / accepted；两叶模块、Checks.SceneBounds 1336/1336、Axioms.SceneBounds 1133/1133 与 Scene1 聚合通过；公理仅含 propext、Classical.choice、Quot.sound |

不宣称原 integral coefficient map 单射，也不从判据断言 actual normalized class 有 lift。
integral-image intersection、H¹ₑ/BK、period/theta/untilt 和联合模型仍需独立闭合。

## S1.419：有限根下降、integral lift 与原饱和子空间交集

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-KUMMER-FINITE-ROOT-DESCENT` | `LocalKummer.exists_root_of_class_divisibility` | Joshi III 3214–3236；任意 integral cocycle 在有限 Tate level 的 scalar 消去、H¹ coboundary equality、实际 RootTower 修正和 InfiniteGalois fixed-field descent；从 cohomological divisibility 得基域具体有限根，无 full Kummer surjectivity 假设。 | Scene1/Derived；proved / accepted；四叶模块、Checks.SceneBounds 1345/1345、Axioms.SceneBounds 1142/1142 与 Scene1 聚合通过；公理仅含 propext、Classical.choice、Quot.sound |
| `JT-SCENE1-DIVIDED-KUMMER-INTEGRAL-LIFT` | `LocalKummer.Rational.integralUnitClass`, `standardMap_integralUnitClass`, `kummerHom_pow_nsmul`, `kummer_eq_divided_of_power_root`, `exists_integralLift_dividedKummer_iff` | S1.418 kernel/division criterion 和实际有限根下降；任意非零基域元素的 divided rational Kummer 类 integral-lift iff power-root 方程在基域有解；反向构造原 integral Kummer class。 | Scene1/Derived；proved / accepted；四叶模块、Checks.SceneBounds 1345/1345、Axioms.SceneBounds 1142/1142 与 Scene1 聚合通过；公理仅含 propext、Classical.choice、Quot.sound |
| `JT-SCENE1-KUMMER-INTEGRAL-INTERSECTION` | `LocalPadicLog.integralLift_iff_mem_principalImage` | 在原 p-power saturated Kummer carrier 内，actual integral coefficient image 恰为原 principal-unit rational Kummer image；root equation 的根仍 principal 由 S1.342 已证 prime-power norm theorem 推出，保持旧 carrier/action。 | Scene1/Derived；proved / accepted；四叶模块、Checks.SceneBounds 1345/1345、Axioms.SceneBounds 1142/1142 与 Scene1 聚合通过；公理仅含 propext、Classical.choice、Quot.sound |
| `JT-SCENE1-ACTUAL-INTEGRAL-ROOT-CRITERION` | `PrincipalUnitKummer.normalizedClass_integralLift_iff_power_root`, `normalizedClass_integralLift_iff_principalImage` | actual normalizedRationalClass、实际 local completion / principal unit、p*=p^(if p=2 then 2 else 1)；将 lift 条件等价到具体基域根方程及原 principal image membership。原创，无参考源码复制。 | Scene1/Derived；proved / accepted；四叶模块、Checks.SceneBounds 1345/1345、Axioms.SceneBounds 1142/1142 与 Scene1 聚合通过；公理仅含 propext、Classical.choice、Quot.sound |

交集结论只针对原 saturated rational Kummer 子空间与原 integral coefficient image；
不识别 H¹ₑ/BK，不宣称 actual normalized class 满足这些条件；period/theta/untilt 与联合模型仍 open。

## S1.420：integral ordinary-log image 与 p*-scaled shell

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-INTEGRAL-KUMMER-LOG-LATTICE` | `LocalPadicLog.principalLogImage`, `mem_principalLogImage_iff`, `principalLogImage_bounded`, `principalLogImage_ne_bot`, `paperScale_mul_logShell_eq_principalLogImage`, `principalLogImage_subset_logShell`, `logShell_not_subset_principalLogImage`, `principalLogImage_ssubset_logShell`, `integralLift_iff_log_mem_principalLogImage`, `exists_shell_class_without_integralLift` | Joshi III 2843–2853、3226–3236；原 ordinary log image 有界非零、p* norm<1 与 S1.419 intersection。旧 shell 严格大于原 integral image 的 log，p* 乘回则恢复同一载体；存在 shell class 无 integral lift。 | Scene1/Derived；proved / accepted；三叶模块、Checks.SceneBounds 1361/1361、Axioms.SceneBounds 1158/1158 与 Scene1 聚合通过；公理仅含 propext、Classical.choice、Quot.sound |
| `JT-SCENE1-ACTUAL-INTEGRAL-SHELL-NORMALIZATION` | `LocalCompletion.principalLogImage_eq_unitLog_image`, `unitLog_image_ssubset_logShell`, `paperScale_mul_logShell_eq_unitLog_image`, `exists_shell_class_without_integralLift` | actual number-field completions 的原 full-unit log 与 S1.417 principal representative；每个有限处给 strict carrier difference 及精确 scale correction，无参考代码复制。 | Scene1/Derived；proved / accepted；三叶模块、Checks.SceneBounds 1361/1361、Axioms.SceneBounds 1158/1158 与 Scene1 聚合通过；公理仅含 propext、Classical.choice、Quot.sound |
| `JT-SCENE1-ACTUAL-INTEGRAL-LOG-CRITERION` | `PrincipalUnitKummer.normalizedClass_integralLift_iff_value_mem_principalLogImage`, `scale_value_mem_principalLogImage` | 原 actual normalizedRationalClass 与 PaperLogWitnessHull.value；integral lift iff witness 在 unscaled log image；p* 乘回的原 witness 无条件属于该 image。原创，无参考源码复制。 | Scene1/Derived；proved / accepted；三叶模块、Checks.SceneBounds 1361/1361、Axioms.SceneBounds 1158/1158 与 Scene1 聚合通过；公理仅含 propext、Classical.choice、Quot.sound |

负面结论只排除原 ordinary-log normalization 下的全载体直接等式。一般 shell 存在
不可 lift 的类，不说明特定 actual q-root witness 不可 lift；不识别 H¹ₑ/BK，不触及暂作
笔误处理的 qLogTerm 符号问题。具体 witness membership 和 period/theta/untilt 身份仍 open。

## S1.421：原 integral-log 交集拓扑与 actual Haar scale correction

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-INTEGRAL-KUMMER-LOG-TOPOLOGY` | `LocalPadicLog.integralLogSubmodule`, `smallBall_subset_integralLogSubmodule`, `integralLogSubmodule_isOpen`, `integralLogSubmodule_span_eq_top`, `integralKummerSubmodule`, `mem_integralKummerSubmodule_iff`, `integralKummerLogEquiv`, `integralKummerSubmodule_isOpen` | 原 unscaled principal-log carrier 与 ℤₚ action、small-ball 满射、p-power 清分母及原 integral coefficient image intersection；Joshi III 3227–3236。原双侧 subspace topology 上连续 ℤₚ log 同构，不通过坐标搬运拓扑。 | Scene1/Derived；proved / accepted；两叶模块、Checks.SceneBounds 1386/1386、Axioms.SceneBounds 1183/1183 与 Scene1 聚合通过；公理仅含 propext、Classical.choice、Quot.sound |
| `JT-SCENE1-ACTUAL-INTEGRAL-LOG-VOLUME` | `LocalCompletion.integralLog`, `integralLog_isCompact`, `integralLog_isOpen`, `integralLog_span_eq_top`, `integralKummer`, `integralKummer_isCompact`, `integralKummer_isOpen`, `logShell_isCompact`, `logShell_isOpen`, `integralLog_haar_pos`, `integralLog_haar_ne_top`, `logShell_haar_pos`, `logShell_haar_ne_top`, `distribHaarChar_toReal_eq_norm`, `integralLog_volume_eq_paperScale_mul_shell`, `integralLog_volume_lt_shell`, `shell_logVolume_sub_integralLog_logVolume` | actual number-field completion 的 compact integer units / continuous full-unit log、原 H¹ log homeomorphism、原 normalized Haar 和 scalar-ball/index character 公式；Joshi III 2843–2853、3227–3236。原 log image 紧开满 span，H¹ integral intersection 紧开；实际 μ(L)=‖p*‖μ(shell)>0，有限且严格更小，对数差为 −log‖p*‖。原创，无参考源码复制。 | Scene1/Derived；proved / accepted；两叶模块、Checks.SceneBounds 1386/1386、Axioms.SceneBounds 1183/1183 与 Scene1 聚合通过；公理仅含 propext、Classical.choice、Quot.sound |

紧开/full-span 不在本单元升级为已提供有限基。这里测量的是原 ordinary local carrier，
未识别 H¹ₑ/BK 或 paper thetaVolume，也不判定特定 normalized witness 的 integral membership。


## S1.422：小球原 integral lift 与 actual q-root 赋值条件

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-SMALL-LOG-INTEGRAL-LIFT` | `LocalPadicLog.smallLogUnit`, `smallLogUnit_log`, `smallLogIntegralLift`, `smallLogIntegralLift_standardMap`, `integralLift_of_saturatedLog_small`, `paperNormalizedLog_mem_principalLogImage_of_small` | 原 Banach small-ball log 满射、实际 principal unit Kummer 类、旧 saturatedExp/log 单射；‖z‖≤‖2p‖ 给实际 integral lift，其原 coefficient 像等于旧 saturatedExp(z)。Joshi III 3199–3236；原创，无参考代码复制。 | Scene1/Derived；proved / accepted；三叶模块、Checks.SceneBounds 1402/1402、Axioms.SceneBounds 1199/1199 与 Scene1 聚合通过；公理仅含 propext、Classical.choice、Quot.sound |
| `JT-SCENE1-COMPLETION-SMALL-LOG-LIFT` | `LocalCompletion.norm_le_prime_iff_qOrder_ge`, `norm_le_smallLogRadius_iff_qOrder_ge`, `paperNormalizedLog_mem_integralImage_of_qOrder`, `eventually_paperNormalizedLog_mem_integralImage` | 实际 completion 的 residue prime valuation=ramIdx、奇 p 的 norm2=1、small-log 满射与 norm powers→0；非零 contracting 参数的小球条件 iff order≥ramIdx，充分高次幂进入原 unscaled log image。Joshi III 3226–3236。 | Scene1/Derived；proved / accepted；三叶模块、Checks.SceneBounds 1402/1402、Axioms.SceneBounds 1199/1199 与 Scene1 聚合通过；公理仅含 propext、Classical.choice、Quot.sound |
| `JT-SCENE1-ACTUAL-SMALL-INTEGRAL-LIFT` | `PrincipalUnitKummer.smallLift_residueChar_odd`, `smallNormalizedIntegralLift`, `smallNormalizedIntegralLift_standardMap`, `qroot_small_iff_order_ge_ramification`, `normalizedClass_has_integralLift_of_order_ge_ramification`, `eventually_qroot_power_log_mem_integralImage` | 从 actual odd support 推 residue characteristic 奇性；用原 witness norm identity 与 saturatedExp 比较构造旧 normalizedRationalClass 的 integral lift，显式要求 q-root order≥ramIdx；高次幂结论直接适配 actual source。原创，无参考代码复制。 | Scene1/Derived；proved / accepted（显式条件范围）；三叶模块、Checks.SceneBounds 1402/1402、Axioms.SceneBounds 1199/1199 与 Scene1 聚合通过；公理仅含 propext、Classical.choice、Quot.sound |

赋值阈值是小球充分条件，不是已证明的 integral-lift 必要条件；原 q-root 只有 norm<1，
不登记原 j=1 或全部有限 theta indices 无条件 integral。高次幂结论也不代替这些有限指标。
原 shell/image 严格差异仍成立；H¹ₑ/BK、period/theta/untilt 与联合模型仍 open。


## S1.423：原 Tate 参数的 integral-lift 阈值与有限幂类

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-ACTUAL-QROOT-INTEGRAL-THRESHOLD` | `LocalCompletion.norm_le_smallLogRadius_iff_ordp_ge_one`, `PrincipalUnitKummer.baseIntegralThreshold`, `baseIntegralThreshold_pos`, `qroot_ordp_eq_baseQOrder`, `qroot_power_small_iff_baseQOrder`, `qroot_small_iff_baseQOrder`, `normalizedClass_has_integralLift_of_baseQOrder`, `finite_qroot_square_small_iff_baseQOrder` | actual q-root equation 与 canonical base ordp accounting；threshold=2ell*e_base，正 n 时小球 iff threshold≤n*baseQOrder；包含 j=1 的有限平方幂族小球测试 iff 原阈值；旧 normalized class 条件性 lift。Joshi III 3199–3236，原创。 | Scene1/Derived；proved / accepted；两叶模块、Checks.SceneBounds 1418/1418、Axioms.SceneBounds 1215/1215 与 Scene1 聚合通过；公理仅含 propext、Classical.choice、Quot.sound |
| `JT-SCENE1-ACTUAL-FINITE-POWER-INTEGRAL-LIFT` | `PrincipalUnitKummer.qroot_power_norm_le_one`, `finitePowerUnit`, `finitePowerClass`, `finitePowerClass_log`, `finitePowerClass_one`, `finitePowerClass_integralLift_iff`, `finitePowerClass_has_integralLift_of_baseQOrder`, `finitePowerClasses_have_integralLifts` | 原 completion 中 1+pStar*qroot^j 的原 saturated H¹ 类，j=1 与旧类相同；log identity、原 coefficient map integral criterion 和显式原 Tate q-order 条件下有限族 lifts。无参考源码复制。 | Scene1/Derived；proved / accepted（显式条件范围）；两叶模块、Checks.SceneBounds 1418/1418、Axioms.SceneBounds 1215/1215 与 Scene1 聚合通过；公理仅含 propext、Classical.choice、Quot.sound |

有限线性幂族在同一 completion 中构造，尚未与不同 untilt 下论文 theta classes 比较。
原始 q-order 阈值未从 actual D 无条件推出；小球阈值是充分条件，不是 lift 必要条件。
H¹ₑ/BK、paper thetaVolume 与真实联合模型仍 open。


## S1.424：原 integral image 的 normalized ordinary log 与实际 witness

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-NORMALIZED-INTEGRAL-KUMMER-LOG` | `LocalPadicLog.mem_integralLog_iff_scale_inv_mem_shell`, `integralLogToShellEquiv`, `integralLogToShellEquiv_apply`, `principalIntegralClass`, `normalizedIntegralKummerLogEquiv`, `normalizedIntegralKummerLogEquiv_apply`, `normalizedIntegralKummerLog_principal`, `normalizedIntegralKummerLog_eq_dividedClass_log` | 原 p* image identity 与原 integral H¹/log 连续同构；显式 normalized ordinary map x↦log(x)/p* 给原 integral image 到旧 shell 的连续 ℤₚ equivalence，原双侧 topology 不变；principal representative 与 divided-class log 精确比较。Joshi III 2843–2853、3226–3236。 | Scene1/Derived；proved / accepted；两叶模块、Checks.SceneBounds 1433/1433、Axioms.SceneBounds 1230/1230 与 Scene1 聚合通过；公理仅含 propext、Classical.choice、Quot.sound |
| `JT-SCENE1-ACTUAL-NORMALIZED-INTEGRAL-LOG` | `PrincipalUnitKummer.actualIntegralImageClass`, `actualIntegralImageClass_coefficient`, `actualIntegralImageClass_normalizedLog`, `finitePowerIntegralImageClass`, `finitePowerIntegralImageClass_normalizedLog`, `finitePowerIntegralImageClass_has_integralLift`, `finitePowerIntegralImageClass_divided_eq` | 原 actual padicClass 经标准 coefficient map 的像，及同域 1+pStar*qroot^j 的原 integral Kummer image；显式 normalized log 无条件给旧 witness/线性幂值，原 finitePowerClass 是除 p* 后的类。Joshi III 3190–3236，原创，无参考源码复制。 | Scene1/Derived；proved / accepted；两叶模块、Checks.SceneBounds 1433/1433、Axioms.SceneBounds 1230/1230 与 Scene1 聚合通过；公理仅含 propext、Classical.choice、Quot.sound |

本单元证明的 map 是 ordinary log/p*，未识别为 BK logarithm；原 integral image 未识别为 H¹ₑ。
缩放 log 不推出 divided rational class integral，S1.420 的原 ordinary-log 严格差异仍成立。
不同 untilt/period、paper thetaVolume 和真实联合模型仍 open。


## S1.425：ordinary 小球校准唯一性与实际原 Kummer 类比较

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-KUMMER-LOG-CALIBRATION` | `LocalPadicLog.linearLog_eq_of_smallLog_calibration`, `linearExp_inverse_eq_of_smallLog_calibration`, `normalizedRationalLog`, `normalizedRationalLog_apply`, `normalizedRationalLog_ne_ordinary`, `normalizedRationalLog_fails_smallLog_calibration` | 原 smallLogUnit 的 log=z，p^n 缩入小球和原 saturated log 单射；ℚₚ-linear log 由该校准唯一确定，线性指数同构若满足小球公式则逆为原 ordinary log；显式 log/p* 不满足同一条件。Joshi III 3212–3226，原创。 | Scene1/Derived；proved / accepted（显式校准范围）；两叶模块、Checks.SceneBounds 1443/1443、Axioms.SceneBounds 1240/1240 与 Scene1 聚合通过；公理仅含 propext、Classical.choice、Quot.sound |
| `JT-SCENE1-ACTUAL-LOG-CALIBRATION` | `PrincipalUnitKummer.originalIntegralImageClass_ordinaryLog`, `originalIntegralImageClass_normalizedRationalLog`, `calibratedLog_originalIntegralImageClass`, `ordinaryLog_originalIntegralImageClass_ne_witness` | 原 actual standardMap(padicClass) 与非零 PaperLogWitnessHull.value；ordinary/calibrated log=p*·value≠value，显式 normalized log=value；只排除指定约定的同时识别，无 actual BK 构造或参考源码复制。Joshi III 3190–3236。 | Scene1/Derived；proved / accepted；两叶模块、Checks.SceneBounds 1443/1443、Axioms.SceneBounds 1240/1240 与 Scene1 聚合通过；公理仅含 propext、Classical.choice、Quot.sound |

校准条件未被登记为 actual BK 已满足；这里没有构造 period rings 或 H¹ₑ。
S1.424 的 normalized ordinary map 保持有效，但不能在保留通常小球指数公式和原类身份时
直接作为其逆映射；BK 的指数/class/map 归一化身份仍需实际来源比较。


## S1.426：原 ordinary-log witness 的 tensor/global volume 修正

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-TENSOR-WITNESS-SCALE-VOLUME` | `LocalCompletion.Packet.normalizationDegreeVolume_singleton_pure`, `LocalCompletion.Packet.normalizationDegreeVolume_singleton_scaled` | 原 scalar determinant/normalization Haar 和 singleton pure hull；degree volume=∏‖zᵢ‖^(1/dᵢ)，逐因子乘法给精确 norm correction。Joshi III 3520–3574。 原创，无参考源码复制。 | Scene1/Derived；proved / accepted；三叶模块、Checks.SceneBounds 1483/1483、Axioms.SceneBounds 1280/1280 与 Scene1 聚合通过；公理仅含 propext、Classical.choice、Quot.sound |
| `JT-SCENE1-ACTUAL-ORDINARY-LOG-HULL-VOLUME` | `OrdinaryKummerLogHull.scalar`, `OrdinaryKummerLogHull.scalar_eq_scale_value`, `OrdinaryKummerLogHull.scalar_ne_zero`, `OrdinaryKummerLogHull.norm_scale_lt_one`, `OrdinaryKummerLogHull.norm_scalar_lt_one`, `OrdinaryKummerLogHull.witness`, `OrdinaryKummerLogHull.region`, `OrdinaryKummerLogHull.region_isCompact`, `OrdinaryKummerLogHull.degreeCorrection`, `OrdinaryKummerLogHull.degreeCorrection_pos`, `OrdinaryKummerLogHull.degreeCorrection_le_one`, `OrdinaryKummerLogHull.region_degreeVolume_eq_corrected`, `OrdinaryKummerLogHull.localCorrection`, `OrdinaryKummerLogHull.localVolume`, `OrdinaryKummerLogHull.localVolume_eq_corrected`, `OrdinaryKummerLogHull.correction`, `OrdinaryKummerLogHull.volume`, `OrdinaryKummerLogHull.correction_pos`, `OrdinaryKummerLogHull.correction_le_one`, `OrdinaryKummerLogHull.volume_eq_corrected`, `OrdinaryKummerLogHull.volume_pos`, `OrdinaryKummerLogHull.volume_le_normalized`, `OrdinaryKummerLogHull.negLog_volume_eq_normalized_add_correction`, `OrdinaryKummerLogHull.negLog_volume_eq_weightedSum_add_correction` | 原 actual Kummer ordinary log=p*·value 的 pure tensor singleton hull；既有 relative/residue 权重下 ordinaryVolume=C_n*normalizedVolume、0<C_n≤1，负对数差精确。Joshi III 3226–3236、3520–3574。 原创，无参考源码复制。 | Scene1/Derived；proved / accepted；三叶模块、Checks.SceneBounds 1483/1483、Axioms.SceneBounds 1280/1280 与 Scene1 聚合通过；公理仅含 propext、Classical.choice、Quot.sound |
| `JT-SCENE1-ACTUAL-ORDINARY-LOG-COLLATION` | `OrdinaryKummerLogHull.degreeCorrection_eq_one_pow`, `OrdinaryKummerLogHull.localCorrection_eq_one_pow`, `OrdinaryKummerLogHull.correction_eq_one_pow`, `OrdinaryKummerLogHull.correctionCost_nonneg`, `OrdinaryKummerLogHull.negLog_volume_eq_mul_correctedCost`, `OrdinaryKummerLogHull.ordinary_region_subset_collation`, `OrdinaryKummerLogHull.ordinary_collation_haar_pos_lt_top`, `OrdinaryKummerLogHull.ordinary_localVolume_le_collation`, `OrdinaryKummerLogHull.ordinary_volume_le_collation`, `OrdinaryKummerLogHull.corrected_rootProduct_pow_le_collation`, `OrdinaryKummerLogHull.ordinary_collation_volume_pos`, `OrdinaryKummerLogHull.ordinary_collation_negLog_le_corrected`, `OrdinaryKummerLogHull.ordinary_collation_absLog_le_corrected`, `OrdinaryKummerLogHull.ordinary_collation_averageAbsLog_le_correctedCost` | 重复完成域 C_n=C_1^n；原 ordinary witness membership 和 normalization containment 给真实 collation hull Haar 正有限、corrected root-product 下界及固定 correction cost 的平均 abs-log 上界。Joshi III 3624–3631。 原创，无参考源码复制。 | Scene1/Derived；proved / accepted；三叶模块、Checks.SceneBounds 1483/1483、Axioms.SceneBounds 1280/1280 与 Scene1 聚合通过；公理仅含 propext、Classical.choice、Quot.sound |

只测量原 ordinary-log block 模型，不识别 paper thetaVolume 或 BK/不同 untilt。
normalized witness 的旧体积结果保留；原类 ordinary log 的消费者必须携带显式 p* correction。
C_n=C_1^n 只针对当前重复同源 completion 的 block，不扩展为未经比较的论文 j-族。


## S1.427：实际 correction cost 的算术公式与吸收判据

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-ACTUAL-ORDINARY-LOG-CORRECTION-COST` | `OrdinaryKummerLogHull.negLog_norm_paperScale_eq_localDeg`, `OrdinaryKummerLogHull.localCorrectionCost`, `OrdinaryKummerLogHull.localCorrectionCost_pos`, `OrdinaryKummerLogHull.negLog_degreeCorrection_one`, `OrdinaryKummerLogHull.negLog_localCorrection_one`, `OrdinaryKummerLogHull.correctionCost_eq_sum`, `OrdinaryKummerLogHull.selectedPaperTerm`, `OrdinaryKummerLogHull.correctedLocalCost`, `OrdinaryKummerLogHull.correctedCost_eq_sum`, `OrdinaryKummerLogHull.selectedPaperSum_eq_sum_terms` | actual odd support p*=p，completion norm=p^(−localDeg)；单块 correction cost=d_v/f_s*log p>0、全局成本和及 corrected/selected 项的同源求和。Joshi III 3226–3236、3520–3574。 原创，无参考源码复制。 | Scene1/Derived；proved / accepted；两叶模块、Checks.SceneBounds 1502/1502、Axioms.SceneBounds 1299/1299 与 Scene1 聚合通过；公理仅含 propext、Classical.choice、Quot.sound |
| `JT-SCENE1-ACTUAL-ORDINARY-LOG-COST-ABSORPTION` | `OrdinaryKummerLogHull.sourceQOrder`, `OrdinaryKummerLogHull.sourceThreshold`, `OrdinaryKummerLogHull.arithmeticAbsorption`, `OrdinaryKummerLogHull.correctedLocalCost_eq_arithmetic`, `OrdinaryKummerLogHull.selectedPaperTerm_eq_arithmetic`, `OrdinaryKummerLogHull.correctedLocalCost_le_paperTerm_iff_arithmetic`, `OrdinaryKummerLogHull.correctedCost_le_selectedPaperSum_of_arithmetic`, `OrdinaryKummerLogHull.arithmeticAbsorption_of_small_and_degree_gap`, `OrdinaryKummerLogHull.ordinary_collation_averageAbsLog_le_selectedPaperSum` | 原 base q-order q、T=2ell*e_base 和实际局部次数给局部成本吸收 iff d_v*(T+q)≤d_s*q；逐处测试足以恢复 ordinary witness collation 的 selected paper-sum 上界，不声称实际测试无条件成立。Joshi III 3624–3631。 原创，无参考源码复制。 | Scene1/Derived；proved / accepted；两叶模块、Checks.SceneBounds 1502/1502、Axioms.SceneBounds 1299/1299 与 Scene1 聚合通过；公理仅含 propext、Classical.choice、Quot.sound |

局部测试是该局部比较的必要充分条件，全局逐处满足只是充分条件；没有排除跨处余量补偿。
尚未证明 actual D 满足测试；BK/不同 untilt/paper thetaVolume 与最终目标身份继续 open。


## S1.428：actual VBad 次数下界与放宽的 correction 吸收条件

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-ACTUAL-VBAD-ORDINARY-LOG-ABSORPTION` | `OrdinaryKummerLogHull.vbad_source_localDeg_ge_ell_mul`, `OrdinaryKummerLogHull.vbad_source_localDeg_ge_two_mul`, `OrdinaryKummerLogHull.arithmeticAbsorption_on_vbad_of_relaxed_order`, `OrdinaryKummerLogHull.arithmeticAbsorption_on_vbad_of_small`, `OrdinaryKummerLogHull.correctedLocalCost_le_paperTerm_on_vbad`, `OrdinaryKummerLogHull.correctedCost_le_selectedPaperSum_of_vbad_and_complement`, `OrdinaryKummerLogHull.ordinary_collation_averageAbsLog_le_selectedPaperSum_of_vbad` | 原 actual q-root valuation/coprimality 给 ℓ∣relativeRamification，次数塔给 d_source≥ℓ*d_moduli；因此 T≤(ℓ−1)*q 足以吸收 correction，旧 small 条件无需外给 degree-gap。VBad/补集显式分开后接完整求和及 ordinary collation。Joshi III initial theta data、3520–3574、3624–3631；原创，无参考源码复制。 | Scene1/Derived；proved / accepted；新叶模块、Checks.SceneBounds 1509/1509、Axioms.SceneBounds 1306/1306 与 Scene1 聚合通过；公理仅含 propext、Classical.choice、Quot.sound |

次数下界无新增数值假设，剩余 q-order 条件和完整 odd-support 补集测试仍显式。
不从六阶 torsion 字段跳过 q-order 证明，不把 VBad coprimality 扩到补集；BK/不同 untilt、
paper thetaVolume 与最终 raw/weighted target 身份仍 open。


## S1.429：全局算术余量与实际 singleton collation

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-ACTUAL-ORDINARY-LOG-GLOBAL-MARGIN` | `OrdinaryKummerLogHull.localArithmeticMargin`, `OrdinaryKummerLogHull.localArithmeticMargin_eq_difference`, `OrdinaryKummerLogHull.localArithmeticMargin_nonneg_iff`, `OrdinaryKummerLogHull.globalArithmeticMargin`, `OrdinaryKummerLogHull.globalArithmeticMargin_eq_difference`, `OrdinaryKummerLogHull.globalArithmeticMargin_nonneg_iff`, `OrdinaryKummerLogHull.globalArithmeticMargin_nonneg_of_local_tests`, `OrdinaryKummerLogHull.ordinary_collation_averageAbsLog_le_paperSum_of_global_margin` | 有符号算术总余量 M 的来源公式、局部/全局成本差、M≥0 的精确全局吸收测试和 arbitrary-index collation 消费者。 Joshi III 3520–3574、3624–3631；原 actual q-order/Haar 模型，原创，无参考代码复制。 | Scene1/Derived；proved / accepted；两新叶模块、Checks.SceneBounds 1527/1527、Axioms.SceneBounds 1324/1324 与 Scene1 聚合通过；公理仅含 propext、Classical.choice、Quot.sound |
| `JT-SCENE1-ACTUAL-ORDINARY-LOG-SINGLETON-CRITERION` | `OrdinaryKummerLogHull.ordinary_witness_mem_normalization`, `OrdinaryKummerLogHull.ordinarySingletonCollation`, `OrdinaryKummerLogHull.ordinarySingletonCollation_laws`, `OrdinaryKummerLogHull.ordinarySingletonCollation_region_eq`, `OrdinaryKummerLogHull.ordinarySingletonCollation_volume_eq`, `OrdinaryKummerLogHull.ordinary_volume_le_one`, `OrdinaryKummerLogHull.ordinary_averageAbsLog_eq_correctedCost`, `OrdinaryKummerLogHull.ordinarySingletonCollation_bound_iff_global_margin`, `OrdinaryKummerLogHull.all_ordinary_collations_bound_iff_global_margin`, `OrdinaryKummerLogHull.ordinarySingletonCollation_violates_bound_of_negative_margin` | actual ordinary witness 的合法 singleton collation，region/volume identity 和精确 averageAbsLog；singleton bound iff M≥0，并等价于所有满足两条 laws 的 Unit-index collation bounds；M<0 给条件性违反模型。 Joshi III 3520–3574、3624–3631；原 actual q-order/Haar 模型，原创，无参考代码复制。 | Scene1/Derived；proved / accepted；两新叶模块、Checks.SceneBounds 1527/1527、Axioms.SceneBounds 1324/1324 与 Scene1 聚合通过；公理仅含 propext、Classical.choice、Quot.sound |

M 的减法在 ℝ 中；未使用截断自然数减法忽略局部亏损。未证明实际 M 的符号。
必要充分性只针对原 ordinary block / 已列两条 collation laws；未识别论文 theta locus、
BK/不同 untilt 或最终 Corollary 3.12，也未构造 actual M<0 的反例数据。


## S1.430：实际六阶 torsion 到 selected q-root 数值下界

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-SIX-TORSION-TATE-ROOT` | `sixTorsion_card_of_rational`, `exists_sixth_root_of_rational_six_torsion` | 原 rational six-torsion 的 point-map 双射与 geometric 36 点；实际 Tate uniformization 上注入后由 residue count/root-class 修正得六次根。 Joshi III initial theta data、3190–3208；原创，无新参考代码复制。 | Scene1/Derived；proved / accepted；三新叶模块、Checks.SceneBounds 1535/1535、Axioms.SceneBounds 1332/1332 与 Scene1 聚合通过；公理仅含 propext、Classical.choice、Quot.sound |
| `JT-SCENE1-COMPLETION-QORDER-POWER` | `LocalCompletion.qOrder_dvd_of_power_root`, `LocalCompletion.qOrder_pow` | 原 completion valuation 的 exp/log 会计；n 次根给 integer q-order 被 n 整除，正次幂的 q-order 乘 n。 Joshi III initial theta data、3190–3208；原创，无新参考代码复制。 | Scene1/Derived；proved / accepted；三新叶模块、Checks.SceneBounds 1535/1535、Axioms.SceneBounds 1332/1332 与 Scene1 聚合通过；公理仅含 propext、Classical.choice、Quot.sound |
| `JT-SCENE1-ACTUAL-SELECTED-QROOT-THREE-DIVISIBILITY` | `selectedTateParameter_has_sixth_root`, `selectedQRoot_three_dvd_qOrder`, `selectedQRoot_qOrder_ge_three`, `selectedPaperTerm_ge_three_log_prime` | 实际 F→torsionField→completion 点群注入与原 selected Tate structure；六次根及 2ell root equation、ell≥5 prime 给 selected q-root order 三整除/≥3，原 selected paper term≥3log p。 Joshi III initial theta data、3190–3208；原创，无新参考代码复制。 | Scene1/Derived；proved / accepted；三新叶模块、Checks.SceneBounds 1535/1535、Axioms.SceneBounds 1332/1332 与 Scene1 聚合通过；公理仅含 propext、Classical.choice、Quot.sound |

数值下界无新增 q-order/volume 假设；仅证明 selected torsion-field completion 的六次根，
不登记 base-completion 六次根。离散 q-root order≥3 不推出≥absolute ramIdx 或 global margin≥0；
实际 BK/不同 untilt/paper thetaVolume 与最终目标身份仍未建立。


## S1.431：基域六次根下降与低 ramification 吸收

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-SIX-TORSION-DIVISOR-CARD` | `torsion_card_of_rational_six_divisor` | 原 rational six-torsion 限制到正因子 n，point-map 双射与 geometric count 给 n² 个 rational n-torsion 点。 Joshi III initial theta data、3190–3208、3520–3574、3624–3631；原创，无新参考代码复制。 | Scene1/Derived；proved / accepted；四新叶模块、Checks.SceneBounds 1546/1546、Axioms.SceneBounds 1343/1343 与 Scene1 聚合通过；公理仅含 propext、Classical.choice、Quot.sound |
| `JT-SCENE1-COMPLETION-DEGREE-ONE` | `LocalCompletion.relativeDegree_eq_one_of_finrank_eq_one`, `LocalCompletion.embedCompletion_surjective_of_finrank_eq_one` | 原 local degree sum 给次数一扩张的 relative e*f=1；实际 completion finrank=1，故完成映射满射。 Joshi III initial theta data、3190–3208、3520–3574、3624–3631；原创，无新参考代码复制。 | Scene1/Derived；proved / accepted；四新叶模块、Checks.SceneBounds 1546/1546、Axioms.SceneBounds 1343/1343 与 Scene1 聚合通过；公理仅含 propext、Classical.choice、Quot.sound |
| `JT-SCENE1-ACTUAL-BASE-TATE-SIXTH-ROOT` | `baseTateParameter_has_sixth_root`, `baseTateParameter_six_dvd_qOrder`, `baseTateParameter_qOrder_ge_six` | actual 三阶点构造 bottom-field split Tate uniformization；j 唯一性与次数一完成映射满射下降实际六次根，给完整 odd support 的 base q-order 六整除/≥6。 Joshi III initial theta data、3190–3208、3520–3574、3624–3631；原创，无新参考代码复制。 | Scene1/Derived；proved / accepted；四新叶模块、Checks.SceneBounds 1546/1546、Axioms.SceneBounds 1343/1343 与 Scene1 聚合通过；公理仅含 propext、Classical.choice、Quot.sound |
| `JT-SCENE1-ACTUAL-LOW-RAMIFICATION-ABSORPTION` | `OrdinaryKummerLogHull.relaxed_order_of_base_ramIdx_le_two`, `OrdinaryKummerLogHull.arithmeticAbsorption_on_vbad_of_base_ramIdx_le_two`, `OrdinaryKummerLogHull.correctedLocalCost_le_paperTerm_on_vbad_of_base_ramIdx_le_two`, `OrdinaryKummerLogHull.correctedCost_le_selectedPaperSum_of_low_ramification`, `OrdinaryKummerLogHull.ordinary_collation_averageAbsLog_le_selectedPaperSum_of_low_ramification` | VBad 的 base absolute ramIdx≤2 与实际 q-order≥6 给原 relaxed-order/吸收测试；全局仍保留 VBad ramification 条件和补集测试。 Joshi III initial theta data、3190–3208、3520–3574、3624–3631；原创，无新参考代码复制。 | Scene1/Derived；proved / accepted；四新叶模块、Checks.SceneBounds 1546/1546、Axioms.SceneBounds 1343/1343 与 Scene1 聚合通过；公理仅含 propext、Classical.choice、Quot.sound |

基域六次根和离散阶数≥6 是无条件 actual 结果；低 ramification 吸收是明确条件性结果。
没有从 actual D 推出普遍 ramIdx≤2 或 global margin≥0；BK/不同 untilt/paper thetaVolume 仍 open。


## S1.432：moduli ramification 条件下的实际 ordinary-log 吸收

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-ACTUAL-MODULI-RAMIFICATION-ABSORPTION` | `OrdinaryKummerLogHull.vbad_source_localDeg_ge_ell_mul_base`, `OrdinaryKummerLogHull.vbad_source_localDeg_ge_ell_mul_baseRelativeRamIdx`, `OrdinaryKummerLogHull.arithmeticAbsorption_on_vbad_of_moduli_ramIdx_le_two`, `OrdinaryKummerLogHull.correctedLocalCost_le_paperTerm_on_vbad_of_moduli_ramIdx_le_two`, `OrdinaryKummerLogHull.correctedCost_le_selectedPaperSum_of_moduli_low_ramification`, `OrdinaryKummerLogHull.globalArithmeticMargin_nonneg_of_moduli_low_ramification`, `OrdinaryKummerLogHull.ordinary_collation_averageAbsLog_le_selectedPaperSum_of_moduli_low_ramification` | 保留 actual 两级次数塔的 relative ramification，得 d_source≥ell*d_base≥ell*r*d_moduli；原 T=2*e_moduli*(ell*r) 及 actual q≥6 给 e_moduli≤2 时的吸收。全局保留补集测试，并接 M≥0 和 ordinary collation 界。Joshi III 3520–3574、3624–3631；原 local degree API 与 S1.431 base root，原创，无新参考代码复制。 | Scene1/Derived；proved / accepted；新叶模块、Checks.SceneBounds 1553/1553、Axioms.SceneBounds 1350/1350 与 Scene1 聚合通过；公理仅含 propext、Classical.choice、Quot.sound |

本结果不限制基域相对 ramification，但 moduli ramification 条件未从一般 actual D 推出；
高 moduli ramification、VBad 补集、一般 margin sign 以及 BK/untilt/paper thetaVolume 仍 open。


## S1.433：局部亏损与跨处修正成本补偿

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-ACTUAL-ORDINARY-LOG-MARGIN-DEFICIT` | `OrdinaryKummerLogHull.localArithmeticMargin_ge_neg_correctionCost`, `OrdinaryKummerLogHull.localArithmeticMargin_eq_neg_correctionCost_of_degree_eq`, `OrdinaryKummerLogHull.localArithmeticMargin_neg_of_degree_eq`, `OrdinaryKummerLogHull.not_arithmeticAbsorption_of_degree_eq`, `OrdinaryKummerLogHull.not_mem_vbad_of_degree_eq` | 全处 M_v≥−C_v；实际 d_source=d_moduli 条件给 M_v=−C_v<0 / 不吸收 / 不属于 VBad，未构造满足该次数条件的 actual D。 Joshi III 3520–3574、3624–3631；原实际 relative degree/correction API，原创，无新参考代码复制。 | Scene1/Derived；proved / accepted；两新叶模块、Checks.SceneBounds 1565/1565、Axioms.SceneBounds 1362/1362 与 Scene1 聚合通过；公理仅含 propext、Classical.choice、Quot.sound |
| `JT-SCENE1-ACTUAL-ORDINARY-LOG-COMPENSATION-BUDGET` | `OrdinaryKummerLogHull.localArithmeticMargin_ge_fifth_correctionCost_on_vbad`, `OrdinaryKummerLogHull.vbadCorrectionCost`, `OrdinaryKummerLogHull.complementCorrectionCost`, `OrdinaryKummerLogHull.five_mul_globalMargin_ge_cost_budget`, `OrdinaryKummerLogHull.globalArithmeticMargin_nonneg_of_cost_budget`, `OrdinaryKummerLogHull.correctedCost_le_selectedPaperSum_of_cost_budget`, `OrdinaryKummerLogHull.ordinary_collation_averageAbsLog_le_selectedPaperSum_of_cost_budget` | VBad 低 moduli ramification 给 M_v≥C_v/5；来源修正成本和给 5M≥C_V−5C_other，显式比较 5C_other≤C_V 取代补集逐处测试，接全局 margin/collation 消费者。 Joshi III 3520–3574、3624–3631；原实际 relative degree/correction API，原创，无新参考代码复制。 | Scene1/Derived；proved / accepted；两新叶模块、Checks.SceneBounds 1565/1565、Axioms.SceneBounds 1362/1362 与 Scene1 聚合通过；公理仅含 propext、Classical.choice、Quot.sound |

实际预算比较和 moduli ramification 条件仍 open；不宣称全局余量已无条件非负或论文 theta model 的反例。


## S1.434：修正成本覆盖与大素数来源路线严格界

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-ACTUAL-CORRECTION-COST-COVERAGE` | `OrdinaryKummerLogHull.vbadCorrectionCost_pos`, `OrdinaryKummerLogHull.complementCorrectionCost_eq_zero_iff_all_mem_vbad`, `OrdinaryKummerLogHull.complementCorrectionCost_eq_zero_iff_coverage`, `OrdinaryKummerLogHull.complementCorrectionCost_eq_zero_iff_omittedPaperSum_eq_zero`, `OrdinaryKummerLogHull.globalArithmeticMargin_pos_of_full_coverage`, `OrdinaryKummerLogHull.correctedCost_lt_selectedPaperSum_of_full_coverage`, `OrdinaryKummerLogHull.ordinary_collation_averageAbsLog_lt_selectedPaperSum_of_full_coverage` | 实际 C_V>0；C_other=0 等价于 full VBad coverage 和旧 omittedPaperSum=0。覆盖与 moduli 低分歧给 M>0 / corrected-cost 严格界和普通 collation 严格界。 Joshi III 1028–1055、Section 3、3520–3574、3624–3631；原实际 support/correction API，原创，无新参考代码复制。 | Scene1/Derived；proved / accepted；两新叶模块、Checks.SceneBounds 1577/1577、Axioms.SceneBounds 1374/1374 与 Scene1 聚合通过；公理仅含 propext、Classical.choice、Quot.sound |
| `JT-SCENE1-ACTUAL-LARGE-PRIME-ORDINARY-LOG-BOUND` | `OrdinaryKummerLogHull.vbad_moduli_coverage_of_largePrime`, `OrdinaryKummerLogHull.complementCorrectionCost_eq_zero_of_largePrime`, `OrdinaryKummerLogHull.globalArithmeticMargin_pos_of_largePrime`, `OrdinaryKummerLogHull.correctedCost_lt_selectedPaperSum_of_largePrime`, `OrdinaryKummerLogHull.ordinary_collation_averageAbsLog_lt_selectedPaperSum_of_largePrime` | 已有 maximal prime-to-ell VBad 与 ell>multiplicative residue bound 推 actual moduli full coverage / C_other=0，再消费显式 moduli 低分歧条件，给 strict margin/collation bound，无独立 coverage/budget 输入。 Joshi III 1028–1055、Section 3、3520–3574、3624–3631；原实际 support/correction API，原创，无新参考代码复制。 | Scene1/Derived；proved / accepted；两新叶模块、Checks.SceneBounds 1577/1577、Axioms.SceneBounds 1374/1374 与 Scene1 聚合通过；公理仅含 propext、Classical.choice、Quot.sound |

maximal VBad / large ell / moduli ramification 条件仍显式；仅 ordinary block，无实际 BK、不同 untilt、paper thetaVolume 或最终 target 身份结论。


## S1.435：ordinary singleton 的 reference-margin target 判据

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-ACTUAL-ORDINARY-LOG-REFERENCE-MARGIN` | `OrdinaryKummerLogHull.corollary312_iff_actual_reference_margin`, `OrdinaryKummerLogHull.not_corollary312_of_actual_reference_margin_negative` | target volume/q-sum 的显式识别下，正式 Corollary iff actual ordinary correctedCost≤reference absLogQ；反向严格不等式给 target 负面消费者。Joshi III 3617–3650；原创，无新参考代码复制。 | Scene1/Derived；proved / accepted；一新叶模块、Checks.SceneBounds 1579/1579、Axioms.SceneBounds 1376/1376 与 Scene1 聚合通过；公理仅含 propext、Classical.choice、Quot.sound |

该判据不证明 reference margin 符号，也不提供 target volume/qLogSum、BK/H¹ₑ、不同 untilt 或 paper thetaVolume 身份。


## S1.436：reference 系数与 ordinary 权重的实际比例

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-ACTUAL-REFERENCE-COEFFICIENT-ORDINARY-WEIGHT` | `OrdinaryKummerLogHull.representativeCoefficient_eq_ordinaryWeight_mul_sourceInertDeg_ratio`, `OrdinaryKummerLogHull.referenceLocalMargin`, `OrdinaryKummerLogHull.referenceLocalMargin_eq_weight_gap`, `OrdinaryKummerLogHull.referenceLocalMargin_eq_sourceInertDeg_gap`, `OrdinaryKummerLogHull.referenceLocalMargin_neg_of_sourceInertDeg_le_moduliDegree` | 精确比例和 reference margin 分解；source residue degree≤moduli global degree 时的局部负面证据。Joshi III eq:weights、3520–3574；原创，无新参考代码复制。 | Scene1/Derived；proved / accepted；一新叶模块、Checks.SceneBounds 1584/1584、Axioms.SceneBounds 1381/1381 与 Scene1 聚合通过；公理仅含 propext、Classical.choice、Quot.sound |

该结果不假设 source residue degree≤moduli global degree，也不判断一般 reference margin 符号。


## S1.437：reference margin 的全局条件性负面证据

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-ACTUAL-REFERENCE-GLOBAL-NEGATIVE-MARGIN` | `OrdinaryKummerLogHull.vbadPaperTerm_eq_selectedPaperTerm_of_coverage`, `OrdinaryKummerLogHull.referenceAbsLogQ_eq_full_coefficient_sum_of_coverage`, `OrdinaryKummerLogHull.referenceAbsLogQ_lt_correctedCost_of_coverage_of_sourceInertDeg_le` | full VBad coverage 下的 finite sum alignment；source residue degree≤moduli global degree 给全局 referenceAbsLogQ<correctedCost。Joshi III eq:weights、3520–3574；原创，无新参考代码复制。 | Scene1/Derived；proved / accepted；一新叶模块、Checks.SceneBounds 1587/1587、Axioms.SceneBounds 1384/1384 与 Scene1 聚合通过；公理仅含 propext、Classical.choice、Quot.sound |

该负面证据只针对显式 coverage/degree 条件与当前 ordinary singleton normalization；不构造 actual 反例，不判定其它路线。


## S1.438：canonical target 加权 paper-normalized q-term 连接

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-CANONICAL-TARGET-PAPER-NORMALIZED-BRIDGE` | `canonicalTateTarget_qLogSum_eq_weightedPaperNormalizedSourceQFactorLogSum`, `canonicalTateQFamily_qLogSum_eq_degree_mul_weightedPaperNormalizedSourceQFactorLogSum` | degree-one canonical bundle 的 qLogSum=同源加权 paper-normalized factor 和；一般数域 raw Tate q-family 保留 [F:ℚ] 因子，无 degree-one/full-link 输入。原 qLogSum/reference、raw normalization 和 paper factor identities 的组合。Joshi III 3617–3650；原创，无参考源码复制。 | Scene1/Derived；proved / accepted；新叶模块、Checks.SceneBounds 1589/1589、Axioms.SceneBounds 1386/1386 与 Scene1 聚合通过；公理仅含 propext、Classical.choice、Quot.sound |

这是 q-term 会计连接，未识别 unweighted representatives、BK、不同 untilt 或 paper thetaVolume；未取消 p* correction，未证明新的体积界。


## S1.439：实际加权张量区域体积与完整 descent 条件

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-LOCAL-COMPLETION-GENERAL-ALGEBRA-NORM` | `LocalCompletion.norm_algebraNorm_eq_completionNorm` | 实际收缩 norm identity 经乘法和求逆扩展到全部非零 completion scalars；无新接口假设。 | Scene1/Derived；proved / accepted |
| `JT-SCENE1-LOCAL-TENSOR-WEIGHTED-REGION-VOLUME` | `Packet.normalizedHaar_scalarLattice_eq_localDeg_product_general`, `degreeLogVolume_scalarLattice_eq_norm_sum_general`, `degreeVolume_scalarLattice_eq_norm_product_general`, `weightedRegionVolume`, `weightedRegionVolume_scalarLattice`, `exists_weighted_region_volume_iff` | 实际 determinant/Haar 公式；所有非零因子上的 weighted product 降到区域 iff weighted degree 恒定，充分方向构造实际 Haar 数值函数。Joshi III 3522–3557。 | Scene1/Derived；proved / accepted |
| `JT-SCENE1-ACTUAL-SELECTED-WEIGHTED-REGION-VOLUME` | `SelectedThetaTensor.weightedDegree_eq_moduliDegree`, `weightedRegionVolume_eq_relative_product`, `relative_region_volume_exists_iff_common_moduliDegree` | actual selected fibre；inverse relative-degree 权重的 raw-norm region function 存在 iff moduli localDeg 恒定，包含空纤维。Joshi III eq:weights。 | Scene1/Derived；proved / accepted |

三新叶模块、Checks.SceneBounds 1599/1599、Axioms.SceneBounds 1396/1396 与 Scene1 聚合通过；公理仅含 propext、Classical.choice、Quot.sound。原创，无参考源码复制。一般 D 的恒定条件、paper norm/thetaVolume、BK 和不同 untilt 仍未证明；不新增 Core 假设。


## S1.440：实际 completion Kummer 单位判据与 q-root 类分离

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-COMPLETION-KUMMER-UNIT-CRITERION` | `LocalCompletion.no_baseRootTower_of_contracting`, `norm_eq_one_of_baseRootTower`, `norm_eq_one_of_rationalKummer_eq_zero`, `normOneIntegerUnit`, `rationalKummer_mem_principalImage_of_norm_eq_one`, `rationalKummer_mem_saturated_iff_norm_eq_one` | 实际离散 valuation 的 root obstruction；rational coefficient clearing；actual finite residue units 给 norm=1 iff saturated membership。Joshi III 3190–3236。 | Scene1/Derived；proved / accepted |
| `JT-SCENE1-ACTUAL-QROOT-KUMMER-SEPARATION` | `PrincipalUnitKummer.qrootRationalKummerClass`, `qrootRationalKummerClass_not_mem_saturated`, `qrootRationalKummerClass_ne_zero`, `qrootRationalKummerClass_ne_normalizedRationalClass` | full odd support 的实际 contracting qroot 给非零、非单位饱和类，并与 existing normalized principal-unit class 区分。无需额外算术条件。 | Scene1/Derived；proved / accepted |

两新叶模块、Checks.SceneBounds 1609/1609、Axioms.SceneBounds 1406/1406 与 Scene1 聚合通过；公理仅含 propext、Classical.choice、Quot.sound。原创，无参考源码复制或新增 Core 假设；不识别 H¹ₑ/BK，不证明 ambient H¹ 满射或直和分解。


## S1.441：实际乘法 Kummer 来源的单位与赋值分解

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-COMPLETION-KUMMER-VALUATION-SPLIT` | `KummerValuation.primeUnit`, `kummer`, `valuationIndex`, `primeUnit_valuation`, `prime_norm_lt_one`, `unitsSubspace`, `correctedUnit`, `correctedUnit_norm`, `correctedUnit_kummer`, `correctedUnit_kummer_mem`, `kummer_decomposition`, `multiplicativeSpan`, `primeLine`, `unitsSubspace_le_multiplicativeSpan`, `multiplicativeSpan_eq_units_sup_primeLine`, `prime_kummer_not_mem_units`, `units_disjoint_primeLine` | actual valued(p)=exp(-e)；构造 norm-one correction 及显式 H¹ 分解。全部 multiplicative Kummer 的 ℚₚ-span=原 unit saturation + prime line，交为零；不声明 ambient H¹ 满射。Joshi III 3190–3236。 | Scene1/Derived；proved / accepted |
| `JT-SCENE1-ACTUAL-QROOT-KUMMER-VALUATION` | `PrincipalUnitKummer.qrootFieldUnit`, `qroot_valuationIndex`, `qroot_kummer_decomposition`, `qroot_correction_mem_unitSubspace` | actual full odd-support qroot 来源；integer coordinate=−qOrder，prime coefficient=qOrder/ramIdx，实际 correction 类属于原单位饱和子空间。 | Scene1/Derived；proved / accepted |

两新叶模块、Checks.SceneBounds 1630/1630、Axioms.SceneBounds 1427/1427 与 Scene1 聚合通过；公理仅含 propext、Classical.choice、Quot.sound。原创，无新参考代码复制或 Core 假设；H¹ₑ/BK、crystalline/different untilt/paper volume 身份均未推断。


## S1.442：全部 rational H¹ 的连续 integral 清分母

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-PADIC-COMPACT-DENOMINATOR` | `PadicCompact.exists_uniform_denominator`, `integralLift`, `integralLift_coe` | compact continuous Q_p image 的统一 bound 和 p^n 衰减；构造至原 Z_p 的连续函数。 | Scene1/Derived；proved / accepted |
| `JT-SCENE1-CONTINUOUS-H1-INTEGRAL-DENOMINATOR` | `LocalKummer.Rational.exists_scaled_integral_cocycle`, `exists_prime_power_integralLift`, `exists_divided_integralLift`, `span_integralCoefficientImage_eq_top` | 原 compact Galois group 与原 Tate coordinates 给完整 cocycle lift；标准 H¹ 上任意 rational class 有 p^n 倍 integral lift，原 coefficient image 的 Q_p-span=⊤。Joshi III 3214–3236。 | Scene1/Derived；proved / accepted |

两新叶模块、Checks.SceneBounds 1637/1637、Axioms.SceneBounds 1434/1434 与 Scene1 聚合通过；公理仅含 propext、Classical.choice、Quot.sound。原创，无参考源码复制或 Core 假设。尚未证明 integral Kummer 来源、ambient multiplicativeSpan=H¹ 或 H¹ₑ/BK。


## S1.443：integral Tate cocycle 的有限层基域来源

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-LOCALLY-CONSTANT-GALOIS-HILBERT90` | `GaloisCocycle.locallyConstant_hilbert90` | Krull 局部常值 cocycle 自动下降至有限 Galois 中间域；调用 Mathlib 有限 Hilbert 90，再回嵌得到原扩域 coboundary。无需给定中间域或 descent witness。 | Scene1/Derived；proved / accepted |
| `JT-SCENE1-INTEGRAL-KUMMER-FINITE-LEVEL-SOURCE` | `LocalKummer.finiteLevel_coboundary`, `finiteLevel_field_source`, `successive_roots_ratio_in_base`, `finiteLevel_sources_compatible`, `every_integralClass_finiteLevel_source` | 原 integral Tate cocycle 的每层实际基域元素和根；相邻根比值下降给模 p^n 次幂的代表元相容；标准 integral H¹ representative 消费。Joshi III 3190–3236。 | Scene1/Derived；proved / accepted |

两新叶模块、Checks.SceneBounds 1643/1643、Axioms.SceneBounds 1440/1440 与 Scene1 聚合通过；公理仅含 propext、Classical.choice、Quot.sound。原创，无参考源码复制或 Core 假设。尚未证明完整 inverse-limit Kummer 等价、ambient H¹ 的乘法来源或 H¹ₑ/BK 身份。


## S1.444：integral H¹ 的有限层检测与基域幂判据

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-INTEGRAL-KUMMER-FINITE-LEVEL-DETECTION` | `LocalKummer.tate_compactSpace`, `exists_tate_with_level`, `finiteLevelWitnesses`, `finiteLevelWitnesses_isClosed`, `finiteLevelWitnesses_decreasing`, `padicClass_eq_zero_iff_all_finiteLevels` | 原 compact Tate group 中的递减非空闭集交；每层 coboundary iff 原 integral H¹ class=0。各层见证延伸使用原 primitive generator。 | Scene1/Derived；proved / accepted |
| `JT-SCENE1-INTEGRAL-KUMMER-FINITE-SOURCE-ZERO` | `LocalKummer.padicClass_eq_zero_iff_source_powers`, `every_integralClass_has_source_zero_criterion` | S1.443 actual a_n,b_n 来源的 class=0 iff 每层 a_n 是基域 p^n 次幂；为每个 standard integral H¹ 类构造相容来源及此判据。Joshi III 3190–3236。 | Scene1/Derived；proved / accepted |

两新叶模块、Checks.SceneBounds 1651/1651、Axioms.SceneBounds 1448/1448 与 Scene1 聚合通过；公理仅含 propext、Classical.choice、Quot.sound。原创，无参考源码复制或 Core 假设。仅闭合 finite-level detection/injectivity，inverse-limit 满射、ambient multiplicativeSpan 与 H¹ₑ/BK 身份仍未证明。


## S1.445：相容基域代表元族的 integral cocycle 实现与原类重构

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-COMPATIBLE-KUMMER-SOURCE-TOWER` | `LocalKummer.CompatibleSourceTower`, `ofCompatible`, `root_ne_zero`, `ratio`, `ratio_pow_eq_one`, `ratio_succ_pow`, `ratio_mul`, `cocycle`, `cocycle_law`, `continuous_cocycle`, `continuousCocycleValue` | 基域 p^n 次幂相容代表元的修正根塔；实际代数闭包递归根提取，基域 correction 在 Galois ratio 消去，得到原连续 Tate cocycle。 | Scene1/Derived；proved / accepted |
| `JT-SCENE1-COMPATIBLE-KUMMER-SOURCE-REALIZATION` | `LocalKummer.padicClass_eq_of_same_sources`, `compatibleSourceCocycle`, `compatibleSourceCocycle_field_sources`, `compatibleSourceClass`, `compatibleSourceClass_eq_original`, `compatibleSourceClass_eq_zero_iff`, `every_integralClass_from_compatible_sources` | 同来源 representative 的 root independence；任意相容族实现为原 integral class；提取后重构等于原 class；class=0 iff 各层基域 p^n 次幂。Joshi III 3190–3236。 | Scene1/Derived；proved / accepted |

两新叶模块、Checks.SceneBounds 1669/1669、Axioms.SceneBounds 1466/1466 与 Scene1 聚合通过；公理仅含 propext、Classical.choice、Quot.sound。原创，无参考源码复制或 Core 假设。未打包 quotient inverse-limit 群同构，未证明 varying local sources 由单一 field element/Q_p-span 实现，亦未识别 H¹ₑ/BK。


## S1.446：actual Kummer classes 张成整个 rational H¹

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-TATE-FINITE-LEVEL-COORDINATE-BOUND` | `Rational.coordinate_reduction_eq_zero_of_level_one`, `norm_coefficientMap_le_prime_pow_of_level_one`, `norm_coefficientMap_sub_le_prime_pow_of_level_eq` | 原 Tate basis/mod p^n reduction 给实际 rational coefficient 的统一 norm(p)^n bound。 | Scene1/Derived；proved / accepted |
| `JT-SCENE1-KUMMER-FINITE-LEVEL-APPROXIMATION` | `LocalKummer.boundaryCocycle`, `adjustCocycle`, `adjustCocycle_class`, `exists_fieldKummer_matching_level`, `exists_fieldKummer_coordinate_approximation` | actual field source + root ratio + 原 Tate extension 构造实际 Kummer representative exact finite-level matching；无新 field source/density 证书。 | Scene1/Derived；proved / accepted |
| `JT-SCENE1-CROSSED-COCYCLE-CLASS-CONTINUITY` | `ContinuousH1Homogeneous.Crossed`, `continuous_homogeneous`, `continuous_crossed_class` | 原 compact-open cochains 与标准 homology quotient，crossed representatives→原 H¹ class 连续。 | Scene1/Derived；proved / accepted |
| `JT-SCENE1-KUMMER-CLASS-APPROXIMATION-CONVERGENCE` | `Rational.exists_kummerClass_sequence_tendsto` | 一致 coefficient bound→原 rational cocycle/H¹ 收敛，实际 Kummer classes 逼近任意 integral coefficient image。 | Scene1/Derived；proved / accepted |
| `JT-SCENE1-COMPLETION-KUMMER-SPAN` | `KummerValuation.multiplicativeSpan_finiteDimensional`, `multiplicativeSpan_isClosed`, `integralCoefficientImage_subset_multiplicativeSpan`, `multiplicativeSpan_eq_top`, `units_sup_primeLine_eq_top`, `units_primeLine_isCompl` | actual finite-dimensional completion 的 unit/prime splitting 给闭 span，逼近及 integral 清分母得原 ambient rational H¹ 全张成和 IsCompl。Joshi III 3190–3236。 | Scene1/Derived；proved / accepted |

五新叶模块、Checks.SceneBounds 1687/1687、Axioms.SceneBounds 1484/1484 与 Scene1 聚合通过；公理仅含 propext、Classical.choice、Quot.sound。原创，无参考源码复制或新增 Core 假设。单位部分尚未识别为 H¹ₑ/BK，paper volume/不同 untilt/联合模型仍缺。

## S1.447：实际 principal-unit Kummer 类进入 ambient unit subspace

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-INITIAL-THETA-PRINCIPAL-UNIT-AMBIENT-SPLIT` | `PrincipalUnitKummer.rationalClass_eq_fieldKummer`, `PrincipalUnitKummer.rationalClass_mem_unitsSubspace` | 实际 principal unit 与 field-element rational Kummer hom 的精确相等；norm-one criterion 将其置于原 unitsSubspace。Joshi III 3190–3236。 | Scene1/Derived；proved / accepted |

S1.447 不把 unitsSubspace 识别为 H¹ₑ/BK，不引入 Core 假设；paper volume、不同 untilt 和联合模型仍缺。原创，无参考源码复制。

## S1.448：实际 normalized principal-unit Kummer 类进入 ambient unit subspace

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-INITIAL-THETA-NORMALIZED-CLASS-AMBIENT-SPLIT` | `PrincipalUnitKummer.normalizedRationalClass_mem_unitsSubspace` | 实际 `normalizedRationalClass` 通过非零 `paperScale` 的标量关系回到已证明的 field-element `rationalClass`，继承 ambient completion `unitsSubspace` 成员性。消费 S1.447 的 norm-one/Kummer 结果；不识别 H¹ₑ/BK。Joshi III 3190–3236；原创，无参考源码复制。 | Scene1/Derived；proved / accepted |

S1.448 不引入 Core 假设，paper volume、不同 untilt、H¹ₑ/BK 身份和联合模型仍缺。

## S1.449：实际 normalized principal-unit 的非零 ambient unit witness

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-INITIAL-THETA-NORMALIZED-CLASS-UNIT-WITNESS` | `PrincipalUnitKummer.normalizedUnitWitness`, `PrincipalUnitKummer.normalizedUnitWitness_ne_zero` | 将 S1.448 的 ambient `unitsSubspace` 成员性与既有 normalized rational-class 非零性包装为实际非零 subtype witness。Joshi III 3190–3236；原创，无参考源码复制。 | Scene1/Derived；proved / accepted |

S1.449 只提供可消费的 ambient unit witness，不识别 H¹ₑ/BK、crystalline/Frobenius、different untilt 或 paper thetaVolume。

## S1.450：实际 normalized 类的 ambient-unit / saturated-Kummer 交集 witness

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-INITIAL-THETA-NORMALIZED-CLASS-UNIT-SATURATED-INTERSECTION` | `PrincipalUnitKummer.normalizedUnitSaturatedWitness`, `PrincipalUnitKummer.normalizedUnitSaturatedWitness_ne_zero` | 将同一实际 normalized rational class 的 ambient `unitsSubspace` 成员性与 saturated principal-Kummer 成员性放入一个合取 subtype，并保留底层类非零性。消费 S1.448、S1.449 及既有 saturated-log 结果；Joshi III 3190–3236；原创，无参考源码复制。 | Scene1/Derived；proved / accepted |

S1.450 只建立两个现有载体的实际交集 witness，不识别 H¹ₑ/BK、crystalline/Frobenius、different untilt 或 paper thetaVolume。

## S1.451：实际 q-root 类位于 normalized principal-unit 线之外

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-ACTUAL-QROOT-OUTSIDE-NORMALIZED-SPAN` | `PrincipalUnitKummer.qrootRationalKummerClass_not_mem_normalized_span` | 由 q-root 类不在 saturated Kummer image、normalized 类在该 image 且 image 对 `ℚₚ` 标量封闭，证明 q-root 类不在 normalized 类的单生成 span 中。Joshi III 3190–3236；原创，无参考源码复制。 | Scene1/Derived；proved / accepted |

S1.451 是 ambient 线性分离结果，不识别 normalized line 为 H¹ₑ/BK，不提供最终 prime-line 或 paper thetaVolume 身份。

## S1.452：原 ambient H¹ 上 log(p)=0 的普通 Kummer 对数

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-COMPLETION-AMBIENT-KUMMER-LOG` | `LocalCompletion.KummerValuation.ambientLog`, `ambientLog_unit`, `ambientLog_eq_zero_iff`, `ambientLog_prime`, `ambientLog_ker`, `ambientLog_surjective`, `ambientLog_kummer`, `ambientLog_unique` | 消费 S1.446 原 H¹ 的 unit/prime 互补分解和原 saturated ordinary log；显式选 log(p)=0，定义线性满射，核恰为 primeLine；由单位限制和 prime 值唯一确定，计算任意实际域元素 Kummer 类的 corrected-unit 公式。Joshi III 3190–3236 的局部 Kummer/log 比较背景；分支及投影构造为本工程显式选择，不冒充论文 BK 结论。原创，无参考源码复制。 | Scene1/Derived；proved / accepted |
| `JT-SCENE1-INITIAL-THETA-AMBIENT-KUMMER-LOG` | `PrincipalUnitKummer.ambientLog_normalizedRationalClass`, `ambientLog_qrootRationalKummerClass` | 在相同原 ambient H¹ 上，normalized 类映到实际 PaperLogWitnessHull.value；q-root 类映到 corrected-unit log/ramIdx。消费 S1.441、S1.447–448 及旧 normalized saturated log。保持两类及其赋值方向的区分。 | Scene1/Derived；proved / accepted |

不把 prime-zero branch 识别为 BK logarithm，不识别 H¹ₑ、不同 untilt 或 paper thetaVolume；Core 假设增量 0。

## S1.453：原 continuous H¹ 的对数/赋值拓扑坐标

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-COMPLETION-KUMMER-COORDINATES` | `KummerValuation.rationalH1_finiteDimensional`, `prime_kummer_ne_zero`, `primeLineEquiv`, `kummerCoordinates`, `kummerCoordinates_fst`, `valuationCoordinate`, `kummerCoordinates_unit`, `kummerCoordinates_prime`, `valuationCoordinate_unit`, `valuationCoordinate_prime`, `valuationCoordinate_eq_zero_iff`, `valuationCoordinate_kummer`, `kummerCoordinatesContinuousEquiv`, `ambientLog_continuous`, `valuationCoordinate_continuous`, `rationalH1_finrank` | 从 S1.446 完整原 H¹ 的 U/P 互补和 S1.452 log(p)=0 分支构造 H¹≃L[ℚₚ]k×ℚₚ；首坐标为原 ordinary log，第二坐标在 κ(p) 上为 1，核恰 U；对域元素 a 的第二坐标为 −valuationIndex(a)/ramIdx。有限维及两向连续性从原 H¹ 的商拓扑证明，不搬运拓扑。Joshi III 3190–3236 的局部比较背景；坐标构造为本工程推导，无参考源码复制。 | Scene1/Derived；proved / accepted |
| `JT-SCENE1-INITIAL-THETA-KUMMER-COORDINATES` | `PrincipalUnitKummer.valuationCoordinate_qrootRationalKummerClass`, `kummerCoordinates_normalizedRationalClass`, `rationalH1_finrank_eq_localDeg_add_one` | 实际 qroot 类第二坐标=qOrder/ramIdx；normalized 类坐标=(实际 ordinary-log value,0)；原 H¹ 维数=actual localDeg+1，完成域维数由既有原 padicAlgebra 定理派生。 | Scene1/Derived；proved / accepted |

单位子空间及 ambient H¹ 拓扑保持原定义；不识别 H¹ₑ/BK、different-untilt 或 paper thetaVolume。Core 假设增量 0。

## S1.454：真实 q-root Kummer 方向的局部对数与商比较

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-COMPLETION-TATE-KUMMER-LOG` | `KummerValuation.nonunit_valuationCoordinate_ne_zero`, `valuationCorrection_mem_units`, `units_nonunitLine_isCompl`, `tateLog`, `tateLog_unit`, `tateLog_eq_zero_iff`, `tateLog_q`, `tateLog_eq_ambientLog_sub`, `tateQuotientLogEquiv`, `tateQuotientLogEquiv_mk`, `tateLog_continuous` | 由原 H¹ 赋值坐标，任意 q∉U 的直线与 U 互补；投影后消费原普通 log，得核为 Q_p·q 的连续线性对数及 (H¹/Q_p·q)≃L[Q_p]completion。分支变换为 L_q(x)=L_0(x)−(v(x)/v(q))•L_0(q)。Joshi III 3150–3156 对 Tate/单位类的区分提供比较背景；本构造为本工程推导，不声明论文中 BK、crystalline 或 Tate 曲线上同调身份。原创，无参考源码复制。 | Scene1/Derived；proved / accepted |
原 H¹、商拓扑和实际 qroot 线的通用消费者保持；没有把 qroot 类、normalized 类或其商当成 H¹ₑ/BK；Core 假设增量 0。

### S1.455：实际 q-root Tate-log 包装的拆分消费者

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-INITIAL-THETA-QROOT-OUTSIDE-UNITS` | `PrincipalUnitKummer.qrootRationalKummerClass_not_mem_unitsSubspace` | 将实际 q-root 的 norm<1 分离证据单独封装为 ambient `unitsSubspace` 外部性证书；消费 S1.440 的 saturated Kummer norm 判据。 | Scene1/Derived；proved / accepted |
| `JT-SCENE1-INITIAL-THETA-QROOT-TATE-LOG` | `PrincipalUnitKummer.qrootClass`, `qrootTateLog`, `qrootTateLog_qroot` | 在显式非单位证书之后实例化通用 Tate-direction log；实际 q-root 方向被消去。 | Scene1/Derived；proved / accepted |
| `JT-SCENE1-INITIAL-THETA-QROOT-TATE-LOG-CONSUMERS` | `PrincipalUnitKummer.qrootTateLog_normalizedRationalClass`, `qrootTateLog_eq_zero_iff`, `normalizedRationalClass_not_mem_qroot_span`, `qrootTateLog_normalizedRationalClass_ne_zero` | normalized 类的分支值等于既有 ordinary-log witness；新证明直接消费实际 `qrootTateLog_eq_ambientLog_sub` 分支公式，并使用 normalized 类赋值为零；kernel 恰为实际 q-root 线，由 witness 非零进一步得到 normalized 类不在 q-root span 且其 Tate-log 非零。该消费者仍在 `maxHeartbeats 2000000` 下通过。 | Scene1/Derived；proved / accepted |

本单元没有把 ambient H¹、q-root 线或其商识别为 H¹ₑ/BK、crystalline、period 或 paper `thetaVolume`。

### S1.456：实际 q-root Tate-log 连续性消费者

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-INITIAL-THETA-QROOT-TATE-LOG-CONTINUOUS` | `PrincipalUnitKummer.qrootTateLog_continuous` | 将通用 `tateLog_continuous` 实例化到实际 contracting q-root；连续性来自原 ambient rational H¹ 的有限维商拓扑与显式非单位证书。保持 q-root Tate-log 为 ambient H¹ 分支，不识别 H¹ₑ/BK、period 或 paper `thetaVolume`。 | Scene1/Derived；proved / accepted |

本单元没有新增 Prologue/Core 假设，也没有改变 q-root、normalized 类和 ambient H¹ 的边界身份。

### S1.457：实际 q-root Tate-log 的通用分支桥接

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-INITIAL-THETA-QROOT-TATE-LOG-GENERIC-BRIDGE` | `PrincipalUnitKummer.qrootTateLog_as_generic`, `PrincipalUnitKummer.qrootTateLog_eq_ambientLog_sub` | 以定义等式把实际 `qrootTateLog` 暴露为通用 `KummerValuation.tateLog` 在实际 q-root 类和非单位证书上的实例；新增消费者直接复用通用分支定理，给出其在实际 q-root 上的 ambient-log/valuation-coordinate 公式，不重新展开该实际数据。公式在 `maxHeartbeats 1000000` 下通过。 | Scene1/Derived；proved / accepted |

本桥接不新增假设，不改变 q-root/normalized 类的 ambient H¹ 身份，也不提供 H¹ₑ/BK、period 或 paper `thetaVolume` 等价。

### S1.458：实际 Scene1 bundle 的 raw qLogSum/reference accounting

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-CANONICAL-TATE-SCENE1-RAW-ACCOUNTING` | `canonicalTateScene1Data_qLogSum_eq_degree_mul_reference` | 将实际 `Corollary312Scene1Data.qFamily` 直接接入既有 Tate-only raw accounting，证明当前 raw `qLogSum` 等于 `[D.F : ℚ]` 乘 reference `absLogQ`；保留一般数域次数，不识别 paper 未加权代表和 theta-volume。 | Scene1/Derived；proved / accepted |

该消费者只减少下游拆包负担，不新增 Prologue/Core 假设，也不改变 raw/degree-normalized 目标边界。

### S1.459：实际 Scene1 bundle 的 raw hull transfer 包装

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-CANONICAL-RAW-SCENE1-BUNDLE-TRANSFER` | `canonicalRawScene1Data_transferLogBound_of_actualHullVolume` | 直接消费真实 `Corollary312Scene1Data` 的 volume、q-family、normalization 和 link transfer 字段，复用 raw hull transfer 定理；`hvolume`、generator coverage、normalization containment 与 Tate-family 等式仍显式保留。 | Scene1/Derived；proved / accepted |

该包装不构造真实 paper `thetaVolume` 身份，不识别 H¹ₑ/BK，也不把条件性 actual hull 等式提升为最终 Corollary 3.12。

### S1.460：实际 Scene1 bundle 的 raw theta-volume 下界包装

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-CANONICAL-RAW-SCENE1-BUNDLE-THETAVOLUME` | `canonicalRawScene1Data_thetaVolume_ge_qProduct_of_actualHullVolume` | 将 raw hull transfer 下界直接包装到真实 `Corollary312Scene1Data`，得到 `thetaVolume ≥ qProduct`；actual hull volume、coverage、normalization 和 Tate-family 等式保持显式。 | Scene1/Derived；proved / accepted |

该结论仍是 actual hull 条件消费者，不构造论文 `thetaVolume` 身份，不识别 H¹ₑ/BK，不关闭最终 Corollary 3.12。

### S1.461：实际 Scene1 bundle 的条件性 Corollary 3.12 包装

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-CANONICAL-RAW-SCENE1-BUNDLE-COR312` | `corollary312_of_canonicalRawScene1Data_of_actualHullVolume` | 将已有 raw hull `Corollary312` 消费者直接应用于真实 `Corollary312Scene1Data`；保留 `0 < n`、`ellStar = n`、actual hull volume、coverage、normalization 和 Tate-family 等式。 | Scene1/Derived；proved / accepted |

该声明是条件性 bundle 包装，不证明真实 paper carrier、theta-volume、H¹ₑ/BK、different/untilt 或最终联合模型。

### S1.462：canonical Tate-link bundle 的条件性 Corollary 3.12 包装

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-CANONICAL-TATE-LINK-BUNDLE-COR312` | `corollary312_of_canonicalInitialThetaLink_of_actualHullVolume_fromScene1Data` | 从真实 `Corollary312Scene1Data` 自动消费 volume、Tate q-family、normalization 与 `ell` side conditions，将 canonical Tate-link 条件和 actual hull volume 条件接入既有条件性 Corollary 3.12 定理。 | Scene1/Derived；proved / accepted |

该包装仍要求 canonical link、degree-one、q-sum/paper-sum、actual hull volume 和 coverage 等外部条件；不构造论文 carrier、H¹ₑ/BK、different/untilt 或最终真实模型。

### S1.463：canonical bundle 的 theta-volume 指数桥包装

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-CANONICAL-TATE-LINK-BUNDLE-THETAVOLUME` | `canonicalScene1ThetaVolume_eq_exp_neg_procession_mul_absLogQ_fromScene1Data` | 直接消费真实 bundle 的 normalization 字段，将 canonical actual-hull volume 条件桥接为 `thetaVolume = exp (-(n * canonical absLogQ))`；canonical link、degree-one、actual hull volume 和 coverage 条件保持显式。 | Scene1/Derived；proved / accepted |

该声明不识别论文 thetaVolume、H¹ₑ/BK、different/untilt 或最终联合模型。

### S1.464：canonical bundle 的 qProduct 指数下界包装

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-CANONICAL-TATE-LINK-BUNDLE-QPRODUCT` | `canonicalScene1Exp_neg_procession_mul_absLogQ_ge_qProduct_fromScene1Data` | 将 canonical theta-volume 指数下界直接包装到真实 `Corollary312Scene1Data`，自动消费其 volume、Tate q-family、normalization 和 q-factor；canonical link、degree-one、q-sum/paper-sum、actual hull volume 与 coverage 条件保持显式。 | Scene1/Derived；proved / accepted |

该包装不构造论文 thetaVolume、H¹ₑ/BK、different/untilt 或最终联合模型。

### S1.465：canonical bundle 的 VBad 系数加权 paper-sum 包装

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-CANONICAL-VBAD-COEFFICIENT-BUNDLE` | `canonicalScene1AbsLogQ_eq_vbadCoefficientWeightedPaperSum_fromScene1Data` | 直接将 canonical q-pilot 的 `absLogQ` 接到实际 VBad 系数加权 paper-sum，自动消费真实 `Scene1Data` 的 canonical bundle 输入；保留实际 VBad carrier 和 ramification coefficient，不声称完整论文 `V_p^oss/L'` 身份。 | Scene1/Derived；proved / accepted |

该包装不识别 H¹ₑ/BK、different/untilt 或 thetaVolume，也不关闭 G3 的完整代表元与重数会计。

### S1.466：实际 q-root 与 normalized principal-unit 类的线性独立

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-INITIAL-THETA-QROOT-NORMALIZED-LINEAR-INDEPENDENT` | `PrincipalUnitKummer.qroot_normalized_linearIndependent` | 消费实际 q-root 类不在 normalized 类单生成子空间，以及 q-root 非零的既有定理，使用 Mathlib `linearIndependent_fin2` 打包为二元线性独立证书。Joshi III 3190–3236；原创，无参考源码复制。 | Scene1/Derived；proved / accepted |

该证书只说明 ambient rational H¹ 中两条实际类方向线性独立，不识别任一方向为 H¹ₑ/BK、crystalline、different untilt 或 paper thetaVolume。

### S1.467：实际 InitialTheta q-root family 的支撑与正性

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-INITIAL-THETA-QROOT-FAMILY` | `IutInitialThetaQRootFamily.badChars`, `qrootAt`, `qrootAt_ne_zero`, `qrootAt_ordp_nonneg`, `qrootAt_eq_one_of_residueChar_not_mem_badChars`, `residueChar_mem_badChars_of_mem_badFinset` | 依据 iut `ThetaLocalData`/`thetaLocalData` 的全局 family 形状，在实际 torsion-field finite places 上坏处使用现有真实 q-root，其余处使用 `1`；非零、非负 `ordp` 和坏特征支撑由实际 q-root norm/root source 派生。iut concrete local-theory carrier、completion embedding 与 root power law仍由现有 source 单独提供，未被隐藏在此定义中。 | Scene1/Derived；proved / accepted |

该生产者只提供 q-root family 的基本 carrier 条件，不声称已构造完整 `ThetaLocalData`、concrete `LocalTheory`、theta-pilot region 或 paper theta-volume。

### S1.468：q-root family 的坏特征素性与坏处幂方程

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-INITIAL-THETA-QROOT-FAMILY-POWER` | `IutInitialThetaQRootFamily.badChars_prime`, `IutInitialThetaQRootFamily.qrootAt_pow_eq_of_mem_badFinset` | 消费上一单元的实际 family 与现有 `IutTorsionQRootSource.qroot_pow_eq`，证明坏 residue characteristics 为素数，并把 `qrootAt` 在坏处还原为真实 q-root power equation。对应 iut `ThetaLocalData.badChars_prime` 与 `qroot_pow`；不构造 concrete `LocalTheory` 或全局 `ThetaLocalData`。 | Scene1/Derived；proved / accepted |

### S1.469：q-root family 的坏处严格收缩与 admissible-prime 幂方程

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-INITIAL-THETA-QROOT-FAMILY-CONTRACTION` | `IutInitialThetaQRootFamily.qrootAt_norm_lt_one_of_mem_badFinset`, `IutInitialThetaQRootFamily.qrootAt_pow_eq_admissiblePrime` | 在实际坏处 family 上复用真实 q-root 的严格范数界，并将坏处 `qrootAt` 的 `2 * ℓ` 次幂方程桥接到 `D.prime.tate` 的 admissible-prime q。普通处仍是定义性的 `1`，不把严格收缩推广到全体 finite places。 | Scene1/Derived；proved / accepted |

该单元只补足 family 的局部 contraction 与实际坏处 Tate 参数接口，不构造 concrete `LocalTheory`、完整 `ThetaLocalData`、theta-pilot region 或 paper theta-volume。

### S1.470：q-root family 的坏处标准估值等式

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-INITIAL-THETA-QROOT-FAMILY-ORDP` | `IutInitialThetaQRootFamily.qrootAt_ordp_eq_baseQOrder` | 复用实际 `PrincipalUnitKummer.qroot_ordp_eq_baseQOrder`，将坏处 `qrootAt` 的估值写成 base q-order 除以 `2 * ℓ * ramIdx`；普通处仍由 family 定义取 `1`，不声称完整 `ThetaLocalData.ordp_qroot` 的任意 base-place 版本。 | Scene1/Derived；proved / accepted |

该等式补足 actual q-root family 的局部 order accounting；paper representatives、完整 finite-place carrier、theta/untilt 和最终 volume accounting 仍保持显式未完成。

### Actual q-root family：任意下方坏处的局部法律

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-INITIAL-THETA-QROOT-FAMILY-LOCAL-LAWS` | `IutInitialThetaQRootFamily.mem_badFinset_of_liesOver`, `qrootAt_pow_eq_of_liesOver`, `qrootAt_ordp_eq_of_liesOver`, `residueChar_mem_badChars_of_liesOver`, `bad_residueChar_mem_badChars`；`Act1Scene1/IutInitialThetaQRootFamilyLocalLaws.lean` | 对实际 torsion-field 处 `v` 和任意下方实际坏处 `w`，从 `Ideal.LiesOver` 与 `w ∈ badPlacesOver(D.VBad)` 推出 family 的 `qrootAt(v)^(2ℓ) = embedF(q_w)`、`ordp(qrootAt(v)) = qOrder(w)/(2ℓ e_w)` 及两域坏剩余特征归属。对应 `refer/iut/Iut/Concrete/ThetaRegion.lean` 的 `ThetaLocalData.qroot_pow`、`ordp_qroot`、`residueChar_mem`、`bad_residueChar_mem`；Joshi III `ss:theta-data-fixing2`、`cor:cor312` 的局部 Tate 来源。证明使用本工程的处收缩唯一性、canonical completion map、真实 q-root 与 admissible-prime q-order 比较；原创证明，无参考源码复制或外部 import。 | Scene1/Derived；proved |

调用方无需提供 `w = basePlace(v)`、额外幂方程、completion-map 兼容或估值证书；新定理只消费同一 `InitialThetaData` 的已证明来源。Prologue-R5 与既有接口类型不变，Core 假设增量 0。完整 odd-support 与 `VBad` 的全局覆盖、concrete `LocalTheory`、paper theta/BK/untilt 和最终 volume 身份仍开放。

验收：新叶、`Checks.SceneBounds`、`Axioms.SceneBounds`、`Act1Scene1` 均以直接 `lake env lean -j1 -o` 热检查通过，耗时依次为 115.831、123.892、117.485、115.318 秒；进程组峰值 RSS 依次为 9,227,544、9,311,280、9,299,316、9,247,768 KiB。CPU affinity `0–13`，`LEAN_NUM_THREADS=10`，实际并发 Lean worker 峰值 1；每 0.5 秒采样进程组 RSS，85 GiB 停止线未触发。首次叶检查因 dependent place transport 类型不匹配失败（116.878 秒，9,229,524 KiB），显式运输后通过；无 heartbeat 超时，未调整上限。公理家族日志解析仅见 `propext`、`Classical.choice`、`Quot.sound`，无 `sorryAx`；未运行 Lake build 调度器，未重编译 Mathlib。

### Actual VBad q-root family：完整纤维与实际 q-pilot 会计

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-INITIAL-THETA-VBAD-QROOT-FAMILY` | `IutInitialThetaQRootFamily.vbadQrootAt`, `vbadQrootAt_ne_zero`, `vbadQrootAt_ordp_nonneg`, `vbadQrootAt_eq_one_of_residueChar_not_mem_badChars`, `vbadQrootAt_eq_qrootAt_of_liesOver`, `vbadQrootAt_pow_eq_of_liesOver`, `vbadQrootAt_ordp_eq_of_liesOver`, `qrootAt_ordp_eq_canonicalVBadRoot`, `vbadWeightedFiber`, `vbadWeightedFiber_eq_canonical`, `vbadWeightedFiber_eq_qOrderSum`, `vbadWeighted_logSum_eq_iut_absLogQ`；`Act1Scene1/IutInitialThetaVBadQRootFamily.lean` | 将同一实际 full odd-support q-root family 显式限制到 `D.VBad` 的 torsion-field 上方处，其余处取 `1`。证明非零、估值非负、有限坏特征支撑与任意下方坏处的幂方程/估值公式；通过共同 `2ℓ` 次幂证明它与 canonical VBad 根的估值相等。对每个 `p`，所有 torsion places 的无 indicator 纤维和精确等于基域 `VBad` 上的 `f_w/[F:ℚ] * qOrder(w)/(2ℓ)` 和，再接到实际 `QPilotData.absLogQ`。来源：`refer/iut/Iut/Concrete/ThetaRegion.lean` 的 `ThetaLocalData`，`Concrete/ThetaLocalConstruct/Data.lean` 的 `sum_weight_ordp_qroot`，Joshi III `ss:theta-data-fixing2` 的局部 Tate 数据；原创证明，无参考源码复制/import。 | Scene1/Derived；proved |

限制族沿用原有限 `badChars`，不要求该集合最小。原 full-support family 保留；新等式不需要 `IutOddMultiplicativeSupport D = badPlacesOver(D.VBad)`，也不推出这个覆盖条件，不删除 full-support 的额外贡献。全局次数、局部 degree 和 `2ℓ` 均沿用既有 arithmetic normalization；无需新的 degree-one、根相等或纤维会计证书。Prologue-R5、Core 与旧定理类型不变，前置信任增量 0。论文 `V_p^oss/L'` representatives、无权 paper sum、theta/BK/untilt 与最终体积身份仍开放。

验收：新叶、`Checks.SceneBounds`、`Axioms.SceneBounds`、`Act1Scene1` 直接 `lake env lean -j1 -o` 热检查均通过，耗时依次为 115.206、125.400、115.236、111.270 秒；进程组峰值 RSS 依次为 9,234,512、9,312,400、9,300,428、9,240,188 KiB。CPU affinity `0–13`，`LEAN_NUM_THREADS=10`，实际并发 Lean worker 峰值 1；每 0.5 秒采样 RSS，85 GiB 停止线未触发。首次叶检查因局部别名下的成员证据未消去限制族分支失败（112.759 秒，9,236,064 KiB），显式转换后通过；无 heartbeat 超时，未调整上限。12 个新增声明的公理输出已逐名核对，整个公理家族仅含 `propext`、`Classical.choice`、`Quot.sound`，无 `sorryAx`；未运行 Lake build 调度器，未重编译 Mathlib。

### S1.471：q-root family 的 residue-characteristic weighted fiber accounting

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-INITIAL-THETA-QROOT-FAMILY-WEIGHTED-FIBER` | `IutInitialThetaQRootFamily.qrootAtWeightedFiber`, `IutInitialThetaQRootFamily.qrootAtWeightedFiber_eq_baseQOrder` | 定义实际 torsion-field place-weighted `ordp(qrootAt)` 求和，并复用完整 odd-support q-root accounting，证明它等于 base bad-place qOrder 求和；只对实际 q-root source carrier 求和，不识别论文 `L'` representatives 或无权 representative sum。 | Scene1/Derived；proved / accepted |

该 fiber 等式覆盖 `ThetaLocalData.sum_weight_ordp_qroot` 的实际 weighted accounting 形状，但不构造 complete `ThetaLocalData` 的任意 base-place theorem、论文代表元会计或 theta-volume identity。

### S1.472：q-root family weighted log-sum 到实际 q-pilot absLogQ

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-INITIAL-THETA-QROOT-FAMILY-ABSLOGQ` | `IutInitialThetaQRootFamily.qrootAt_log_sum_eq_iut_absLogQ_of_support_eq` | 在显式 `IutOddMultiplicativeSupport D = badPlacesOver(D.VBad)` 条件下，将 family weighted fiber 的 residue-characteristic log-sum 接到实际 `ReferenceIut.QPilotData.absLogQ`；通过共同 base q-order accounting 比较 family 与 odd-support source。 | Scene1/Derived；proved / conditional |

该包装不证明 support equality，不识别论文 `L'`/`V_p^oss` representatives、无权 accounting、thetaVolume、H¹ₑ/BK 或最终 Corollary 3.12。

### S1.473：q-root family 到 canonical Scene1 q-pilot 的 absLogQ bridge

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-INITIAL-THETA-QROOT-FAMILY-CANONICAL-QPILOT` | `IutInitialThetaQRootFamily.qrootAt_log_sum_eq_canonical_qPilot_absLogQ_of_support_eq` | 将上一单元的 actual family weighted log-sum 与 canonical `toSceneQPilot.absLogQ` 的真实 `InitialThetaData` reference bridge 合并；保留 canonical link、Tate compatibility、`hEll` 和完整-support equality 为显式条件。 | Scene1/Derived；proved / conditional |

该 bridge 只连接两个实际 q-pilot数值接口，不证明 degree-one weighted normalization，不识别论文 `L'`/`V_p^oss` representatives、无权 accounting、thetaVolume、H¹ₑ/BK 或最终 Corollary 3.12。

### S1.474：q-root family 到 VBad 系数加权 paper sum

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-INITIAL-THETA-QROOT-FAMILY-VBAD-PAPER-SUM` | `IutInitialThetaQRootFamily.qrootAt_log_sum_eq_vbadCoefficientWeightedPaperSum_of_support_eq` | 将 actual q-root family 的 weighted log-sum 通过真实 `QPilotData.absLogQ` 接到已有 VBad selected paper accounting，得到实际 representatives 上带 ramification coefficient 的 paper term sum；完整 odd-support 与 VBad carrier 相等仍显式假设。 | Scene1/Derived；proved / conditional |

该结果不把系数和升级为论文无权 representative sum，不证明 support coverage、thetaVolume、H¹ₑ/BK 或最终 Corollary 3.12。

### S1.475：完整 paper sum 的 q-root family 双缺陷分解

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-QROOT-FAMILY-PAPER-SUM-DEFECT-DECOMPOSITION` | `IutInitialThetaQRootFamily.vbadRepresentativeCoefficientDefect`, `IutInitialThetaQRootFamily.fullPaperSum_eq_qrootFamilySum_add_defects_of_support_eq`, `IutInitialThetaQRootFamily.vbadRepresentativeCoefficientDefect_nonneg` | 在 full odd support 与 actual VBad pullback 相等的显式条件下，将完整 selected paper q-sum 精确拆为 actual q-root family weighted log-sum、VBad representative coefficient defect 和 omitted-support paper mass；证明系数 defect 非负。两项缺口分别对应代表元 ramification coefficient 与 VBad support omission。 | Scene1/Derived；proved / conditional |

该恒等式不消去任一缺陷，不把 q-pilot 加权和等同论文无权和；support equality、`L'`/`V_p^oss` 来源、thetaVolume 和最终 Corollary 3.12 仍未完成。

### S1.476：完整 odd-support q-root family 到 full-base q-pilot

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-INITIAL-THETA-QROOT-FAMILY-FULL-BASE` | `IutInitialThetaQRootFamily.qrootAt_log_sum_eq_fullBaseQPilotLogSum` | 无需 VBad 覆盖条件，将完整 odd multiplicative support 上的 q-root family residue-characteristic weighted log-sum 分组为 actual full-base q-pilot log sum；消费 base q-order fiber accounting 与正 Tate q-orders。 | Scene1/Derived；proved / accepted |

### S1.477：完整 support representative coefficient defect

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-QROOT-FAMILY-FULL-COEFFICIENT-DEFECT` | `IutInitialThetaQRootFamily.fullSupportRepresentativePaperTerm`, `IutInitialThetaQRootFamily.fullSupportRepresentativeCoefficientDefect`, `IutInitialThetaQRootFamily.selectedPaperSum_eq_qrootFamilySum_add_fullCoefficientDefect`, `IutInitialThetaQRootFamily.fullSupportRepresentativeCoefficientDefect_nonneg` | 在完整 odd support 上，将 selected paper q-sum 精确拆为 q-root family weighted log-sum 与完整 representative coefficient defect，并证明 defect 非负。该恒等式不要求 `VBad` 覆盖完整 support，明确保留相对 ramification/residue-degree 导致的系数损失。 | Scene1/Derived；proved / accepted |

这些结果仍不冻结 raw/degree-normalized q-factor，不识别论文 `L'`/`V_p^oss` carrier，不证明无权 representative sum、thetaVolume、H¹ₑ/BK 或最终 Corollary 3.12。

### S1.478：q-root family 到 selected paper sum 的代表系数判据

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-QROOT-FAMILY-SELECTED-SUM-COEFFICIENT-CRITERION` | `IutInitialThetaQRootFamily.qrootAt_log_sum_le_selectedPaperSum`, `IutInitialThetaQRootFamily.qrootAt_log_sum_lt_selectedPaperSum`, `IutInitialThetaQRootFamily.qrootAt_log_sum_eq_selectedPaperSum_iff_coefficients_eq_one` | 将实际 family 的完整 odd-support weighted sum 接到 full-base q-pilot sum，复用代表系数 accounting，给出 selected paper sum 的上界、由实际系数严格小于一得到的严格界，以及相等的精确充要条件。 | Scene1/Derived；proved / accepted |

这些结果不构造论文 `L'` representative 身份，也不把实际 q-pilot 权重或代表系数替换为无权 paper sum；q-factor normalization、thetaVolume 和最终 Corollary 3.12 仍未冻结。

### S1.479：full-support coefficient defect 的 residue-degree 展开

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-QROOT-FAMILY-COEFFICIENT-RESIDUE-DEGREE-FORMULA` | `IutInitialThetaQRootFamily.fullSupportRepresentativeCoefficientDefect_eq_residueDegreeFormula` | 将完整 support representative coefficient defect 展开为 `1 - ordinaryWeight * (selected source inertial/residue degree / moduli global degree)` 乘 paper term 的有限和，消费现有 actual coefficient/ordinary-weight ratio 定理。该公式保留 residue-degree 比例，不假设其等于一。 | Scene1/Derived；proved / accepted |

该展开只澄清代表元系数缺陷的算术来源，不关闭论文 carrier、无权 accounting、thetaVolume、H¹ₑ/BK 或最终 Corollary 3.12。

### S1.480：代表系数 defect 的条件性严格正性

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-QROOT-FAMILY-COEFFICIENT-DEFECT-POSITIVE` | `IutInitialThetaQRootFamily.fullSupportRepresentativeCoefficientDefect_pos_of_exists_lt_one` | 若实际 full-support representative carrier 中存在一个 coefficient 严格小于一，则证明完整 coefficient defect 严格为正；每个 paper term 的正性与其余系数的非负缺陷均显式消费。 | Scene1/Derived；proved / conditional |

该条件性结论不声称所有代表元 coefficient 都严格小于一；它只把严格 paper-sum gap 的局部充分条件公开化，不关闭 residue-degree 来源、论文 carrier、thetaVolume 或最终 Corollary 3.12。

### S1.481：由实际 VBad 非空得到 full-support defect 严格正性

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-QROOT-FAMILY-COEFFICIENT-DEFECT-VBAD-NONEMPTY` | `IutInitialThetaQRootFamily.fullSupportRepresentativeCoefficientDefect_pos_of_vbad_nonempty` | 消费 `InitialThetaData.global.bad_nonempty`、VBad 到 odd-support 的实际包含和 VBad representative coefficient 的严格小于一，得到 full-support coefficient defect 严格为正。 | Scene1/Derived；proved / accepted |

该结果只证明代表系数缺陷为正，不消除缺陷或导出论文无权和等式；residue-degree accounting、论文 carrier、thetaVolume 和最终 Corollary 3.12 仍保持开放。

### S1.482：full-support q-root family 的 selected/omitted base 分解

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-QROOT-FAMILY-SELECTED-OMITTED-BASE-DECOMPOSITION` | `IutInitialThetaQRootFamily.qrootAt_log_sum_eq_selectedWeighted_add_omitted` | 将完整 odd-support q-root family weighted log-sum 精确拆为 section-selected weighted q-root contribution 与 omitted base q-pilot contribution，消费实际 `iutInitialThetaFullBaseQPilotLogSum_eq_selected_add_omitted`。 | Scene1/Derived；proved / accepted |

该分解不假设 support coverage，也不识别 selected carrier 为论文 `L'`/`V_p^oss`；omitted contribution、residue-degree coefficients、thetaVolume、H¹ₑ/BK 和最终 Corollary 3.12 仍显式保留。

### S1.483：q-root family selected weighted 和的 coverage 判据

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-QROOT-FAMILY-COVERAGE-CRITERION` | `IutInitialThetaQRootFamily.qrootAt_log_sum_eq_selectedWeighted_of_coverage`, `IutInitialThetaQRootFamily.qrootAt_log_sum_eq_selectedWeighted_iff_coverage` | 使用 selected/omitted base 分解及实际 omitted-log-sum 零当且仅当 support coverage，给出 q-root family weighted log-sum 等于 selected weighted contribution 的充分且必要条件。 | Scene1/Derived；proved / accepted |

该判据只刻画 selected base support 是否覆盖 `IutOddMultiplicativeSupport`；它不提供 coverage，也不识别论文 `L'`/`V_p^oss`、无权 representative sum、thetaVolume、H¹ₑ/BK 或最终 Corollary 3.12。

### S1.484：large-prime 路线的 q-root family `absLogQ` bridge

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-QROOT-FAMILY-LARGE-PRIME-ABSLOGQ` | `IutInitialThetaQRootFamily.qrootAt_log_sum_eq_iut_absLogQ_of_largePrime` | 消费最大 prime-to-ell `VBad` 选择和曲线乘法支撑的有限 residue-characteristic 上界，自动得到完整 odd support 与 `badPlacesOver(VBad)` 的等式，再应用 q-root family 的 support-conditioned `absLogQ` bridge。 | Scene1/Derived；proved / conditional |

该结果只消除 support equality 的重复调用条件；`hVBad` 与 large-prime 条件仍显式保留，不识别论文 `L'`/`V_p^oss`、无权 representative sum、thetaVolume、H¹ₑ/BK 或最终 Corollary 3.12。

### S1.485：large-prime 路线的 canonical q-pilot bridge

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-QROOT-FAMILY-LARGE-PRIME-CANONICAL-BRIDGE` | `IutInitialThetaQRootFamily.qrootAt_log_sum_eq_canonical_qPilot_absLogQ_of_largePrime` | 将 large-prime 自动得到的完整 support equality 传入 canonical Scene1 q-pilot bridge，保留实际 theta/link、`QNormTateCompatibility`、`hEll` 和 canonical source 参数。 | Scene1/Derived；proved / conditional |

该结果只自动提供 support equality 的 large-prime 来源，不关闭 canonical q-pilot 的其余真实 analytic laws，也不识别论文 `L'`/`V_p^oss`、无权 representative sum、thetaVolume、H¹ₑ/BK 或最终 Corollary 3.12。

### S1.486：large-prime 路线的系数加权 paper-sum bridge

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-QROOT-FAMILY-LARGE-PRIME-VBAD-PAPER-SUM` | `IutInitialThetaQRootFamily.qrootAt_log_sum_eq_vbadCoefficientWeightedPaperSum_of_largePrime` | 将 large-prime 自动得到的完整 support equality 传入实际 `VBadSelectedPaper` 系数加权 accounting，保留 representative coefficient、paper term 和 VBad moduli carrier。 | Scene1/Derived；proved / conditional |

该结果不消除 representative coefficient defect，不产生论文无权 representative sum，也不关闭 `V_p^oss`/`L'` 来源等式、thetaVolume、H¹ₑ/BK 或最终 Corollary 3.12。

### S1.487：large-prime 路线的完整 paper-sum 双缺陷分解

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-QROOT-FAMILY-LARGE-PRIME-FULL-PAPER-DEFECTS` | `IutInitialThetaQRootFamily.fullPaperSum_eq_qrootFamilySum_add_defects_of_largePrime` | 将 large-prime 自动得到的完整 support equality 传入 full paper-sum 分解，保留 q-root family weighted sum、representative coefficient defect 和 omitted-support paper mass 三项。 | Scene1/Derived；proved / conditional |

该结果不消除任一 defect，也不把系数加权和改写为论文无权和；`V_p^oss`/`L'` 来源等式、thetaVolume、H¹ₑ/BK 和最终 Corollary 3.12 仍开放。

### S1.488：degree-one raw target 与 q-root family 的 large-prime accounting bridge

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-QROOT-FAMILY-LARGE-PRIME-RAW-QLOGSUM-DEGREE-ONE` | `IutInitialThetaQRootFamily.qrootAt_log_sum_eq_canonicalTateScene1Data_qLogSum_of_largePrime_degreeOne` | 将 large-prime q-root family `absLogQ` accounting 接到实际 canonical Tate Scene1 raw `qLogSum`，消费 raw accounting 的 `[D.F : ℚ]` 系数并显式要求 degree-one。 | Scene1/Derived；proved / conditional |

一般数域的 degree factor 未被消除；该结果不冻结 raw/degree-normalized 最终选择，也不识别论文 `L'`/`V_p^oss` representatives、thetaVolume、H¹ₑ/BK 或最终 Corollary 3.12。

### S1.489：一般数域 raw qLogSum 与 selected paper sum 的严格 degree-scaled gap

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-CANONICAL-TARGET-PAPER-SUM-DEGREE-GAP` | `canonicalTateTarget_qLogSum_lt_degree_mul_selectedPaperSum` | 将一般数域 raw qLogSum 的实际 `[D.F : ℚ]` accounting 与 canonical reference `absLogQ < selectedPaperSum` 组合，保留全局次数因子并得到严格 gap；不改变 paper carrier 或 q-factor 定义。 | Scene1/Derived；proved / conditional |

该负证据只排除当前 canonical raw accounting 与 `degree * selectedPaperSum` 的等式装配；它不决定最终 raw/degree-normalized 目标，也不识别 `V_p^oss`、`L'` representatives、thetaVolume、H¹ₑ/BK 或最终 Corollary 3.12。

### S1.490：large-prime q-root family 到一般数域 raw qLogSum 的 degree accounting

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-QROOT-FAMILY-LARGE-PRIME-RAW-QLOGSUM` | `IutInitialThetaQRootFamily.qrootAt_log_sum_mul_degree_eq_canonicalTateScene1Data_qLogSum_of_largePrime` | 将 large-prime q-root family weighted log-sum 的实际 `absLogQ` 等式与 canonical Tate raw qLogSum 的 `[D.F : ℚ]` accounting 合并，得到一般数域的 degree-scaled raw target 等式；support、Tate 对齐和 large-prime 条件保持显式。 | Scene1/Derived；proved / conditional |

该等式不去除 degree factor，不识别论文 `V_p^oss`/`L'` representatives 或无权 paper sum，也不关闭 thetaVolume、H¹ₑ/BK 或最终 Corollary 3.12。

### S1.491：一般数域 raw target 到完整 paper sum 的缩放缺陷恒等式

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-CANONICAL-RAW-TARGET-FULL-PAPER-DEFECT-ACCOUNTING` | `IutInitialThetaQRootFamily.canonicalTateScene1Data_qLogSum_add_degree_mul_paperDefects_eq_degree_mul_fullPaperSum_of_largePrime` | 合并一般数域 raw qLogSum 的 degree-scaled q-root family accounting 与 large-prime full paper-sum 双缺陷分解，精确给出 `raw qLogSum + degree * (representative coefficient defect + omitted paper mass) = degree * full paper sum`。 | Scene1/Derived；proved / conditional |

该恒等式保留两项实际缺陷与全局次数，不把当前 q-term 等同于无权 paper sum，也不关闭 q-factor 最终归一化、paper thetaVolume、H¹ₑ/BK 或 Corollary 3.12。

### S1.492：large-prime raw target 严格低于 degree-scaled full paper sum

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-CANONICAL-RAW-TARGET-FULL-PAPER-STRICT-GAP` | `IutInitialThetaQRootFamily.vbadRepresentativeCoefficientDefect_pos`, `IutInitialThetaQRootFamily.canonicalTateScene1Data_qLogSum_lt_degree_mul_fullPaperSum_of_largePrime` | 消费实际 VBad 非空带来的严格 representative coefficient defect、omitted paper mass 非负性和 S1.491 恒等式，证明 large-prime canonical raw qLogSum 严格小于 `[D.F:ℚ]` 缩放的完整 selected paper sum。 | Scene1/Derived；proved / conditional |

该严格 gap 只排除当前 canonical raw accounting 的无缺陷等式路径；它不裁决最终 q-factor 归一化，也不识别论文 representatives、thetaVolume、H¹ₑ/BK 或 Corollary 3.12。

### S1.496：canonical raw qLogSum 的 degree-normalized reference 投影

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-CANONICAL-DEGREE-NORMALIZED-QLOGSUM` | `canonicalTateScene1Data_degreeNormalized_qLogSum_eq_reference` | 将 canonical raw qLogSum 的全局次数因子除去，得到 exact reference `QPilotData.absLogQ`；该等式只描述现有 raw 与 degree-normalized 候选的关系。 | Scene1/Derived；proved / conditional |

该投影不冻结 Corollary 3.12 的最终 q-factor、paper `C_p` norm 或无权 representative 目标，也不关闭 thetaVolume、H¹ₑ/BK 和最终联合模型。

### S1.497：degree-normalized raw qLogSum 到 weighted paper-normalized source sum

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-CANONICAL-DEGREE-NORMALIZED-PAPER-QLOGSUM` | `canonicalTateQFamily_degreeNormalized_qLogSum_eq_weightedPaperNormalizedSourceQFactorLogSum` | 将一般数域 raw qLogSum 的 degree factor 除去，精确得到同一 canonical q-pilot carrier 上的 qPilot-weighted paper-normalized source-factor sum。 | Scene1/Derived；proved / conditional |

该等式保留 qPilot 权重、source carrier 与 paper-normalized local factor，不证明无权 paper representative sum，也不冻结最终 Corollary 3.12 归一化。

### S1.498：degree-normalized qLogSum 到 grouped weighted paper-normalized sum

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-CANONICAL-DEGREE-NORMALIZED-GROUPED-PAPER-QLOGSUM` | `canonicalTateQFamily_degreeNormalized_qLogSum_eq_weightedPaperNormalizedSourceQLogSum` | 将 degree-normalized canonical raw qLogSum 直接接到同一 Tate q-family 的 finite source-index grouped weighted paper-normalized sum，消费已有 source-index equivalence。 | Scene1/Derived；proved / conditional |

该 grouped bridge 保留 qPilot 权重和 paper-normalized factor，不识别无权 paper representatives 或最终 q-factor 目标。

### S1.493：canonical raw qLogSum 接入实际 ordinary-log hull volume

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-CANONICAL-RAW-QLOGSUM-ACTUAL-VOLUME` | `InitialThetaRawQ.canonicalTateScene1Data_qLogSum_eq_logSum`, `InitialThetaRawQ.canonicalTateScene1Data_exp_neg_procession_mul_qLogSum_le_actualVolume` | 将 canonical Tate raw qLogSum 与同一 `InitialThetaData` 的实际 raw completion log-sum 对齐，并消费 ordinary-log collation 的 Haar/product bound，得到 `exp(-n*qLogSum) ≤ VBadThetaLogCollation.volume`。 | Scene1/Derived；proved / conditional |

该结果连接的是 actual ordinary-log hull volume；它不把该 volume 识别为论文 thetaVolume，不引入 H¹ₑ/BK、untilt 或最终 Corollary 3.12。

### S1.494：canonical qProduct 到 actual ordinary-log hull volume

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-CANONICAL-QPRODUCT-ACTUAL-VOLUME` | `InitialThetaRawQ.canonicalTateScene1Data_qProduct_eq_exp_neg_ellStar_mul_qLogSum`, `InitialThetaRawQ.canonicalTateScene1Data_qProduct_le_actualVolume` | 用 canonical Tate q-family 的 qFactor/qLogTerm identity 将 qProduct 改写为 `exp(-ellStar*qLogSum)`，再以 `ellStar=n` 消费 actual raw volume bound，得到 qProduct 不超过 VBad ordinary-log hull volume。 | Scene1/Derived；proved / conditional |

该 qProduct 界仅针对 actual ordinary-log hull volume；论文 thetaVolume 的身份和其余 theta/BK/untilt/source obligations 仍开放。

### S1.495：actual raw volume 条件下的 canonical Scene1 Corollary 3.12 consumer

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-CANONICAL-RAW-VOLUME-COR312-CONSUMER` | `InitialThetaRawQ.corollary312_of_canonicalTateScene1Data_actualRawVolume` | 从实际 collation volume 派生 thetaVolume 正性与上界，消费 general-degree canonical qProduct-to-actual-volume bound 和真实 Scene1 side conditions，得到条件性 Corollary 3.12；只要求 Tate 对齐、length 与 actual volume identity。 | Scene1/Derived；proved / conditional |

实际 `thetaVolume = VBadThetaLogCollation.volume` 仍是输入条件；该消费者不构造 paper theta/BK/untilt volume，也不关闭真实联合模型闸门。

### S1.499：actual canonical bundle 的 degree-normalized grouped paper bridge

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-CANONICAL-ACTUAL-HULL-DEGREE-NORMALIZED-PAPER-BRIDGE` | `CanonicalActualHull.degreeNormalized_qLogSum_eq_weightedPaperNormalizedSourceQLogSum`；`Act1Scene1/IutInitialThetaCanonicalActualHullData.lean` | 将同一 `InitialThetaData` 构造的 actual `CanonicalActualHull.data` 与其 canonical Tate q-family 的 raw qLogSum 除以全局次数，直接接到 grouped weighted paper-normalized source sum。消费 S1.498 的 source-index accounting 和 actual bundle 的 canonical Tate/link 对齐；保留 qPilot 权重、source carrier、paper normalization、theta/volume analytic inputs 及无权 representative 身份义务。 | Scene1/Derived；proved / conditional |

该桥只把已证明的归一化会计接入 actual canonical bundle，不识别论文 `V_p^oss`/`L'`、无权 representative sum 或 paper `thetaVolume`，也不关闭 H¹ₑ/BK、different/untilt 和最终 Corollary 3.12。

### S1.500：actual canonical bundle 的 degree-normalized reference bridge

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-CANONICAL-ACTUAL-HULL-DEGREE-NORMALIZED-REFERENCE` | `CanonicalActualHull.degreeNormalized_qLogSum_eq_reference`；`Act1Scene1/IutInitialThetaCanonicalActualHullData.lean` | 将 actual `CanonicalActualHull.data` 的 raw qLogSum 除以 `[D.F : ℚ]`，消费同一实际 Tate/q-root accounting 得到 reference `QPilotData.absLogQ`。该结果只固定 global degree coefficient 的投影，不改变 raw target 或 paper representative 语义。 | Scene1/Derived；proved / conditional |

该桥不冻结最终 q-factor，不识别论文 `V_p^oss`/`L'`、无权 representative sum 或 paper `thetaVolume`，也不关闭 H¹ₑ/BK、different/untilt 和最终 Corollary 3.12。

### S1.501：actual canonical bundle 的 qProduct-hull volume consumer

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-CANONICAL-ACTUAL-HULL-QPRODUCT-VOLUME` | `CanonicalActualHull.qProduct_le_hullVolume`；`Act1Scene1/IutInitialThetaCanonicalActualHullData.lean` | 将 generic canonical qProduct-to-actual-volume inequality具体化到 actual bundle 固定的 `length D`、section tuple、LiesOver 证明和 `hullVolume D`，直接得到 actual qProduct 的 hull-volume 上界。 | Scene1/Derived；proved / conditional |

该消费者不把 `hullVolume` 识别为论文 `thetaVolume`，不构造 paper representatives、H¹ₑ/BK 或 different/untilt，也不关闭最终 Corollary 3.12。

### S1.502：actual canonical bundle 的 thetaVolume-qProduct consumer

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-CANONICAL-ACTUAL-HULL-THETAVOLUME-QPRODUCT` | `CanonicalActualHull.thetaVolume_ge_qProduct`；`Act1Scene1/IutInitialThetaCanonicalActualHullData.lean` | 消费 actual bundle 的 `data_thetaVolume_eq` 和 S1.501 的 hull-volume bound，将固定的 actual `thetaVolume` 直接接到同一 qProduct。 | Scene1/Derived；proved / conditional |

该消费者仍只涉及 actual ordinary-log hull；不识别论文 `thetaVolume`、H¹ₑ/BK、different/untilt 或论文 representatives，也不单独关闭最终 Corollary 3.12。

### S1.503：actual canonical bundle 的 transfer-to-Corollary consumer

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-CANONICAL-ACTUAL-HULL-COR312-CONSUMER` | `CanonicalActualHull.corollary312_of_transferLogBound`；`Act1Scene1/IutInitialThetaCanonicalActualHullData.lean` | 消费 actual bundle 已构造的 volume normalization、transfer log bound、q-family 和真实 `ell` side conditions，应用 generic transfer-to-qProduct-to-Corollary theorem 得到 actual `Corollary312`。该 consumer 不证明 `AnalyticInput` 的 theta/perfectoid 来源或论文 volume 身份；它把现有条件性 analytic laws 接入最终 target。 | Scene1/Derived；proved / conditional |

该结论仍依赖 `CanonicalActualHull.AnalyticInput` 提供的显式 theta/period/perfectoid 与 volume-transfer contracts，不把它们升级为真实论文来源，也不关闭四个形式冻结闸门。

### Actual tensor factor automorphisms 与有限像并集

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-LOCAL-TENSOR-FACTOR-INDETERMINACY` | `LocalCompletion.Packet.factorTensorMap`, `factorTensorMap_tprod`, `factorTensorMap_bijective`, `factorTensorAut`, `factorTensorMap_refl`, `factorTensorAut_continuous`, `factorTensorAut_image_normalization`, `factorIndeterminacies`, `factorIndeterminacies_finite`, `id_mem_factorIndeterminacies`, `continuous_of_mem_factorIndeterminacies`, `factorIndeterminacyOrbit`, `subset_factorIndeterminacyOrbit`, `factorIndeterminacyOrbit_isCompact`, `factorIndeterminacyOrbit_haar_pos_lt_top`, `factorIndeterminacyOrbit_normalization`；`Act1Scene1/LocalCompletionTensorIndeterminacy.lean` | 适配 `refer/iut/Iut/Concrete/LocalConstruct/Indeterminacy.lean` 的 tensor map/identity 与 `ThetaAdmissible.lean` 的 finite factor automorphisms/compact union 证明。两文件原提交 `b76207ab8955e68a7408d5d2a770b75a30c3bebf`，快照 `07cb1da58f6d428a670dbb5dd6093d428bcbcdd8`，Git 作者 Christian Merten、文件作者与版权 The iut contributors（2026），Apache-2.0 已逐文件审查并保留通知。使用本工程 actual completion Packet、原 tensor 拓扑与 normalization；Mathlib `PiTensorProduct.congr` 证明双射，并由实际 integral closure 证明 normalization 的像等式。 | Scene1/Derived；proved |
| `JT-SCENE1-LOCAL-TENSOR-FACTOR-ORBIT-REGION` | `LocalCompletion.Packet.factorOrbitScalarRegion`, `scalarNormalization_subset_factorOrbitScalarRegion`, `pure_mem_factorOrbitScalarRegion`, `factorOrbitScalarRegion_isCompact`, `factorOrbitScalarRegion_haar_pos_lt_top`, `factorOrbitScalarRegion_subset_normalization`；`Act1Scene1/LocalCompletionTensorIndeterminacyRegion.lean` | 本地消费者：将有限自同构像并集应用到 actual `scalarNormalization z hz`，从已有 determinant/Haar 结果推出紧性和正有限 normalization Haar，并在 `∀ i, ‖z i‖ ≤ 1` 下证明整个并集位于 normalization。对应参考 `ThetaAdmissible.theta_admissible` / `ThetaRegion.thetaFinite` 的局部 container 形状；此消费者无额外参考代码复制。 | Scene1/Derived；proved |

该有限自同构族仅由各实际完成域的 `ℚ_p`-代数自同构产生；不将它识别为论文全部 Ind1–Ind3，也不将该并集识别为 Joshi `theta_M^I`。新消费者不要求紧性、admissibility、Haar 正性或 normalization-containment 证书；这些结论从已有 actual scalars 和实际 tensor/measure 构造得出。无新的 Prologue 字段，Core 假设增量 0，Prologue-R5 与旧定理类型不变。参考工程未成为依赖，未导入 `refer/iut`；许可证登记见 `LICENSES.md` 的同名条目。

验收：两个新叶、`Checks.SceneBounds`、`Axioms.SceneBounds` 与 `Act1Scene1` 共 5 个直接 Lean 热检查任务均首次通过，耗时依次为 68.347、67.822、123.448、115.863、113.690 秒；进程组峰值 RSS 依次为 5,487,224、5,485,328、9,314,164、9,302,072、9,247,172 KiB。全部使用 CPU affinity `0–13`、`LEAN_NUM_THREADS=10`、Lean `-j1`；实际并发 worker 峰值 1，每 0.5 秒采样进程组 RSS，未触发 85 GiB 停止线。22 个新公开声明已逐名核对公理输出，整个公理家族仅含 `propext`、`Classical.choice`、`Quot.sound`，无 `sorryAx`；无 heartbeat 超时或上限调整，未运行 Lake build 调度器，未重编译 Mathlib。

### Actual InitialThetaData 的指定因子平方幂区域

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-INITIAL-THETA-FINITE-FACTOR-REGION` | `IutInitialThetaFiniteFactorRegion.qrootAt_norm_le_one`, `IutInitialThetaFiniteFactorRegion.vbadQrootAt_norm_le_one`, `IutInitialThetaFiniteFactorRegion.scalars`, `IutInitialThetaFiniteFactorRegion.scalars_distinguished`, `IutInitialThetaFiniteFactorRegion.scalars_other`, `IutInitialThetaFiniteFactorRegion.scalars_ne_zero`, `IutInitialThetaFiniteFactorRegion.scalars_norm_le_one`, `IutInitialThetaFiniteFactorRegion.scaleElt`, `IutInitialThetaFiniteFactorRegion.scaleElt_eq_singleAlgHom`, `IutInitialThetaFiniteFactorRegion.scaleElt_isUnit`, `IutInitialThetaFiniteFactorRegion.region`, `IutInitialThetaFiniteFactorRegion.region_eq_orbit_principalRegion`, `IutInitialThetaFiniteFactorRegion.scaleElt_mem_region`, `IutInitialThetaFiniteFactorRegion.region_isCompact`, `IutInitialThetaFiniteFactorRegion.region_haar_pos_lt_top`, `IutInitialThetaFiniteFactorRegion.region_subset_normalization`, `IutInitialThetaFiniteFactorRegion.scalars_eq_one_of_not_bad`, `IutInitialThetaFiniteFactorRegion.scaleElt_eq_one_of_not_bad`, `IutInitialThetaFiniteFactorRegion.region_eq_normalization_of_not_bad`, `IutInitialThetaFiniteFactorRegion.distinguished_ordp_eq_of_liesOver`；`Act1Scene1/IutInitialThetaFiniteFactorRegion.lean` | 消费同一 actual `InitialThetaData` 的 `vbadQrootAt`、actual completion Packet 及有限 factor-automorphism orbit。参考 `refer/iut/Iut/Concrete/ThetaRegion.lean` 的 `ThetaLocalData.distinguished`、`scaleElt`、`isUnit_scaleElt`、`thetaFinite`、`thetaComponent_eq_integral`（148–240）；Joshi III `th:thetam-construction` 为后续 locus 对齐目标。仅指定因子乘上 `qroot^(j²)`，其余因子为 1；以 canonical singleAlgHom 识别 scaleElt，并直接推导紧性、正有限 normalization Haar、normalization 包含、坏特征外等于 normalization，以及指定因子 `ordp` 的实际 Tate q-order 公式。原创消费者证明，没有复制额外参考代码。 | Scene1/Derived；proved |

该区域是实际局部 container 构件，不识别为全部论文 Ind1–Ind3 或 Joshi theta locus；不要求调用方提供 norm、紧性、Haar 正性或包含证书。沿用已有 full-support `badChars`，无需其最小性、full support 等于 VBad、degree-one 或额外根相等假设。Core 假设增量 0，Prologue-R5 与旧声明类型不变；无新增参考依赖或许可证变更。

验收：最终新叶、`Checks.SceneBounds`、`Axioms.SceneBounds`、`Act1Scene1` 四个直接 Lean 热检查均退出 0，耗时依次为 119.931、127.609、117.818、113.284 秒，进程组峰值 RSS 依次为 9,236,280、9,315,632、9,303,472、9,248,304 KiB。最终四项合计 478.642 秒；新增 20/20 公开声明逐名通过公理检查，1659 个公理打印声明只含 `propext`、`Classical.choice`、`Quot.sound`，无 `sorryAx`；最终叶日志无错误或 warning。Scene1 的 451 个可达本工程模块通过静态导入边界检查，无 Obligations、Candidate、Scene2、Act2 或 `Iut.*` 导入。全部采用 CPU affinity `0–13`、`LEAN_NUM_THREADS=10`、Lean `-j1`，实际并发 Lean worker 峰值 1；每 0.5 秒采样进程组 RSS，未触发 85 GiB 停止线。

首次因 `pow_le_one₀` 多传参数失败，耗时 113.323 秒、进程组峰值 9,229,028 KiB；修复后叶及三项审计分别在 113.432、125.575、121.871、119.493 秒通过。日志复核发现一个 unused `Fintype` 提示，清除后执行上述最终四项验收。本单元共 9 次直接 Lean 任务（8 成功、1 失败），累计 1072.336 秒，进程组总峰值 9,315,632 KiB；无 heartbeat 超时或上限调整，未运行 Lake build 调度器，未重编译 Mathlib。

### Actual InitialThetaData 的完整有限处 tuple packet 与标准 procession

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-INITIAL-THETA-FINITE-PACKET-REGION` | `IutInitialThetaFinitePacketRegion.Fiber`, `IutInitialThetaFinitePacketRegion.fiber_nonempty`, `IutInitialThetaFinitePacketRegion.Tuple`, `IutInitialThetaFinitePacketRegion.tuple_nonempty`, `IutInitialThetaFinitePacketRegion.packet`, `IutInitialThetaFinitePacketRegion.Total`, `IutInitialThetaFinitePacketRegion.region`, `IutInitialThetaFinitePacketRegion.integralRegion`, `IutInitialThetaFinitePacketRegion.mem_region`, `IutInitialThetaFinitePacketRegion.mem_integralRegion`, `IutInitialThetaFinitePacketRegion.witness`, `IutInitialThetaFinitePacketRegion.witness_mem_region`, `IutInitialThetaFinitePacketRegion.region_nonempty`, `IutInitialThetaFinitePacketRegion.region_isCompact`, `IutInitialThetaFinitePacketRegion.integralRegion_isCompact`, `IutInitialThetaFinitePacketRegion.region_subset_integralRegion`, `IutInitialThetaFinitePacketRegion.productMeasure`, `IutInitialThetaFinitePacketRegion.productMeasure_region`, `IutInitialThetaFinitePacketRegion.productMeasure_integralRegion`, `IutInitialThetaFinitePacketRegion.productMeasure_region_le_one`, `IutInitialThetaFinitePacketRegion.productMeasure_region_pos_lt_top`, `IutInitialThetaFinitePacketRegion.region_eq_integralRegion_of_not_bad`, `IutInitialThetaFinitePacketRegion.badPrimes_finite`, `IutInitialThetaFinitePacketRegion.region_finite_support`, `IutInitialThetaFinitePacketRegion.Index`, `IutInitialThetaFinitePacketRegion.procession_length_pos`, `IutInitialThetaFinitePacketRegion.capsule_card`, `IutInitialThetaFinitePacketRegion.processionRegion`, `IutInitialThetaFinitePacketRegion.processionRegion_isCompact`, `IutInitialThetaFinitePacketRegion.processionRegion_nonempty`, `IutInitialThetaFinitePacketRegion.processionRegion_finite_support`；`Act1Scene1/IutInitialThetaFinitePacketRegion.lean` | 参考 `refer/iut/Iut/Concrete/Container.lean` 的 `fiberFiniteEquiv`、`packet`、`productRegion_eq_pi`，`ThetaRegion.lean` 的 `thetaPilot`，`Cor312/Procession.lean` 的 `Procession.standard`。在同一 actual InitialThetaData 的 torsion field 上遍历每个有理素数上全部有限处的 tuple，以 `{0,…,j}` 为标签、j 为指定因子，装配已有 actual q-root scaled-normalization 区域。证明素数纤维和 tuple 非空、区域显式 witness、紧性、integral 基准包含、局部 normalization Haar 的有限乘积公式、基准测度 1、正有限测度及坏特征外基准等式。标准 procession 使用 `ellStar=(ell-1)/2`、`j=i+1`，其正长度和全族共同有限支撑均从同一 D 推出。原创消费者证明，无额外参考代码复制。 | Scene1/Derived；proved |

该构造使用完整有限处 tuple，不额外选择一个 section tuple，也不假设 full-support 等于 VBad、degree-one 或 representative mass-one。乘积测度只是一组已构造局部 normalization Haar 的普通有限乘积；不识别为论文 tuple-weighted / procession-normalized log-volume，不构造无穷处区域、paper representatives、BK/theta locus 或完整 RHSData。四个最终闸门继续开放。Prologue-R5、旧声明类型和导入边界不变，Core 假设增量 0；无新增参考依赖或许可证变更。

验收：最终新叶、`Checks.SceneBounds`、`Axioms.SceneBounds`、`Act1Scene1` 四项直接 Lean 热检查均退出 0，耗时依次 118.478、125.080、113.679、114.336 秒，进程组峰值 RSS 依次 9,243,844、9,317,704、9,305,516、9,249,212 KiB；最终四项合计 471.573 秒。最终叶日志无错误或 warning，31/31 个新增公开声明逐名通过公理核对；1690 个打印声明仅含 `propext`、`Classical.choice`、`Quot.sound`，无 `sorryAx`。静态可达导入检查覆盖 452 个本工程模块，未导入 Obligations、Candidate、Scene2、Act2 或 `Iut.*`。

首轮叶检查退出 0（113.882 秒，进程组峰值 9,237,236 KiB），发现两条 linter 提示后清理。清理脚本的相对路径错误曾启动未清理版本的检查；发现后以 SIGTERM 停止，记退出 -15（64.205 秒，峰值 5,197,996 KiB），未将此中断记为成功；修正绝对路径后执行上述最终四项。本轮共 6 个直接 Lean 任务（5 成功、1 中断），累计 649.660 秒，进程组峰值 9,317,704 KiB。全部采用 CPU affinity `0–13`、`LEAN_NUM_THREADS=10`、Lean `-j1`，实际并发 worker 峰值 1，每 0.5 秒采样 RSS 并设置 85 GiB 停止线，未触发内存停止；无 heartbeat 超时或上限调整。只调用 `lake env lean -j1 -o` 使用现有依赖产物，未运行 Lake build 调度器，未重编译 Mathlib。

### Actual finite-place tuple packet 的 degree-weighted 三层 log-volume

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-INITIAL-THETA-FINITE-PACKET-LOG-VOLUME` | `IutInitialThetaFinitePacketLogVolume.placeWeight`, `IutInitialThetaFinitePacketLogVolume.placeWeight_pos`, `IutInitialThetaFinitePacketLogVolume.placeWeight_sum_one`, `IutInitialThetaFinitePacketLogVolume.tupleWeight`, `IutInitialThetaFinitePacketLogVolume.tupleWeight_pos`, `IutInitialThetaFinitePacketLogVolume.tupleWeight_sum_one`, `IutInitialThetaFinitePacketLogVolume.tupleWeight_le_one`, `IutInitialThetaFinitePacketLogVolume.tupleWeight_eq_dimension_div_degree`, `IutInitialThetaFinitePacketLogVolume.componentLogVolume`, `IutInitialThetaFinitePacketLogVolume.componentLogVolume_integral`, `IutInitialThetaFinitePacketLogVolume.weighted_componentLogVolume`, `IutInitialThetaFinitePacketLogVolume.packetLogVolume`, `IutInitialThetaFinitePacketLogVolume.packetLogVolume_eq_sum_log_div_degree`, `IutInitialThetaFinitePacketLogVolume.packetLogVolume_eq_productMeasure_log`, `IutInitialThetaFinitePacketLogVolume.packetLogVolume_nonpos`, `IutInitialThetaFinitePacketLogVolume.packetLogVolume_eq_zero_of_not_bad`, `IutInitialThetaFinitePacketLogVolume.badPrimes`, `IutInitialThetaFinitePacketLogVolume.mem_badPrimes`, `IutInitialThetaFinitePacketLogVolume.packetLogVolume_support_subset`, `IutInitialThetaFinitePacketLogVolume.packetLogVolume_finite_support`, `IutInitialThetaFinitePacketLogVolume.globalLogVolume`, `IutInitialThetaFinitePacketLogVolume.globalLogVolume_eq_sum`, `IutInitialThetaFinitePacketLogVolume.globalLogVolume_nonpos`, `IutInitialThetaFinitePacketLogVolume.processionLogVolume`, `IutInitialThetaFinitePacketLogVolume.processionLogVolume_eq_sum`, `IutInitialThetaFinitePacketLogVolume.processionLogVolume_eq_prime_sum`, `IutInitialThetaFinitePacketLogVolume.processionLogVolume_nonpos`, `IutInitialThetaFinitePacketLogVolume.negative_abs_processionLogVolume`；`Act1Scene1/IutInitialThetaFinitePacketLogVolume.lean` | 参考 `refer/iut/Iut/Concrete/Container.lean` 的 `weight`、`tupleWeight`、`vol`，`LocalConstruct/Volume.lean` 的 `componentVol`（195–204）和 `Cor312/LogVolume.lean` 的 `globalVol`、`processionVol`。使用同一 actual D 的全素数纤维，证明 place/tuple 正权及总质量 1；tuple weight 精确等于 actual tensor dimension 除以 `[Kt:ℚ]^(j+1)`。component 定义为实际 normalization Haar 的实对数除以 tensor dimension，消去后 weighted packet log-volume 等于实际 productMeasure 区域的实对数除以 `[Kt:ℚ]^(j+1)`。由已证正有限 Haar、integral 包含和有限坏特征集，推导非正性、显式有限素数和、标准 procession 平均及负绝对值符号。原创消费者证明，无参考代码复制。 | Scene1/Derived；proved |

该计算固定参考 container 的全部 torsion-field tuple 和 local-degree 权重，没有把 ordinary product measure 直接称为 packet-normalized volume，也没有把此 local-degree 会计识别为 Joshi III `ss:weighted-vol` / `eq:weights` 中的所选代表处及 relative-degree 权重。paper carrier/权重比较、真实 theta/BK/无穷处区域及最终 thetaVolume 身份仍开放。本轮不是最终 3.12 下界，不增加 Core 假设；Prologue-R5、旧定理类型与独立依赖不变，无新增参考代码或许可证变更。

验收：最终新叶、`Checks.SceneBounds`、`Axioms.SceneBounds`、`Act1Scene1` 四项直接 Lean 热检查均退出 0，耗时依次 114.712、130.685、121.934、115.700 秒，进程组峰值 RSS 依次 9,234,928、9,319,716、9,306,140、9,247,044 KiB；成功验收合计 483.031 秒。28/28 个新增公开声明逐名核对公理，1718 个打印声明仅含 `propext`、`Classical.choice`、`Quot.sound`，无 `sorryAx`；最终叶日志无错误或 warning。静态导入检查覆盖 453 个可达本工程模块，无 Obligations、Candidate、Scene2、Act2 或 `Iut.*` 导入。Lean `v4.35.0-rc3` 与 Mathlib `389347a7c1cfa76f6bd5be2ca35d4cb621610ad3` 冻结基线核对通过。

前两次叶检查均因同一 `toReal_mono` 调用中嵌套 `by` 的换行缩进解析失败（分别 120.947, 117.414 秒、退出 1；拆出独立 `have` 后解决）；未发生数学证明或 heartbeat 超时。本轮共 6 次直接 Lean 任务（4 成功、2 失败），累计 721.392 秒，进程组峰值 9,319,716 KiB。全部使用 CPU affinity `0–13`、`LEAN_NUM_THREADS=10`、Lean `-j1`，实际并发 worker 峰值 1；每 0.5 秒采样 RSS，85 GiB 停止线未触发。只用 `lake env lean -j1 -o` 访问现有依赖产物，没有运行 Lake build 调度器，未重编译 Mathlib。

### Actual finite packet 的指定因子 q-root log-volume 下界

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-LOCAL-TENSOR-NORMALIZATION-LOG-VOLUME` | `JoshiTeich.Act1Scene1.LocalCompletion.Packet.normalizationLogVolume`, `JoshiTeich.Act1Scene1.LocalCompletion.Packet.normalizationLogVolume_scalarNormalization`, `JoshiTeich.Act1Scene1.LocalCompletion.Packet.normalizationLogVolume_mono`, `JoshiTeich.Act1Scene1.LocalCompletion.Packet.normalizationLogVolume_scalarNormalization_le_factorOrbit`, `JoshiTeich.Act1Scene1.LocalCompletion.Packet.normalizationLogVolume_pure_principalRegion`, `JoshiTeich.Act1Scene1.LocalCompletion.Packet.normalizationLogVolume_principalRegion_le_factorOrbit`；`Act1Scene1/LocalCompletionTensorNormalizationLogVolume.lean` | 从 actual normalization Haar 与已证 determinant/completion-norm 公式推出 `normalizationLogVolume=log(Haar)/tensor dimension` 的 scalar-normalization 精确求值及包含单调性，再以 principalRegion 等式导出实际 finite factor orbit 的下界。Joshi III `le:volume-lemma3` 为包含与体积比较的来源。原创消费者证明，无参考源码复制。 | Scene1/Derived；proved |
| `JT-SCENE1-INITIAL-THETA-FINITE-PACKET-LOWER-BOUND` | `JoshiTeich.Act1Scene1.IutInitialThetaFinitePacketLowerBound.tupleWeight_coordinate_sum`, `JoshiTeich.Act1Scene1.IutInitialThetaFinitePacketLowerBound.normalized_root_log_eq_ordp`, `JoshiTeich.Act1Scene1.IutInitialThetaFinitePacketLowerBound.componentLogVolume_principalRegion`, `JoshiTeich.Act1Scene1.IutInitialThetaFinitePacketLowerBound.componentLogVolume_region_lower_bound`, `JoshiTeich.Act1Scene1.IutInitialThetaFinitePacketLowerBound.tupleWeight_order_sum`, `JoshiTeich.Act1Scene1.IutInitialThetaFinitePacketLowerBound.packetLogVolume_lower_bound`, `JoshiTeich.Act1Scene1.IutInitialThetaFinitePacketLowerBound.packetLogVolume_bounds`；`Act1Scene1/IutInitialThetaFinitePacketLowerBound.lean` | 参考 `refer/iut/Iut/Concrete/ThetaRegion.lean` 的 `scaleElt` / `thetaFinite` 区域形状及 Joshi III `le:volume-lemma3` 比较模式；对同一实际 D 的全部 torsion-place tuple 证明任意指定坐标的加权边缘恒等式，计算指定因子 `qroot^(j²)` 的 principal normalization log-volume，继而推出 actual region 的 component 下界和 `-j² * log(p) * vbadWeightedFiber(D,p) ≤ packetLogVolume(D,p,j) ≤ 0`。`vbadWeightedFiber` 使用全部 torsion-field 处，根、估值及权重均来自同一 D，无额外 coverage/degree-one/mass-one 前提。原创消费者证明，无参考源码复制。 | Scene1/Derived；proved |

该界精确保留指定因子的 `j²`，没有将有限自同构 container 识别为论文 theta locus，也没有把 local-degree 全部 tuple 权重替换为 Joshi paper representatives / relative-degree 权重；H¹ₑ/BK、无穷处、paper volume 及最终 3.12 仍开放。通用模块的公开等式对任意 set 定义实 log 值，但下界/单调性应用均从实际正有限 Haar 与包含推导，未以 `Real.log 0=0` 代替扩展对数。无新增 Core 前提，Prologue-R5、旧声明类型和独立依赖不变，无许可证增量。

验收（2026-10-19）：最终通用叶 `LocalCompletionTensorNormalizationLogVolume` 退出 0，70.455 秒、进程组峰值 5,480,492 KiB；实际叶 `IutInitialThetaFinitePacketLowerBound` 退出 0，561.892 秒、峰值 12,849,648 KiB，两叶最终日志均无错误或 warning。`Checks.SceneBounds`、`Axioms.SceneBounds`、`Act1Scene1` 依次退出 0，耗时 128.862、97.672、99.467 秒，峰值 RSS 依次 9,320,972、9,308,472、9,241,704 KiB。13/13 个新增公开声明逐名通过公理核对；1731 个打印声明只含 `propext`、`Classical.choice`、`Quot.sound`，无 `sorryAx`。静态导入检查覆盖 455 个可达本工程模块，无 Obligations、Candidate、Scene2、Act2 或 `Iut.*` 导入。

heartbeat 重试遵守用户顺序：默认 200000 失败后升至 1000000；再次失败后拆出通用 normalization log-volume 与单调性模块并升至 2000000；继续改为已证等价的 principalRegion 集合接口并升至 4000000；最后用逐步等式链替代实际区域上的 `simp`，局部下界在 8000000 下通过，principalRegion 精确求值保留 2000000。高阶 tuple 求和另改为显式 `Fintype.prod_sum` / marginal 函数，乘法重排改用精确 `mul_div_assoc`，未改变目标下界或数学前提。前四次实际叶均退出 1，耗时 153.724、305.279、492.045、677.631 秒；通用叶第一次版本在 71.880 秒通过，随后扩展 principalRegion API 的最终版本在上述 70.455 秒通过。

本轮共 10 次直接 Lean 任务（6 成功、4 失败），累计 2658.907 秒，进程组峰值 12,849,648 KiB。全部使用 CPU affinity `0–13`、`LEAN_NUM_THREADS=10`、Lean `-j1`，实际并发 worker 峰值 1，每 0.5 秒采样进程组 RSS，85 GiB 停止线未触发（用户上限 90 GiB）。只使用 `lake env lean -j1 -o` 和现有依赖产物，未运行 Lake build 调度器，未重编 Mathlib。无数学负面结论或动态边界变更，不写入 log5。

### Actual finite packet 下界的全局与标准 procession 汇总

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-INITIAL-THETA-FINITE-GLOBAL-LOWER-BOUND` | `JoshiTeich.Act1Scene1.IutInitialThetaFiniteGlobalLowerBound.{vbadWeightedFiber_eq_zero_of_not_qPilot_char,qPilot_chars_subset_badChars,badChars_weighted_logSum_eq_absLogQ,badPrimes_weighted_logSum_eq_absLogQ,globalLogVolume_lower_bound,globalLogVolume_bounds,squareAverage,squareAverage_pos,processionLogVolume_lower_bound,processionLogVolume_bounds,negative_abs_processionLogVolume_lower_bound}`；`Act1Scene1/IutInitialThetaFiniteGlobalLowerBound.lean` | Joshi III `le:volume-lemma3`（3576–3583）的包含/体积比较及 `th:moccor-Mochizuki-form2`（3617–3633）的局部到全局组织；`refer/iut/Iut/Cor312/LogVolume.lean` 的 `globalVol` / `processionVol`（170–205）区分素数求和与 capsule 平均，III `cor:cor312` 为后续符号/归一化目标。由已证实际 packet 下界，在同一 D 上证明 q-pilot 特征集包含于 full-support badChars，多余素数的实际 VBad weighted fiber 为零，经素数子类型重索引得 `sum_badPrimes(log(p)*vbadWeightedFiber)=absLogQ(actual Q)`。对所有 j 得 `-j²*absLogQ ≤ globalLogVolume(D,j) ≤ 0`；对标准 j=1,…,n、n=(ell-1)/2 平均，得 `-(squareAverage(D)*absLogQ) ≤ processionLogVolume(D) ≤ 0`，以及同一负绝对值下界，`squareAverage=(sum_j j²)/n>0`。原创消费者证明，无参考源码复制。 | Scene1/Derived；proved |

本单元只将已证明的 actual finite container 下界接到同一 D 的实际 VBad q-pilot，并保留平方指数平均系数；未将其改成系数 1，也未声称 Joshi `cor:cor312`。full torsion-field local-degree 权重与论文代表处/relative-degree 权重的身份、theta locus 与 paper hull/volume、H¹ₑ/BK、untilt/period 联合来源和无穷处贡献仍未闭合，G1–G4 保持 0/4。无新增 Core 契约或假设，Prologue-R5 不变，旧公开类型不变，无许可证增量。没有边界变更或数学负面证据，不写入 log5。

验收（2026-10-19）：新叶 `IutInitialThetaFiniteGlobalLowerBound` 一次通过，106.158 秒、进程组峰值 9,230,836 KiB，日志无错误或 warning。`Checks.SceneBounds`、`Axioms.SceneBounds`、`Act1Scene1` 依次退出 0，耗时 108.642、109.811、105.296 秒，峰值 RSS 依次 9,321,832、9,309,372、9,248,924 KiB。11/11 个新增公开声明逐名通过公理核对；1742 个打印声明仅含 `propext`、`Classical.choice`、`Quot.sound`，无 `sorryAx`，公理审计日志无 warning。静态导入审计覆盖 456 个可达本工程模块，无 Obligations、Candidate、Scene2、Act2 或 `Iut.*` 导入，未改任何已证高扇出数学模块。

本轮共 4 次直接 Lean 任务，全部成功，累计 429.907 秒，进程组峰值 9,321,832 KiB。全部使用 CPU affinity `0–13`、`LEAN_NUM_THREADS=10`、Lean `-j1`，实际并发 worker 峰值 1；每 0.5 秒采样进程组 RSS，85 GiB 停止线未触发（用户上限 90 GiB）。只用 `lake env lean -j1 -o` 和现有依赖产物；未调用 Lake build 调度器、未冷构建或重编 Mathlib，也未改冻结工具链或依赖。

### Actual infinite-place tensor、log-shell 与 packet 贡献

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-LOCAL-ARCHIMEDEAN-TENSOR-INTEGRAL` | `LocalArchimedean.{archField,Factor,Tensor,tensorBasis,NormedFactor,ProjectiveModel,archNorm,archIntegral,exists_archNorm_le,continuous_archNorm,exists_norm_le_archNorm,isCompact_archIntegral,exists_ball_subset_archIntegral}` 及其坐标/范数辅助法律；`Act1Scene1/LocalArchimedeanTensor.lean` | 独立移植参考 `LocalConstruct/Packet.lean` 的实/复因子和基坐标 tensor，以及 `LocalConstruct/Archimedean.lean` 的 projective norm 比较。仅用实际 `InfinitePlace K`，不保留 finite-place junk、LocalTheory 或参考依赖。用显式有限基索引、finite module 实例与 frozen Mathlib API，建立 B_I 的紧性及零点邻域；不假定 projective seminorm 的 Hausdorff 性。 | Scene1/Derived；proved |
| `JT-SCENE1-LOCAL-ARCHIMEDEAN-COMPLETION-MODEL` | `LocalArchimedean.{completionModelHom,completionModelHom_complex,completionModelHom_bijective,completionModelEquiv,completionNormedEquiv,completionModelEquiv_norm,completionModelIsometry}`；`Act1Scene1/LocalArchimedeanCompletionModel.lean` | 原创消费者证明；Mathlib `InfinitePlace.Completion.extensionEmbedding`、实/复满射性及 isometry 提供同一实际完成域到所选实/复因子的 canonical ring equivalence 与 norm-preserving equivalence。没有另给完成域身份假设；正向映射就是实际处嵌入的连续延拓。 | Scene1/Derived；proved |
| `JT-SCENE1-LOCAL-ARCHIMEDEAN-TENSOR-LOG-SHELL` | `LocalArchimedean.{norm_algHom_apply_subalgebra,archField_cases,norm_archAut_apply,archAutCLM,factorTensorAut,toProjectiveModel_factorTensorAut,archNorm_factorTensorAut_le,archLogShell,isCompact_archLogShell,factorTensorAut_image_archLogShell_subset,factorOrbit,factorOrbit_archLogShell,isCompact_factorOrbit_archLogShell}` 及 tprod、identity、scaled-B_I 法律；`Act1Scene1/LocalArchimedeanTensorLogShell.lean` | 独立适配 `LocalConstruct/ArchLogShell.lean`；证明各实际实/复 factor 的 ℝ-algebra automorphism 保范，tensor map 对 projective norm 收缩，因此保 B_I 与所有实缩放；完整 factor orbit 的 π^|I| B_I 恰等于自身并紧。对应 IUT IV Proposition 1.5(iii),(iv) 的局部区域性质。 | Scene1/Derived；proved |
| `JT-SCENE1-LOCAL-ARCHIMEDEAN-TENSOR-HAAR` | `LocalArchimedean.{integralPositiveCompact,normalizedHaar,normalizedHaar_archIntegral,normalizedHaar_archLogShell,archLogShell_haar_pos_lt_top,factorOrbit_archLogShell_haar_pos_lt_top,tensor_finrank_pos,normalizationLogVolume,normalizationLogVolume_archIntegral,normalizationLogVolume_archLogShell,normalizationLogVolume_archLogShell_nonneg}`；`Act1Scene1/LocalArchimedeanTensorHaar.lean` | 原创证明；Mathlib `Measure.addHaarMeasure` 和 `addHaar_smul_of_nonneg` 在已证紧且有内点的 B_I 上归一化真实 Haar。精确计算 shell 测度为 `(π^|I|)^dim`，证明其及全部 factor orbit 的正有限 Haar；除以实际 tensor 维数的实 log 为 `|I|*log π`，积分基准的 log 为 0。 | Scene1/Derived；proved |
| `JT-SCENE1-INITIAL-THETA-ARCHIMEDEAN-PACKET` | `IutInitialThetaArchimedeanPacketRegion.{Tuple,Total,completionEquiv,region,integralRegion,region_eq_shell_product,region_isCompact,productMeasure,productMeasure_integralRegion,productMeasure_region,productMeasure_region_pos_lt_top,placeWeight,placeWeight_pos,placeWeight_sum_one,tupleWeight,tupleWeight_sum_one,packetLogVolume,packetLogVolume_eq,packetLogVolume_nonneg,processionLogVolume,processionLogVolume_eq,processionLogVolume_nonneg}`；`Act1Scene1/IutInitialThetaArchimedeanPacketRegion.lean` | 原创实际消费者；`refer/iut/Iut/Concrete/Container.lean` 的 infinite fiber、weight、tupleWeight、packet product 及 `ThetaRegion.lean` 的 thetaInfinite 提供装配形状；IUT IV Proposition 1.5 与 Joshi III `th:thetam-construction` 提供无穷处目标背景。对同一 D 的 torsion field 所有无限处、每个 Fin(j+1) capsule 的全部 tuple 构造 region，并给出实际 completion equivalence、紧性与正有限 product Haar。placeWeight=mult/[Kt:ℚ]，由 Mathlib sum_mult_eq 推出 place/tuple 总质量 1；actual packet 的 normalized log 精确等 `(j+1)*log π`，标准 procession 是这些值的平均并非负。 | Scene1/Derived；proved |

所有上述 Lean 命名空间均以前缀 `JoshiTeich.Act1Scene1` 开始。移植前已核对参考 Packet、Archimedean、ArchLogShell 的版权头及双方 LICENSE：均为 Apache-2.0；Git 作者 Christian Merten，文件作者 The iut contributors。Packet 原提交 `4d2b6e926089b949109c69c28f13c7f878249c5d`，Archimedean / ArchLogShell 原提交 `b76207ab8955e68a7408d5d2a770b75a30c3bebf`，参考快照 `07cb1da58f6d428a670dbb5dd6093d428bcbcdd8`。两份移植文件保留原版权/许可证头，并记录路径、提交、作者、独立命名空间和改写范围；其余三个文件为原创 Mathlib/source 消费者。未依赖或导入 refer/iut，未引入新许可证。

该单元完成实际无限处的局部模型、B_I / log-shell、factor orbit、正有限测度和同一 D 上的 packet/procession 贡献；没有将这些 full torsion-field place weights 与 Joshi 的 selected representatives/relative-degree 权重混同，也未声称它们就是论文 theta locus。有限/无限处统一 carrier、完整 RHSData、paper theta/hull/volume 身份、H¹ₑ/BK 和 untilt/period 联合来源仍待完成，G1–G4 保持 0/4。新增数学只在 Scene1/Derived；Core 假设增量 0，Prologue-R5 不变。没有新的边界变更或数学负面证据，不写入 log5。

验收（2026-10-19）：五个新叶最终检查均退出 0，最终日志全部为空（无错误或 warning）：`LocalArchimedeanTensor` 79.978 秒、峰值 5,013,404 KiB；`LocalArchimedeanCompletionModel` 59.740 秒、4,984,456 KiB；`LocalArchimedeanTensorLogShell` 61.855 秒、4,991,280 KiB；`LocalArchimedeanTensorHaar` 56.195 秒、4,990,280 KiB；`IutInitialThetaArchimedeanPacketRegion` 105.304 秒、9,084,388 KiB。`Checks.SceneBounds`、`Axioms.SceneBounds`、`Act1Scene1` 依次退出 0，耗时 115.872、108.833、110.257 秒，峰值 RSS 依次 9,329,900、9,317,388、9,248,824 KiB。108/108 个新增公开声明（含 named instances 和载体别名）逐名通过公理核对；1850 个打印声明仅含 `propext`、`Classical.choice`、`Quot.sound`，无 `sorryAx`，公理审计无 warning。静态导入审计覆盖 461 个可达本工程模块，无 Obligations、Candidate、Scene2、Act2 或 `Iut.*` 导入。

六次失败均属冻结 API / 类型适配：基索引 Fintype 与 tensor finite-module 的显式实例缺失（63.826 秒）；错误使用不存在的 `Trigonometric.Constants` 模块名，改用已有 `Trigonometric.Basic`（57.187 秒）；Factor 与 NormedFactor 类型同义词的 norm/isometry elaboration，改为显式 normed equivalence（60.244 秒）；参考 `Finset.prod_le_one` 及 `isCompact_smul` 的旧 API（60.745 秒）；实数积的单调性改用 `prod_le_one₀` 并显式给非负性（61.764 秒）；Haar scaling 的 `Measure` 命名空间修正（61.353 秒）。同时清除弃用名与 unused-section/haveI 警告。未出现 heartbeat 或内存失败，未改变目标、数学前提或放宽检查。

本轮共 14 次直接 Lean 任务（8 成功、6 失败），累计 1063.153 秒，进程组峰值 9,329,900 KiB。全部使用 CPU affinity `0–13`、`LEAN_NUM_THREADS=10`、Lean `-j1`，实际并发 worker 峰值 1；每 0.5 秒采样进程组 RSS，85 GiB 停止线未触发（用户上限 90 GiB）。只使用 `lake env lean -j1 -o` 与现有依赖产物；所有直接 Mathlib 导入均核对已有 olean，没有调用 Lake build 调度器、冷构建、重编 Mathlib 或变更冻结工具链/依赖。

### Actual finite/infinite packets 的统一 adelic 区域与 log-volume

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-RATIONAL-PLACE-INDEX` | `RationalPlace`、finite/infinite constructors、`RationalPlace.{IsFinite,residueChar,residueChar_finite,residueChar_infinite}`；`Act1Scene1/Scene1RationalPlace.lean` | 独立移植 `refer/iut/Iut/Cor312/RationalPlace.lean`，只保留标准有理处索引及其基本识别法律，精确导入 prime definitions；没有参考工程依赖，没有增加 Core 契约。来源 IUT I Definition 3.1(e) 及 IUT III Propositions 3.1–3.3。 | Scene1/Derived；proved |
| `JT-SCENE1-INITIAL-THETA-ADELIC-PACKET-REGION` | `IutInitialThetaAdelicPacketRegion.{toRational,PlaceFiber,fiberFiniteEquiv,fiberInfiniteEquiv,Tuple,placeTupleEquiv,Total,region,integralRegion,packetMeasure,region_isCompact,packetMeasure_integralRegion,packetMeasure_region_pos_lt_top,exceptionalPlaces,finite_mem_exceptionalPlaces,region_eq_integralRegion_of_not_exceptional,region_support_subset,region_finite_support,processionRegion_finite_support,Container,containerRegion,integral_eventually_of_mem_region,toContainer,toContainer_mem,region_nonempty,witness,witness_mem_containerRegion,containerRegion_nonempty}` 及 Total 的拓扑/可测结构；`Act1Scene1/IutInitialThetaAdelicPacketRegion.lean` | 适配 reference `Concrete/Container.lean` 的处映射、finite/infinite fiber equivalences 和 `Cor312/Container.lean` 的 restricted-product carrier 形状；原创消费者使用已证同一 D 的实际有限处/无限处区域及 Haar。`PlaceFiber` 为同一 torsion field 全部 actual places 的精确纤维，`placeTupleEquiv` 识别全部 Fin(j+1) tuple。对每个有理处给出紧 region、integral 基准测度 1、正有限局部 product Haar；共同 exceptionalPlaces=finite badPrimes image 加 ∞，对所有 j 及整个标准 procession 有限支撑。任意逐处 region family 自动属于相对 integral 基准的 restricted product，构造实际 witness 并证明 containerRegion 非空；未引入无限乘积测度或 theta-pilot 作为输入假设。对应 `Concrete/ThetaRegion.lean` 的 thetaPilot 有限支撑组织，Joshi III `th:thetam-construction` 提供后续 adelic 来源目标。 | Scene1/Derived；proved |
| `JT-SCENE1-INITIAL-THETA-ADELIC-PACKET-LOG-VOLUME` | `IutInitialThetaAdelicPacketLogVolume.{packetLogVolume,packetLogVolume_eq_zero_of_not_exceptional,packetLogVolume_support_subset,packetLogVolume_finite_support,globalLogVolume,globalLogVolume_eq_sum,finite_image_logSum,globalLogVolume_eq_finite_add_arch,globalLogVolume_bounds,processionLogVolume,processionLogVolume_eq_finite_add_arch,processionLogVolume_bounds}`；`Act1Scene1/IutInitialThetaAdelicPacketLogVolume.lean` | 原创消费者；reference `Concrete/Container.lean` 的 vol 与 `Cor312/LogVolume.lean` 的 globalVol / processionVol 区分逐处求和和标准 capsule 平均。实际 packetLogVolume 在共同 exceptionalPlaces 外为零，故有理处 finsum 精确分解为有限处 globalLogVolume 加无穷处 packetLogVolume；procession 同样精确分解。若 A_j 为已证 `(j+1)log π`、Q 为同一 D 的实际 VBad absLogQ，则 `A_j-j²Q ≤ adelicGlobalLogVolume(D,j) ≤ A_j`；若 A 是实际无限处 procession 平均、S 是已证 squareAverage，则 `A-SQ ≤ adelicProcessionLogVolume(D) ≤ A`。没有假定完整 adelic log 的符号，也未把它替换成负绝对值或最终 3.12。Joshi III `ss:weighted-vol`、`th:moccor-Mochizuki-form2` 为后续 paper-volume 比较来源。 | Scene1/Derived；proved |

本节命名空间均以前缀 `JoshiTeich.Act1Scene1` 开始。移植前核对所用参考文件版权头及双方 LICENSE：Apache-2.0；Git 作者 Christian Merten，文件作者 The iut contributors。RationalPlace / Cor312 Container 原提交 `0702e371fa9ecf639fb469038281dced22907723`，Concrete Container 原提交 `be25c6c14681a180795dc60972941472ce4d2645`，参考快照 `07cb1da58f6d428a670dbb5dd6093d428bcbcdd8`。移植文件保留原版权/许可证通知并登记路径、作者、提交和独立改写范围；没有依赖或导入 refer/iut，没有新增许可证。

本单元闭合已构造 actual finite/infinite container 的统一 rational-place carrier、有限支撑、restricted-product 非空区域和其 log-volume 拆分。没有将该 container 识别为真实论文 theta locus、未识别 paper selected representatives/relative-degree 权重或 holomorphic hull/volume，完整 RHSData 的 log-shell/hull/source 比较以及 H¹ₑ/BK、untilt/period 联合来源仍未闭合，G1–G4 保持 0/4。所有新数学留在 Scene1/Derived，Core 假设增量 0，Prologue-R5 不变；没有新的数学负面证据或动态边界变更，不写入 log5。

验收（2026-10-19）：新叶 `Scene1RationalPlace`、`IutInitialThetaAdelicPacketRegion` 一次通过，耗时 40.507、104.238 秒，进程组峰值 3,047,400、9,239,732 KiB；最终 `IutInitialThetaAdelicPacketLogVolume` 111.438 秒、9,218,424 KiB，三叶最终日志全部为空，无错误或 warning。`Checks.SceneBounds`、`Axioms.SceneBounds`、`Act1Scene1` 依次退出 0，耗时 111.852、110.958、108.861 秒，峰值 RSS 依次 9,333,880、9,320,920、9,250,892 KiB。49/49 个新增公开声明逐名通过公理核对；1899 个打印声明仅含 `propext`、`Classical.choice`、`Quot.sound`，无 `sorryAx`，公理审计无 warning。静态导入审计覆盖 464 个可达本工程模块；额外确认所有这些模块均使用扫描器覆盖的单模块 import 行，无漏掉的多模块/public/meta import；无 Obligations、Candidate、Scene2、Act2 或 `Iut.*` 导入。

一次体积叶失败（106.809 秒、峰值 9,230,824 KiB）：冻结 API 的 `add_le_add_right` 给出另一侧加法的项次序，无法匹配当前 calc 目标；改为显式 `add_le_add hb (le_refl A)` 后通过。有限/无限处拆分等式在首轮已通过，未改变目标或数学前提，未发生 heartbeat / 内存失败。

本轮共 7 次直接 Lean 任务（6 成功、1 失败），累计 694.663 秒，进程组峰值 9,333,880 KiB。全部使用 CPU affinity `0–13`、`LEAN_NUM_THREADS=10`、Lean `-j1`，实际并发 worker 峰值 1；每 0.5 秒采样进程组 RSS，85 GiB 停止线未触发（用户上限 90 GiB）。只使用 `lake env lean -j1 -o` 与现有依赖产物；直接 Mathlib 导入已核对预编译 olean，未调用 Lake build 调度器、冷构建、重编 Mathlib 或变更冻结工具链/依赖。

### Actual q-root packet 的 least normalization hull 与 adelic hull volume

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-INITIAL-THETA-FINITE-PACKET-HULL` | `IutInitialThetaFinitePacketHull.{componentHull,component_subset_hull,componentHull_isCompact,componentHull_haar_pos_lt_top,componentHull_eq_normalizationHull,componentHull_isPrincipal,componentHull_le_principalRegion,componentHull_subset_normalization,componentHull_eq_normalization_of_not_bad,region,mem_region,source_subset_region,region_le_principal_product,region_isCompact,region_subset_integralRegion,productMeasure_region,productMeasure_region_pos_lt_top,region_eq_integralRegion_of_not_bad,packetLogVolume,source_packetLogVolume_le,packetLogVolume_nonpos,packetLogVolume_bounds,packetLogVolume_eq_zero_of_not_bad}`；`Act1Scene1/IutInitialThetaFinitePacketHull.lean` | Joshi III principal normalization hull（3568–3574）、`le:volume-lemma3`；reference `LocalConstruct/Hull.lean` 的 `exists_leastHull_finite` 与 `Concrete/Container.lean` 的 componentwise hull 产品。由同一 actual D 已证的 q-root factor orbit 紧性/正 Haar，实际构造每个 tuple 的 leastHull；证明与 normalization-module span 的等式，保 principal 最小性、normalization 上包含、紧性及正有限 Haar。产品最小性从 source packet 非空和 Set.pi 反射包含推出，未将逐 tuple 条件留给调用者。坏特征外 hull 等于 integral 基准；tuple 权重不变，source packet log-volume ≤ hull packet log-volume ≤ 0，继而保留 `-j² log(p) vbadWeightedFiber` 下界。原创消费者证明，无参考源码复制。 | Scene1/Derived；proved |
| `JT-SCENE1-INITIAL-THETA-ADELIC-PACKET-HULL` | `IutInitialThetaAdelicPacketHull.{region,source_subset_region,region_isCompact,packetMeasure_region_pos_lt_top,region_eq_integralRegion_of_not_exceptional,region_support_subset,region_finite_support,processionRegion_finite_support,containerRegion,source_containerRegion_subset,containerRegion_nonempty,integral_eventually_of_mem_region,toContainer,toContainer_mem,packetLogVolume,finite_packetLogVolume_eq_productMeasure_log,source_packetLogVolume_le,packetLogVolume_eq_zero_of_not_exceptional,packetLogVolume_support_subset,packetLogVolume_finite_support,globalLogVolume,globalLogVolume_eq_sum,source_globalLogVolume_le,globalLogVolume_eq_finite_add_arch,globalLogVolume_bounds,processionLogVolume,source_processionLogVolume_le,processionLogVolume_bounds}`；`Act1Scene1/IutInitialThetaAdelicPacketHull.lean` | reference `Concrete/Container.lean` 的 hull、`Cor312/ContainerHull.lean` 的 hullFamily，及 `Cor312/RightHandSide.lean` 的先 hull 再 procession-volume 组合；Joshi III `le:volume-lemma3` 是包含到 hull 体积比较的来源。有限处使用新构造 actual least normalization hull，无限处保留已是径向 π^|I| B_I 的原 shell，统一在上一单元同一 rational-place/tuple/Container carrier。证明 source 包含、逐处紧与正有限 Haar、共同 exceptionalPlaces 外 integral 等式、整个标准 procession 的有限支撑及 restricted-product 区域非空。证明有限处 hull packet log=log(actual product Haar)/[Kt:ℚ]^(j+1)，再在同一权重上证明 source→hull packet/global/procession log 单调性及 finite/arch 拆分。若 Q 是同一 D 实际 VBad absLogQ、A_j=(j+1)log π、A 是对应标准 procession 平均、S=squareAverage，则 `A_j-j²Q ≤ hullGlobalLogVolume(D,j) ≤ A_j`、`A-SQ ≤ hullProcessionLogVolume(D) ≤ A`。原创消费者证明，无参考源码复制。 | Scene1/Derived；proved |

本节全部命名空间均有前缀 `JoshiTeich.Act1Scene1`。没有新的源码移植或许可证增量；所用 leastHull 与 normalization span 定理均为已验收的本工程定理。这里将先前通用 least-hull 定理实际应用到当前 q-root 区域和全部 tuple，关闭此 container 的 hull 构造与测度/加权 log 连接；未将其识别为论文 theta locus 或 paper holomorphic hull，未将 normalization-module span 替换为 ℤₚ integral hull，未识别 selected representatives/relative-degree 权重。无穷处保持原径向 shell，不声称构造任意无限处 region 的通用 hull operation。完整 RHSData 的 log-shell/source 身份、H¹ₑ/BK、untilt/period 联合来源与最终 3.12 仍开放，G1–G4 保持 0/4。新数学仅在 Scene1/Derived；Core 假设增量 0，Prologue-R5 不变，没有动态边界变更或数学负面证据，不写入 log5。

验收（2026-10-19）：实际有限处 hull 叶 `IutInitialThetaFinitePacketHull` 一次通过，105.734 秒、进程组峰值 9,244,868 KiB；最终 adelic 叶 `IutInitialThetaAdelicPacketHull` 103.144 秒、9,236,596 KiB，两叶最终日志全部为空，无错误或 warning。`Checks.SceneBounds`、`Axioms.SceneBounds`、`Act1Scene1` 依次退出 0，耗时 109.842、110.330、109.312 秒，峰值 RSS 依次 9,337,780、9,322,544、9,249,720 KiB。51/51 个新增公开声明逐名通过公理核对；1950 个打印声明仅含 `propext`、`Classical.choice`、`Quot.sound`，无 `sorryAx`，公理审计无 warning。静态导入审计覆盖 466 个可达本工程模块，并确认所有 import 行均由扫描器覆盖；无 Obligations、Candidate、Scene2、Act2 或 `Iut.*` 导入。

一次 adelic 叶失败（106.772 秒、峰值 9,242,536 KiB）：新增 productMeasure log 等式的显式 tuple 和求和需要本模块自己的 prime Fact、fiber Finite/Fintype 局部实例；补齐后通过。没有 heartbeat / 内存失败，没有改变目标、数学前提或放宽检查。

本轮共 6 次直接 Lean 任务（5 成功、1 失败），累计 645.134 秒，进程组峰值 9,337,780 KiB。全部使用 CPU affinity `0–13`、`LEAN_NUM_THREADS=10`、Lean `-j1`，实际并发 worker 峰值 1；每 0.5 秒采样进程组 RSS，85 GiB 停止线未触发（用户上限 90 GiB）。只用 `lake env lean -j1 -o` 访问现有依赖产物，未调用 Lake build 调度器、冷构建、重编 Mathlib 或变更冻结工具链/依赖。

### Actual infinite-place 的最小径向 hull 与 packet 固定点

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-LOCAL-ARCHIMEDEAN-RADIAL-HULL` | `LocalArchimedean.{radialRegion,mem_radialRegion,radialRegion_mono,radialRegion_isCompact,normalizedHaar_radialRegion,radialRegion_haar_pos_lt_top,hullRadius,radialHull,nonempty_of_haar_pos,archNorm_image_bddAbove,archNorm_le_hullRadius,hullRadius_pos,subset_radialHull,hullRadius_le_of_subset_radialRegion,radialHull_le_radialRegion,radialHull_isCompact,radialHull_haar_pos_lt_top,radialHull_mono,radialHull_radialRegion,radialHull_idem,radialHull_eq_sInter,normalizationLogVolume_mono,normalizationLogVolume_radialRegion,normalizationLogVolume_radialHull,normalizationLogVolume_le_radialHull,radialHull_archLogShell}`；`Act1Scene1/LocalArchimedeanTensorRadialHull.lean` | 独立适配参考 `refer/iut/Iut/Concrete/LocalConstruct/Admissible.lean`（103–178）的径向成员判据和 supremum 最小半径构造。IUT IV Proposition 1.5(iii) 与 `Cor312/HolomorphicHull.lean` 的径向 hull class 是来源。使用本工程实际无限处 Tensor、projective/coordinate norm 比较及 normalized Haar；有界 U 的 projective norm image 有上界，正 Haar 排除 U⊆{0}，故 radius=sSup(archNorm(U))>0。径向 hull=radius·B_I 为包含 U 的最小正径向区域；证明其紧性、正有限 Haar、单调性、径向固定点、幂等性和 sInter 刻画。Haar=radius^dim，dimension-normalized log=log(radius)，并给正有限测度下的 log 单调性。超出 bounded/positive-Haar 域只定义数值，不赋予 hull 法律。 | Scene1/Derived；proved |
| `JT-SCENE1-INITIAL-THETA-ARCHIMEDEAN-PACKET-HULL` | `IutInitialThetaArchimedeanPacketHull.{componentHull,componentHull_eq_archLogShell,region,region_eq_source,region_le_radial_product,region_isPositiveRadialProduct,adelicHull_infinite_eq,region_isCompact,productMeasure_region_pos_lt_top,componentHull_logVolume,packetLogVolume,packetLogVolume_eq_source,packetLogVolume_eq,adelicHull_infinite_logVolume_eq}`；`Act1Scene1/IutInitialThetaArchimedeanPacketHull.lean` | 原创实际消费者；reference `LocalConstruct/Admissible.lean` 的 `exists_leastHull_infinite`、`Concrete/Container.lean` 的 componentwise hull 与 `Cor312/HolomorphicHull.lean` 的正径向类。对同一 D 的 torsion field 全部无限处 tuple 取实际 component radialHull；由已证 factorOrbit(shell)=shell 及径向固定点，证明 componentHull=π^|I| B_I。packet product 属于正径向产品类，且通过非空 source product 的坐标包含反射和通用径向最小性，证明它是包含 source 的最小正径向产品。明确识别 `IutInitialThetaAdelicPacketHull.region ... .infinite` 与此 hull product，保紧性、正有限 product Haar，component/packet log 仍为 `(j+1)log π`，并识别 adelic hull 的无限处 packet log。 | Scene1/Derived；proved |

所有上述命名空间均以前缀 `JoshiTeich.Act1Scene1` 开始。移植前核对参考 Admissible 文件及双方 LICENSE：Apache-2.0；Git 作者 Christian Merten，文件作者 The iut contributors；原提交 `fe96f99cae5c6d48d25113163f1b9b388fc35814`，参考快照 `07cb1da58f6d428a670dbb5dd6093d428bcbcdd8`。新移植文件保留版权/许可证头并记录路径、提交、作者及改写；消费者无参考代码复制，未依赖或导入 refer/iut，没有许可证增量。

本单元补齐上一轮 adelic hull 的无限处分支最小性来源：它确实是正实径向产品类中的 hull，而非仅沿用紧 shell。通用径向操作对所有 bounded positive-Haar 区域有上述法律；没有假定任意 tensor unit 缩放类存在最小 hull。paper theta locus、Joshi selected representative/relative-degree 权重、paper hull/volume、H¹ₑ/BK、untilt/period 联合来源、完整 RHSData 与最终 3.12 仍未闭合，G1–G4 保持 0/4。新结果仅在 Scene1/Derived；Core 假设增量 0，Prologue-R5 不变，旧公开声明类型不变；无动态边界变更或数学负面证据，不写入 log5。

验收（2026-10-19）：最终通用叶 `LocalArchimedeanTensorRadialHull` 退出 0，59.753 秒、进程组峰值 4,984,272 KiB；实际叶 `IutInitialThetaArchimedeanPacketHull` 退出 0，107.364 秒、9,218,984 KiB，两叶最终日志全部为空，无错误或 warning。`Checks.SceneBounds`、`Axioms.SceneBounds`、`Act1Scene1` 依次退出 0，耗时 117.448、111.342、101.693 秒，峰值 RSS 依次 9,340,132、9,327,152、9,251,860 KiB。40/40 个新增公开声明逐名通过公理核对；1990 个打印声明仅含 `propext`、`Classical.choice`、`Quot.sound`，无 `sorryAx`，公理审计无 warning。静态导入审计覆盖 468 个可达本工程模块并确认所有 import 行均受扫描器覆盖；无 Obligations、Candidate、Scene2、Act2 或 `Iut.*` 导入。

三次失败均属 Lean API/化简适配：通用叶的 ENNReal 非负性调用 `zero_le _` 改为 `bot_le`（57.138 秒、峰值 4,990,208 KiB）；消费者的 Set.pi 函数参数未由 simp 逐点改写，改用显式 funext（104.223 秒、9,225,836 KiB）；径向产品的 `Fintype.card (Fin (j+1))` 不由 rfl 化简，改用 `Fintype.card_fin`（103.145 秒、9,219,008 KiB）。最终清除 unused simp 警告，未改变目标或数学前提；未发生 heartbeat / 内存失败。

本轮共 8 次直接 Lean 任务（5 成功、3 失败），累计 762.106 秒，进程组峰值 9,340,132 KiB。全部使用 CPU affinity `0–13`、`LEAN_NUM_THREADS=10`、Lean `-j1`，实际并发 worker 峰值 1；每 0.5 秒采样进程组 RSS，85 GiB 停止线未触发（用户上限 90 GiB）。只用 `lake env lean -j1 -o` 访问现有依赖产物，未调用 Lake build 调度器、冷构建、重编 Mathlib 或变更冻结工具链/依赖。

### Actual ordinary tensor log-shell 的 normalization 饱和及 packet 包含

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-LOCAL-TENSOR-SATURATED-LOG-SHELL` | `LocalCompletion.Packet.{factorLogShell_isCompact,exists_factorLogShell_coordinate_bound,tensorLogShell_isBounded,tensorLogShell_isOpen,tensorLogShell_isCompact,tensorLogShell_haar_pos,saturatedLogShell,tensorLogShell_subset_saturatedLogShell,saturatedLogShell_eq_leastHull,saturatedLogShell_isCompact,saturatedLogShell_isOpen,saturatedLogShell_haar_pos_lt_top,normalization_subset_saturatedLogShell,saturatedLogShell_mul_mem,saturatedLogShell_le_iff,saturatedLogShell_normalizationLogVolume_nonneg,tensorLogShell_logVolume_le_saturatedLogShell}`；`Act1Scene1/LocalCompletionTensorSaturatedLogShell.lean` | reference `LocalConstruct/LogShell.lean` 的 tensorLogShell / logShell 区分普通 ℤₚ tensor span 与 normalization-module saturation，integral_subset_logShell / isCompact_logShell 指出应证明的局部法律；Joshi III tensor log-shell 与 principal hull（3568–3574）提供来源背景。原创消费者使用实际 completion logShell_isCompact，连续基坐标给每因子 uniform bound，再以 tensor basis product 和 ultrametric span induction 得实际 tensorLogShell 有界；包含 unitLattice 推出紧开、正 Haar。定义 saturatedLogShell=normalizationHull(tensorLogShell)，通过已证 normalizationHull_eq_leastHull 获得紧开和正有限 Haar；1 属于 ordinary tensor shell，因此 normalization 包含于其 span。证明 normalization-module 乘法稳定性、span universal law、非负 normalized log-volume 及 ordinary→saturated log 比较。无参考源码复制；证明结构复用本地 unitLattice 坐标界与已验收 hull API。 | Scene1/Derived；proved |
| `JT-SCENE1-INITIAL-THETA-FINITE-PACKET-LOG-SHELL` | `IutInitialThetaFinitePacketLogShell.{componentShell,region,region_isCompact,integralRegion_subset,source_region_subset,hull_region_subset,productMeasure_region,productMeasure_region_pos_lt_top,one_le_productMeasure_region,packetLogVolume,packetLogVolume_eq_productMeasure_log,packetLogVolume_nonneg,hull_packetLogVolume_le,source_packetLogVolume_le}`；`Act1Scene1/IutInitialThetaFinitePacketLogShell.lean` | reference `LocalConstruct/LogShell.lean` 的 integral containment / compactness、`Concrete/Container.lean` 的 logShell 产品和 `ThetaRegion.lean` 的 thetaComponent_subset_logShell 是装配参考；Joshi III tensor log-shell 和 weighted volume 提供后续身份目标。原创实际消费者在同一 D、每素数、每 Fin(j+1) capsule 的全部 torsion-place tuple 上取实际饱和 shell；产品紧，actual product Haar 正有限且 ≥1，integral/source/least-normalization-hull region 均包含于 shell region。沿用实际 tuple local-degree 权重，packet shell log 非负，精确等 log(product Haar)/[Kt:ℚ]^(j+1)，source packet / hull packet log 均不超过 shell packet log。无新增 source/containment/volume 证书参数。 | Scene1/Derived；proved |

所有命名空间均以前缀 `JoshiTeich.Act1Scene1` 开始。本轮无参考源码复制或许可证增量。该单元为实际有限处 container 补上 normalization-saturated ordinary tensor log-shell 的构造与局部包含/测度消费者；不把 ordinary tensor span 直接认作 normalization，也不把该普通对数 shell 识别为论文 H¹ₑ/BK log-shell。奇未分歧处 shell=normalization、全局 shell 有限支撑、factor automorphism 稳定性和实际 adelic logShell/source/hull 同一对象装配仍待后续单元完成。paper selected representative/relative-degree 权重、theta locus/hull/volume 身份、untilt/period 联合来源及最终 3.12 仍开放，G1–G4 保持 0/4。新增数学仅在 Scene1/Derived；Core 假设增量 0，Prologue-R5 不变，无边界变更或数学负面证据，不写入 log5。

验收（2026-10-19）：最终通用叶 `LocalCompletionTensorSaturatedLogShell` 退出 0，69.392 秒、进程组峰值 5,787,340 KiB；实际叶 `IutInitialThetaFinitePacketLogShell` 退出 0，107.197 秒、9,247,796 KiB，两叶最终日志全部为空，无错误或 warning。`Checks.SceneBounds`、`Axioms.SceneBounds`、`Act1Scene1` 依次退出 0，耗时 111.243、111.875、108.976 秒，峰值 RSS 依次 9,343,612、9,329,636、9,223,416 KiB。31/31 个新增公开声明逐名通过公理核对；2021 个打印声明仅含 `propext`、`Classical.choice`、`Quot.sound`，无 `sorryAx`，公理审计无 warning。静态导入审计覆盖 470 个可达本工程模块并确认所有 import 行均受扫描器覆盖；无 Obligations、Candidate、Scene2、Act2 或 `Iut.*` 导入。

一次通用叶失败（66.760 秒、峰值 5,775,276 KiB）：直接改写 p 会同时改写依赖 Packet 参数，motive 不合法；改为对已有 completion 紧性定理做剩余特征的 `simpa only`。其余两叶版本均证明成功；随后清除 factor compactness 及其 coordinate-bound 消费者冗余的 Fact/Fintype 参数，使日志无警告。参数变化后各重检叶模块，先前两次收尾 Checks 进程主动 SIGTERM（41.040、26.348 秒、退出 -15），均登记为中断，未计成功；其后完整最终审计全部成功。中间成功叶耗时 67.312、105.240、68.318、112.876 秒，其资源均纳入本轮总量。没有 heartbeat 或内存失败，未改变 shell、包含或体积目标及数学前提。

本轮共 12 次直接 Lean 任务（9 成功、1 失败、2 主动中断），累计 996.577 秒，进程组峰值 9,343,612 KiB。全部使用 CPU affinity `0–13`、`LEAN_NUM_THREADS=10`、Lean `-j1`，实际并发 worker 峰值 1；每 0.5 秒采样进程组 RSS，85 GiB 停止线未触发（用户上限 90 GiB）。只用 `lake env lean -j1 -o` 访问现有依赖产物，未调用 Lake build 调度器、冷构建、重编 Mathlib 或变更冻结工具链/依赖。

### Actual ordinary / saturated log-shell 的 factor 自同构稳定性

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-LOCAL-PADIC-LOG-FUNCTORIALITY` | `LocalPadicLog.{norm_lt_one_iff_tendsto_pow,norm_map_sub_one_lt,map_padicLog,image_logShell_subset}`；`Act1Scene1/LocalPadicLogFunctoriality.lean` | 独立适配 reference `refer/iut/Iut/Concrete/LocalConstruct/LogShell.lean`（64–115）。`norm(a)<1` 以 powers→0 刻画，连续环映射保持此条件；实际已证对数级数 HasSum 经连续映射后仍为同一系数的 log series，得到 ordinary log 相容性和 `(2p)⁻¹ log` shell 的 image 包含。无需另给 norm isometry 或 log 稳定性证书。IUT IV Proposition 1.2 和 Joshi III log-shells 为稳定性消费者的来源背景。 | Scene1/Derived；proved |
| `JT-SCENE1-LOCAL-TENSOR-LOG-SHELL-INDETERMINACY` | `LocalCompletion.Packet.{factorAut_image_logShell_subset,factorTensorAut_mem_tensorLogShell,factorTensorAut_mem_saturatedLogShell,factorTensorAut_apply_inverse_family,factorTensorAut_image_saturatedLogShell,factorIndeterminacyOrbit_saturatedLogShell,factorIndeterminacyOrbit_saturatedLogShell_haar_pos_lt_top}`；`Act1Scene1/LocalCompletionTensorLogShellIndeterminacy.lean` | 原创 tensor 消费者；reference `LocalConstruct/LogShell.lean` 的 mapAlgHom_image_logShell_subset / indAut_logShell 是明确目标。实际 factor 的 ℚₚ-linear algebra automorphism 因有限维而连续，消费新 ordinary-log functoriality；对 ℤₚ tensor span 和 normalization-module span 分别 induction，结合已证 normalization 稳定性得 image 包含；inverse family 给精确 image 等式及完整 factor orbit=saturatedLogShell，沿用实际 Haar 的正有限性。 | Scene1/Derived；proved |
| `JT-SCENE1-INITIAL-THETA-FINITE-PACKET-SHELL-INDETERMINACY` | `IutInitialThetaFinitePacketLogShellIndeterminacy.{Automorphisms,packetMap,packetMap_inverse_family,packetMap_bijective,packetMap_mem_region,packetMap_image_region,componentOrbit_eq_shell,componentOrbit_isCompact,componentOrbit_haar_pos_lt_top}`；`Act1Scene1/IutInitialThetaFinitePacketLogShellIndeterminacy.lean` | 原创实际消费者；reference `Concrete/Container.lean` 的全部 tuple packet product 和 `LocalConstruct/LogShell.lean` 的 indAut_logShell。同一 D、同一 p/j 上，对每个 tuple 和每个 label 独立选择真实 completion-factor algebra automorphism，构造 packetTotal 映射，证明 inverse family、双射、shell region 的完整 image 等式；actual component orbit=shell 并保紧性、正有限 Haar。未用独立 carrier 或外给稳定性证书代替实际源。 | Scene1/Derived；proved |

上述命名空间均以前缀 `JoshiTeich.Act1Scene1` 开始。移植前已核对 LogShell 文件头及双方 LICENSE：Apache-2.0；Git 作者 Christian Merten，文件作者 The iut contributors。原提交 `fe96f99cae5c6d48d25113163f1b9b388fc35814`、参考快照 `07cb1da58f6d428a670dbb5dd6093d428bcbcdd8`；移植文件保留版权/许可证头并记录路径、作者、提交及使用本地 2p 定义的改写范围。后两文件为原创消费者，无源码复制；未依赖或导入 refer/iut，无新增许可证。

本单元只关闭实际 completion-factor 自同构及其 tensor/全部 tuple packet 对 ordinary saturated shell 的稳定性；未将此族识别为论文全部 Ind1–Ind3，不识别 H¹ₑ/BK、different-untilt、paper theta locus/hull/volume 或 selected representative 权重。奇未分歧处 shell=normalization、全局 shell 有限支撑和完整 RHSData/source 身份仍待完成，G1–G4 保持 0/4。新增结果均在 Scene1/Derived；Core 假设增量 0，Prologue-R5 不变，旧公开类型不变，没有动态边界变更或数学负面证据，不写入 log5。

验收（2026-10-19）：最终三个新叶日志全部为空，无错误或 warning。`LocalPadicLogFunctoriality` 退出 0，53.154 秒、进程组峰值 4,402,572 KiB；`LocalCompletionTensorLogShellIndeterminacy` 68.835 秒、5,787,756 KiB；`IutInitialThetaFinitePacketLogShellIndeterminacy` 107.235 秒、9,232,288 KiB。`Checks.SceneBounds`、`Axioms.SceneBounds`、`Act1Scene1` 依次退出 0，耗时 114.399、108.329、110.376 秒，峰值 RSS 依次 9,345,592、9,331,492、9,212,728 KiB。20/20 个新增公开声明逐名通过公理核对；2041 个打印声明仅含 `propext`、`Classical.choice`、`Quot.sound`，无 `sorryAx`，公理审计无 warning。静态导入审计覆盖 473 个可达本工程模块，所有 import 行均受扫描器覆盖；无 Obligations、Candidate、Scene2、Act2 或 `Iut.*` 导入。

第一次 ordinary-log 叶失败（56.210 秒、峰值 4,395,884 KiB）：未打开本地赋值 norm 所需的 `Valued` scope，导致 Norm k 实例未被选中；补 `open scoped Valued` 后通过。tensor 和实际 packet 两叶首次均通过；未发生 heartbeat / 内存失败，没有改目标或数学前提。

本轮共 7 次直接 Lean 任务（6 成功、1 失败），累计 618.538 秒，进程组峰值 9,345,592 KiB。全部使用 CPU affinity `0–13`、`LEAN_NUM_THREADS=10`、Lean `-j1`，实际并发 worker 峰值 1；每 0.5 秒采样进程组 RSS，85 GiB 停止线未触发（用户上限 90 GiB）。只用 `lake env lean -j1 -o` 访问现有依赖产物，未调用 Lake build 调度器、冷构建、重编 Mathlib 或变更冻结工具链/依赖。

### Actual unramified shell 等式与 adelic shell 的共同有限支撑

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-LOCAL-UNRAMIFIED-LOG-SHELL` | `LocalCompletion.{norm_le_prime_of_norm_lt_one_of_unramified,logShell_eq_closedBall_of_unramified,dvd_differentIdeal_of_ramIdx_ne_one,ramified_finite}`；`Act1Scene1/LocalCompletionUnramifiedLogShell.lean` | 独立适配 reference `LocalConstruct/PadicLog.lean` 的 logShell_subset_closedBall / logShell_eq_closedBall，`LogShell.lean` 的 factorLogShell_eq_of_unramified 及 `Arithmetic.lean` 的 ramified_finite。实际 completion 的 residue characteristic 赋值已证为 exp(-e)，e=1 使其为 uniformizer；离散指数给 norm(a)<1→norm(a)≤norm(p)。结合已证 log series bound、奇素数 norm(2)=1 和实际小球满射，得到 ordinary 2p shell=整数球。实际 e!=1 的处整除非零 different 理想，以 normalizedFactors 的有限性得到 ramified places 有限。IUT I Definition 5.4.5 / IUT IV Proposition 1.2 为 log-shell 来源；different 仅用于当前前置 ramification 支撑事实，不引入 Scene2 主界估计。 | Scene1/Derived；proved |
| `JT-SCENE1-LOCAL-TENSOR-UNRAMIFIED-LOG-SHELL` | `LocalCompletion.Packet.{factorLogShell_eq_closedBall_of_unramified,tensorLogShell_eq_unitLattice_of_unramified,saturatedLogShell_eq_normalization_of_unramified}`；`Act1Scene1/LocalCompletionTensorUnramifiedLogShell.lean` | 原创消费者；reference LogShell 的 tensorLogShell_eq_order_of_unramified / logShell_eq_integral_of_unramified。在实际 completion Packet 上逐因子 e=1 且 p 为奇素数时，ordinary tensor shell 精确等于 tensor unitLattice；对 normalization-module span 使用其 universal law 与 1 的包含，证明饱和 shell 精确等于 actual normalization。没有假定 tensor unit order=normalization。 | Scene1/Derived；proved |
| `JT-SCENE1-INITIAL-THETA-ADELIC-LOG-SHELL` | `IutInitialThetaAdelicLogShell.{ramifiedPrimes,ramIdx_eq_one_of_not_ramifiedPrimes,exceptionalPlaces,region,finite_region_eq_integral_of_unramified,region_eq_integralRegion_of_not_exceptional,region_isCompact,packetMeasure_region_pos_lt_top,hull_region_subset,source_region_subset,region_support_subset,region_finite_support,processionRegion_finite_support,containerRegion,hull_containerRegion_subset,containerRegion_nonempty,integral_eventually_of_mem_region,toContainer,toContainer_mem,packetLogVolume,packetLogVolume_nonneg,packetLogVolume_eq_zero_of_not_exceptional,packetLogVolume_support_subset,packetLogVolume_finite_support,globalLogVolume,globalLogVolume_eq_sum,globalLogVolume_nonneg,hull_packetLogVolume_le,hull_globalLogVolume_le,processionLogVolume,processionLogVolume_nonneg,hull_processionLogVolume_le}`；`Act1Scene1/IutInitialThetaAdelicLogShell.lean` | 原创实际消费者；reference Concrete/Container 的 logShell_finiteSupport、logShellAdmissible 及 LocalConstruct/LogShell 的 unramified equality。对同一 D 的实际 torsion field 所有 finite/infinite places、全部 Fin(j+1) tuple 和标准 procession 使用之前已证的 shell/测度/权重；actual ramifiedPrimes 是 e!=1 的有限处的 residue-char image，共同 exceptionalPlaces=∞、2 加 ramifiedPrimes image。证明例外集外全部 factor e=1、奇素数 shell product=integral 基准，因此所有 j 及整个 procession 同时有限支撑。逐处 shell 紧且 product Haar 正有限，包含已构造 source/hull；区域落在同一 restricted product 并非空。实际 shell packet log 在共同例外集外为零，全局 finsum 等于显式有限和，packet/global/procession log 非负；利用双方实际有限支撑及点态比较证明 hull global/procession log≤shell log。 | Scene1/Derived；proved |

上述命名空间均以前缀 `JoshiTeich.Act1Scene1` 开始。移植前核对参考 PadicLog、LogShell、Arithmetic 文件头和双方 LICENSE：Apache-2.0；Git 作者 Christian Merten，文件作者 The iut contributors。原提交分别 `bc1c6e6c7ac4bcf0c363b9b1bbe9b6d7bc35bf9c`、`fe96f99cae5c6d48d25113163f1b9b388fc35814`、`b76207ab8955e68a7408d5d2a770b75a30c3bebf`，参考快照 `07cb1da58f6d428a670dbb5dd6093d428bcbcdd8`。移植文件保留版权/许可证通知，并登记路径、作者、提交和 actual completion 改写范围；后两文件为原创消费者，无参考代码复制。未依赖或导入 refer/iut，无许可证增量。

本单元关闭当前 actual ordinary saturated tensor shell 的奇未分歧恒等式及整个 adelic / 标准 procession 的共同有限支撑；有限例外处的 shell 贡献保留在真实有限和中，未删去 ramification 或无限处。连同上一单元 factor stability，当前 actual container / hull / shell 的局部包含与全局支撑均已有无缺口来源消费者。仍未识别该 ordinary shell 与论文 H¹ₑ/BK、theta locus/hull/volume、selected representatives/relative-degree 权重；untilt/period 联合来源、完整 paper RHSData 身份及最终 3.12 仍开放，G1–G4 保持 0/4。新增数学仅在 Scene1/Derived，Core 假设增量 0，Prologue-R5 不变，无动态边界变更或数学负面证据，不写入 log5。

验收（2026-10-19）：最终三个新叶日志全部为空，无错误或 warning。`LocalCompletionUnramifiedLogShell` 一次通过，64.280 秒、进程组峰值 5,458,392 KiB；最终 `LocalCompletionTensorUnramifiedLogShell` 65.317 秒、5,751,612 KiB；`IutInitialThetaAdelicLogShell` 107.246 秒、9,233,624 KiB。`Checks.SceneBounds`、`Axioms.SceneBounds`、`Act1Scene1` 依次退出 0，耗时 115.885、114.138、115.512 秒，峰值 RSS 依次 9,348,928、9,334,596、9,253,124 KiB。39/39 个新增公开声明逐名通过公理核对；2080 个打印声明仅含 `propext`、`Classical.choice`、`Quot.sound`，无 `sorryAx`，公理审计无 warning。静态导入审计覆盖 476 个可达本工程模块，所有 import 行均受扫描器覆盖；无 Obligations、Candidate、Scene2、Act2 或 `Iut.*` 导入。

tensor 叶首版证明已通过（62.751 秒、峰值 5,727,612 KiB），清除一个冗余 Fintype 参数警告后重检。一次全局叶失败（114.398 秒、峰值 9,244,028 KiB）：字段调用的点号后直接换行违反语法，改成同一字段调用后通过；未改变目标或数学前提。第一次全局命令在进入 Lean 前被最终日志断言停止（因上述 tensor warning），没有启动 Lean，不计入直接 Lean 任务。没有 heartbeat 或内存失败。

本轮共 8 次直接 Lean 任务（7 成功、1 失败），累计 759.527 秒，进程组峰值 9,348,928 KiB。全部使用 CPU affinity `0–13`、`LEAN_NUM_THREADS=10`、Lean `-j1`，实际并发 worker 峰值 1；每 0.5 秒采样进程组 RSS，85 GiB 停止线未触发（用户上限 90 GiB）。只用 `lake env lean -j1 -o` 访问现有依赖产物，未调用 Lake build 调度器、冷构建、重编 Mathlib 或变更冻结工具链/依赖。

### Actual admissible 区域的 hull closure 与 adelic source 消费者

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-LOCAL-TENSOR-HULL-CLOSURE` | `LocalCompletion.Packet.{AdmissibleHullRegion,hullRegion,hullRegion_idem,hullClosure,hullClosure_isClosed_iff,integralHullRegion,hullClosure_integralHullRegion,saturatedShellHullRegion,hullClosure_saturatedShellHullRegion}`；`LocalArchimedean.{AdmissibleHullRegion,hullRegion,hullClosure,hullClosure_isClosed_iff,integralHullRegion,hullClosure_integralHullRegion,logShellHullRegion,hullClosure_logShellHullRegion}`；`Act1Scene1/LocalTensorHullClosure.lean` | reference `Cor312/HolomorphicHull.lean` 的 closureOperator、hull_idem 及 Joshi III principal hull（3568–3574）、`le:volume-lemma3` 提供目标。原创消费者在实际 Tensor 区域的 subtype `bounded ∧ positive normalizationHaar` 上，用已证 leastHull / radialHull 构造 Mathlib ClosureOperator；幂等性直接由各自 principal/radial 固定点和真实 hull multiplier 推出。证明 finite closure 的闭合对象恰为 unit multiplier 的 principal normalization 区域，infinite closure 的闭合对象恰为正实径向区域，并给 integral / actual saturated shell 固定点。没有加入 least-hull 存在性或闭包法律作为新假设。 | Scene1/Derived；proved |
| `JT-SCENE1-INITIAL-THETA-ADELIC-HULL-CLOSURE` | `IutInitialThetaAdelicHullClosure.{componentwiseClosure,PacketFamily,packetClosure,Family,adelicClosure,productRegion,productRegion_mono,integralFamily,packetClosure_integralFamily,adelicClosure_integralFamily,productRegion_integralFamily,shellFamily,adelicClosure_shellFamily,productRegion_shellFamily,sourceFamily,productRegion_sourceFamily,productRegion_closure_sourceFamily,sourceFamily_le_shellFamily,closure_sourceFamily_le_shellFamily,productRegion_subset_closure,family_support_closure_subset,family_finite_support_closure,sourceFamily_support_subset,sourceFamily_finite_support,closure_sourceFamily_finite_support,productRegion_closure_finite_support,productRegion_closure_idem}` 及 PacketFamily partial order；`Act1Scene1/IutInitialThetaAdelicHullClosure.lean` | reference `Concrete/Container.lean` 的 hull 及 `Cor312/ContainerHull.lean` 的 hullFamily / hull_integralRegion / hullAdmissible_idem 是明确装配来源。原创消费者对同一 D 的所有 p / infinity / Fin(j+1) tuple 以实际 admissible component 区域为载体，逐组件、逐有理处构造闭包。integral/shell family 均为固定点，actual source family 的闭包产品精确等于现有 actual adelic hull；source≤shell 由实际包含证明，闭包 source≤shell 从单调性和 shell 固定点导出。integral 固定点使任意 finite-support admissible family 的支撑在闭包下只缩小；实际 source 的共同 exceptionalPlaces 推出 source / closure source 有限支撑，并将这一性质传给闭包 product regions。整个实际 source、hull、shell 消费链无需外给 HullSystem 或 hull-existence 证书。 | Scene1/Derived；proved |

本节所有命名空间均以前缀 `JoshiTeich.Act1Scene1` 开始。无新源码移植或许可证增量。该单元把已证明的实际局部 hull 提升为 admissible 区域上的真正闭包操作，并在当前全部 tuple / rational-place source 上实际消费，补上参考 ContainerHull 的扩张/单调/幂等和支撑保持连接；没有仅通过一个未实例化的新接口转移证明义务。它仍只描述当前 ordinary q-root container 的 principal/radial hull，不识别论文 theta source、selected representative 权重、H¹ₑ/BK、untilt/period 或 paper thetaVolume / 完整 RHSData。G1–G4 保持 0/4；新增数学仅在 Scene1/Derived，Core 假设增量 0，Prologue-R5 不变，无动态边界变更或数学负面证据，不写入 log5。

验收（2026-10-19）：最终通用叶 `LocalTensorHullClosure` 退出 0，73.511 秒、进程组峰值 5,776,172 KiB；实际叶 `IutInitialThetaAdelicHullClosure` 一次通过，116.099 秒、9,242,568 KiB，两叶最终日志全部为空，无错误或 warning。`Checks.SceneBounds`、`Axioms.SceneBounds`、`Act1Scene1` 依次退出 0，耗时 124.643、115.477、113.955 秒，峰值 RSS 依次 9,352,488、9,338,188、9,195,160 KiB。44/44 个新增公开声明逐名通过公理核对；2124 个打印声明仅含 `propext`、`Classical.choice`、`Quot.sound`，无 `sorryAx`，公理审计无 warning。静态导入审计覆盖 478 个可达本工程模块，所有 import 行均受扫描器覆盖；无 Obligations、Candidate、Scene2、Act2 或 `Iut.*` 导入。新增直接 Mathlib 导入 `Order.Closure` 已核对预编译 olean。

一次通用叶失败（68.333 秒、峰值 5,776,384 KiB）：对子类型 coe equality 的 `subst` 不适用，改用已证最小性和包含的双向 Set.Subset；saturated shell 固定点的 hull multiplier 及其 admissibility 需显式指定，补齐后通过；同时打开集合缩放的 Pointwise scope。未改变目标或数学前提，没有 heartbeat 或内存失败。

本轮共 6 次直接 Lean 任务（5 成功、1 失败），累计 612.018 秒，进程组峰值 9,352,488 KiB。全部使用 CPU affinity `0–13`、`LEAN_NUM_THREADS=10`、Lean `-j1`，实际并发 worker 峰值 1；每 0.5 秒采样进程组 RSS，85 GiB 停止线未触发（用户上限 90 GiB）。只用 `lake env lean -j1 -o` 访问现有依赖产物，未调用 Lake build 调度器、冷构建、重编 Mathlib 或变更冻结工具链/依赖。


### Actual finite packet 的素数逆像与 normalization log-volume 缩放

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-LOCAL-TENSOR-PRIME-LOG-VOLUME` | `LocalCompletion.Packet.{primePreimage,natCast_mul_eq_smul,normalizationHaar_primePreimage,primePreimage_measurableSet,primePreimage_haar_pos_lt_top,normalizationLogVolume_primePreimage}`；`Act1Scene1/LocalCompletionTensorPrimeLogVolume.lean` | 独立适配 `refer/iut/Iut/Concrete/LocalConstruct/Volume.lean`（277–300）的 corrected `componentVol_prime_preimage'`；`Cor312/LogVolume.lean` 的 `componentVol_prime_preimage` 将区域限制在正有限 principal regions。IUT III Proposition 3.9(i) 为 normalization 来源。实际 completion Packet 的 natCast 乘法等于 Qp scalar action，使用本地已证 PadicHaar 的 Haar modulus 得 `μ(p⁻¹U)=p^dim μ(U)`，证明可测性及正有限测度保持，再用真实 tensor 维数正性推出 normalized log 增加 log p。必要的可测、正有限测度条件均保留，不对零测度或无限测度集合断言此法律。 | Scene1/Derived；proved |
| `JT-SCENE1-INITIAL-THETA-FINITE-PACKET-PRIME-LOG-VOLUME` | `IutInitialThetaFinitePacketPrimeLogVolume.{familyLogVolume,primePreimageFamily,familyLogVolume_eq_productMeasure_log,componentLogVolume_primePreimage,familyLogVolume_primePreimage,primePreimageFamily_haar_pos_lt_top,productMeasure_log_primePreimage,source_primePreimage_logVolume,hull_primePreimage_logVolume,shell_primePreimage_logVolume}`；`Act1Scene1/IutInitialThetaFinitePacketPrimeLogVolume.lean` | 原创实际消费者；reference `Concrete/Container.lean` 的 tupleWeight / vol 和 `Cor312/LogVolume.lean` 的 componentVol_prime_preimage / packetVol 指出装配。对同一 D 的全部有限处和全部 Fin(j+1) tuple 使用真实 component region family、normalization Haar 及 local-degree tuple weights；familyLogVolume 等于实际 product Haar 的实对数除 `[Kt:Q]^(j+1)`。正有限可测 family 的 prime-preimage 仍正有限，其 weighted log 恰增加 log p，维数和 tuple 个数均不作为额外因子；证明由真实 tupleWeight_sum_one 消去该系数。source、principal hull、饱和普通 log-shell 三个消费者直接从已有紧性及 Haar 正有限性提供输入，无新增几何 certificates。 | Scene1/Derived；proved |

本节命名空间均以前缀 `JoshiTeich.Act1Scene1` 开始。移植前核对参考 `Volume.lean` 文件头及双方 LICENSE：Apache-2.0；Git 作者 Christian Merten，文件作者 The iut contributors，原提交 `b76207ab8955e68a7408d5d2a770b75a30c3bebf`，参考快照 `07cb1da58f6d428a670dbb5dd6093d428bcbcdd8`。通用叶保留版权、许可证、原路径、作者、提交及 actual normalization 改写范围；packet 叶为原创消费者。没有依赖或导入 refer/iut，没有改动冻结环境。

本单元补齐当前实际 container 的一个 reference LogVolumeData 局部法律并给出实际三类区域消费者；没有把这些 full torsion-field/local-degree 权重识别为论文 selected representatives/relative-degree 权重，也没有识别 paper theta locus/hull/volume、H¹ₑ/BK 或 untilt/period 联合来源。不宣称已构造完整 RHSData 或最终 3.12；G1–G4 保持 0/4。新增数学只在 Scene1/Derived，Core 假设增量 0，Prologue-R5 不变；无动态边界变更或数学负面证据，不写入 log5。


编辑期三次失败均已修正并复验：通用叶首检 72.525 秒、峰值 RSS 5,484,240 KiB，补齐实际 factor 的 FiniteDimensional 局部实例，用已证 scalar identity 给出连续性，并用 ENNReal 的非零乘积证明正性，清除冗余 Fintype section 参数 warning；第二次 67.926 秒、5,493,080 KiB，将连续性证明中的 scalar 明确为 `(p : ℚ_[p])`。packet 叶首检 118.554 秒、9,244,232 KiB，将 productMeasure 的乘积公式显式命名，并用 calc 对齐 sum/div 后通过，同时清除 unused simp warning。没有修改数学目标或添加前提，没有 heartbeat / 内存失败。


验收（2026-10-19）：最终通用叶 `LocalCompletionTensorPrimeLogVolume` 退出 0，85.722 秒、进程组峰值 RSS 5,501,448 KiB；实际 packet 叶 `IutInitialThetaFinitePacketPrimeLogVolume` 退出 0，120.750 秒、9,247,908 KiB。两叶最终日志均为空，无错误或 warning。`Checks.SceneBounds`、`Axioms.SceneBounds`、`Act1Scene1` 依次退出 0，耗时 126.280、122.722、119.221 秒，峰值 RSS 依次 9,354,020、9,339,612、9,255,272 KiB。16/16 个新增公开声明逐名通过公理核对；全部 2140 个打印声明仅含 `propext`、`Classical.choice`、`Quot.sound`，无 `sorryAx`，公理审计和聚合日志无 warning。静态导入审计覆盖 480 个可达本工程模块，全部 import 行形式均受扫描器覆盖；无 Obligations、Candidate、Scene2、Act2 或 `Iut.*` 导入。

本轮共 8 次直接 Lean 任务（5 成功、3 失败），成功累计 574.695 秒、失败累计 259.005 秒、总计 833.700 秒；进程组峰值 RSS 9,354,020 KiB（8.921 GiB）。全部使用 CPU affinity `0–13`、`LEAN_NUM_THREADS=10`、Lean `-j1`，实际并发 worker 峰值 1；每 0.5 秒采样进程组 RSS，85 GiB 停止线未触发（用户上限 90 GiB）。只用 `lake env lean -j1 -o` 访问现有依赖产物，未调用 Lake build 调度器、冷构建、重编 Mathlib 或变更冻结工具链/依赖。


### Actual admissible adelic family 的三层加权 log-volume 与 hull 消费

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-INITIAL-THETA-ARCHIMEDEAN-PACKET-LOG-VOLUME` | `LocalArchimedean.{factor_finrank_eq_mult,tensor_finrank_eq_mult_prod}`；`IutInitialThetaArchimedeanPacketLogVolume.{tupleWeight_eq_dimension_div_degree,weighted_normalizationLogVolume,familyLogVolume,familyLogVolume_eq_productMeasure_log,packetLogVolume_eq_productMeasure_log}`；`Act1Scene1/IutInitialThetaArchimedeanPacketLogVolume.lean` | reference `Concrete/Container.lean` 的 weight / tupleWeight / vol、`Cor312/LogVolume.lean` 的 packetVol_product 及 Joshi III ss:weighted-vol 指出目标。实际 real/complex Factor 的 ULift 与 archField 子代数计算给 real dimension=处 mult，实际 tensor basis 给 dimension=mult 乘积；据此消去同一 D 的全部 infinite-place tuple weights 与 component 的维数分母。对任意正有限 component 区域证明 weighted family log=实际 product Haar 实对数 / `[Kt:Q]^(j+1)`，并在已有 π-shell factor-orbit source 上消费。 | Scene1/Derived；proved |
| `JT-SCENE1-INITIAL-THETA-ADELIC-FAMILY-LOG-VOLUME` | `IutInitialThetaAdelicFamilyLogVolume.{packetMeasure_productRegion_pos_lt_top,productRegion_nonempty,packetLogVolume,finite_packetLogVolume_eq_weighted,infinite_packetLogVolume_eq_weighted,packetLogVolume_integral,packetLogVolume_mono,AdmissibleFamily,integralAdmissibleFamily,closureFamily,packetLogVolume_support_subset,packetLogVolume_finite_support,globalLogVolume,globalLogVolume_eq_sum,globalLogVolume_mono,globalLogVolume_integral,globalLogVolume_le_closure,globalLogVolume_closure_idem,sourceAdmissibleFamily,shellFamily_finite_support,shellAdmissibleFamily,globalLogVolume_closure_le_shell,packetLogVolume_source,packetLogVolume_hull,packetLogVolume_shell,globalLogVolume_source,globalLogVolume_hull,globalLogVolume_shell,processionLogVolume,processionLogVolume_mono,processionLogVolume_integral,processionLogVolume_le_closure,processionLogVolume_closure_idem,processionLogVolume_closure_le_shell,processionLogVolume_source,processionLogVolume_hull,processionLogVolume_shell}`；`Act1Scene1/IutInitialThetaAdelicFamilyLogVolume.lean` | reference `Cor312/LogVolume.lean` 的 packetVol_product、finite_support_packetVol、globalVol、processionVol 与 `ContainerHull.lean` 的 hullFamily 提供装配目标。对同一 D 的真实有限／无限处 PacketFamily 定义统一 packet functional = product Haar log / `[Kt:Q]^(j+1)`，实际两处分支各自证明 weighted combination；bounded positive-Haar component subtype 自身提供正有限性，故 product 区域非空、正有限。integral log=0，包含推出 packet log 单调。AdmissibleFamily 以相对 integral 的真实有限支撑为 subtype 条件，全局 finsum 有限、等于显式有限和且单调；closureFamily 消费已证实际 closure/support preservation，给 global log 不减及幂等。实际 shell family 的有限支撑由已有 shell region 支撑和正测度区域非空性导出；shell 固定点给任意所含 family 的 closure global 上界。标准 procession 保留独立的 unweighted capsule average，同样单调、integral=0、闭包不减／幂等及 shell 上界。source、closure source hull、shell 三个实际对象在 packet/global/procession 全部精确还原原有 volume，完成通用生产者到实际消费者的连接。 | Scene1/Derived；proved |

本节声明命名空间均以前缀 `JoshiTeich.Act1Scene1` 开始。两文件为本工程原创证明和消费者，无参考源码复制或许可证增量；不依赖 refer/iut。该单元将此前分散于 source/hull/shell 的测度和局部权重接到实际任意 admissible component family 的三层 functional，尤其补上无限处 tensor dimension / mult 权重的 product-Haar accounting。没有把最终下界、volume identity 或任意几何 certificate 改成接口假设，也不在非有限支撑 family 上宣称全局单调性。仍未识别论文 selected representatives/relative-degree 权重、theta locus/hull/volume、H¹ₑ/BK 或 untilt/period 联合来源；完整 RHSData 与最终 3.12 仍开放，G1–G4 保持 0/4。数学仅在 Scene1/Derived；Core 假设增量 0，Prologue-R5 不变，无动态边界变更或数学负面证据，不写入 log5。


编辑期失败记录：无限处叶首检 108.888 秒、峰值 RSS 9,087,360 KiB，冻结版 `finrank_ulift` 位于根命名空间，修正名称；第二次 110.000 秒、9,084,640 KiB，`unfold Factor` 后留下的旧实例阻止 implicit-transparency 改写，改用完整 `change` 重建 canonical ULift 模块目标后通过。统一叶首检 115.555 秒、9,249,048 KiB：将两个分支的 product Haar 公式显式命名后同时用于正性和有限性；support 的 lambda 应用先 change 到显式 packetLogVolume 目标；integral family 的空支撑证明改用 simp，清除弃用 Set.setOf_false 的 warning。目标及数学前提均保持原样，无 heartbeat 或内存失败。


验收（2026-10-19）：最终无限处 accounting 叶 `IutInitialThetaArchimedeanPacketLogVolume` 退出 0，108.842 秒、进程组峰值 RSS 9,082,108 KiB；统一 family 叶 `IutInitialThetaAdelicFamilyLogVolume` 退出 0，114.419 秒、9,252,412 KiB。两叶最终日志均为空，无错误或 warning。`Checks.SceneBounds`、`Axioms.SceneBounds`、`Act1Scene1` 依次退出 0，耗时 128.280、122.148、117.550 秒，峰值 RSS 依次 9,357,936、9,343,224、9,255,768 KiB。44/44 个新增公开声明逐名通过公理核对；全部 2184 个打印声明仅含 `propext`、`Classical.choice`、`Quot.sound`，无 `sorryAx`，公理审计和聚合日志无 warning。静态导入审计覆盖 482 个可达本工程模块，全部 import 行形式均受扫描器覆盖；无 Obligations、Candidate、Scene2、Act2 或 `Iut.*` 导入。

本轮共 8 次直接 Lean 任务（5 成功、3 失败），成功累计 591.239 秒、失败累计 334.443 秒、总计 925.682 秒；进程组峰值 RSS 9,357,936 KiB（8.924 GiB）。全部使用 CPU affinity `0–13`、`LEAN_NUM_THREADS=10`、Lean `-j1`，实际并发 worker 峰值 1；每 0.5 秒采样进程组 RSS，85 GiB 停止线未触发（用户上限 90 GiB）。只用 `lake env lean -j1 -o` 访问现有依赖产物，未调用 Lake build 调度器、冷构建、重编 Mathlib 或变更冻结工具链/依赖。


### Actual finite q-root 点轨道、normalization hull 与体积身份

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-LOCAL-TENSOR-POINT-ORBIT-HULL` | `LocalCompletion.Packet.{factorPointOrbit,mem_factorPointOrbit,factorTensorAut_mem_factorPointOrbit,factorPointOrbit_finite,factorPointOrbit_isCompact,factorPointOrbit_subset_thickOrbit,thickOrbit_subset_normalizationHull_points,normalizationHull_factorPointOrbit,normalizationHull_pointOrbit_le_iff,normalizationHull_purePointOrbit_eq_leastHull,normalizationHull_purePointOrbit_haar_pos_lt_top,normalizationHaar_singleton_eq_zero,factorPointOrbit_haar_eq_zero}`；`Act1Scene1/LocalCompletionTensorPointOrbitHull.lean` | Joshi III principal hull（3568–3574）、convex/hull 比较（3597–3609）及 single-point witness（3624–3631）提供目标；reference `ThetaRegion.thetaFinite` 与 `Cor312/RightHandSide` 的 images→hull→log-volume 指出当前 container 的连接。直接使用已验收实际 factorTensorAut 与 normalization 稳定性，证明任意点 a 的有限 factorPointOrbit 和 factorIndeterminacyOrbit(principalRegion a) 生成相同 normalization module：前者包含于后者，后者中每个 φ(a*r)=φ(a)*φ(r) 都由 φ(a) 的 normalization 倍数生成。对 pure z、各 z_i 非零，精确接到已有 scalar-region leastHull，得到正有限 Haar。span 的普遍性质给点包含与 hull 包含的等价，目标 principal multiplier 不必先假定单位。已有 proper Qp-subspace nullity用于零子空间，再用 Haar 平移不变性给单点零测度，有限点轨道因而零测度。没有要求 raw point set 正 Haar。 | Scene1/Derived；proved |
| `JT-SCENE1-INITIAL-THETA-FINITE-POINT-ORBIT-HULL` | `IutInitialThetaFinitePointOrbitHull.{componentPoints,scaleElt_mem_componentPoints,componentPoints_finite,componentPoints_isCompact,componentPoints_haar_eq_zero,componentPoints_subset_source,componentHull,componentHull_eq_existing,componentPoints_subset_hull,componentHull_isCompact,componentHull_haar_pos_lt_top,componentHull_le_principalRegion_iff,pointRegion,pointRegion_isCompact,witness_mem_pointRegion,pointRegion_nonempty,productMeasure_pointRegion_eq_zero,hullRegion,hullRegion_eq_existing,pointRegion_subset_hull,hullRegion_le_principalProduct,hullRegion_eq_integral_of_not_bad,hullRegion_finite_support,packetHullLogVolume,packetHullLogVolume_eq_existing,packetHullLogVolume_eq_productMeasure_log,hullPacketFamily,hullPacketFamily_eq_existing,hullAdmissibleFamily,hullAdmissibleFamily_eq_existing,globalHullLogVolume_eq_existing,processionHullLogVolume_eq_existing}`；`Act1Scene1/IutInitialThetaFinitePointOrbitHull.lean` | 原创实际消费者，对同一 D、每个 p、全部 Fin(j+1) tuple 的实际 scaleElt=incl_d(qroot^j²) 构造有限点轨道和 normalization span。证明 component span 等于之前已证的 least principal componentHull，继承其紧性与 Haar 正有限；raw 点区域紧且由原 witness 实际非空，packet product Haar=0 使用实际 tuple 非空而非任意指定坐标。pointHull 的 packet 产品等于原 packet hull，并从 raw 点产品的包含独立给出任意 principal 产品中的最小性，hull 在共同 badChars 外等于 integral。实际权重下 packetHullLogVolume 等于现有 hull log 及实际 product-Haar log/[Kt:Q]^(j+1)。hullPacketFamily 在有限处使用这些点生成 spans，无穷处保留现有实际径向 hull；证明 family 精确等于已有 actual source 的 adelic closure，故属于实际 finite-support AdmissibleFamily，global/procession 体积与现有实际 hull 完全相同。 | Scene1/Derived；proved |

以上命名空间均以前缀 `JoshiTeich.Act1Scene1` 开始。两文件均为本工程原创证明，无参考代码复制或许可证增量，不依赖 refer/iut。本单元把先前 normalization-thickened q-root 区域的 hull/volume 接回实际有限 factor-aut 点轨道，正有限测度和全局 admissibility 均在取 hull 后由证明给出。Raw 点的零测度是本构造的局部事实，未用它反驳任何论文 locus，也未把 Real.log(0) 当作论文 log-volume。没有声称该有限 factor orbit 包含论文全部 Ind1–Ind3、实际 theta-values locus 或跨 holomorphoid 的 collation；H¹ₑ/BK、untilt/period、selected representatives/relative-degree 权重及 paper thetaVolume 身份仍开放，最终 3.12 和 G1–G4 未关闭。数学仅在 Scene1/Derived；Core 假设增量 0，Prologue-R5 不变，无动态边界变更或对既有契约的数学反例，不写入 log5。


编辑期失败记录：通用叶首检 67.396 秒、峰值 RSS 5,487,140 KiB，normalization 成员资格和 normalizationHull 成员资格在 implicit-transparency 改写时需要显式 Set 目标，补齐 coe 类型并先 change/rw 到真实 map_mul 目标后通过；同时将 proof 内 haveI/letI 改为冻结版 linter 要求的 have/let，清除 style warning。实际消费者首检 112.439 秒、9,253,300 KiB，IsCompact 的 Submodule-to-Set coercion 需显式 tensor 元素类型；有限支撑的 set membership 目标需先 by_contra 再使用非坏特征等式，修正后复验。没有 heartbeat / 内存失败，定理目标和数学前提均未改变。


验收（2026-10-19）：最终通用叶 `LocalCompletionTensorPointOrbitHull` 退出 0，63.253 秒、进程组峰值 RSS 5,486,768 KiB；实际 packet 消费者 `IutInitialThetaFinitePointOrbitHull` 退出 0，115.493 秒、9,247,128 KiB。两叶最终日志均为空，无错误或 warning。`Checks.SceneBounds`、`Axioms.SceneBounds`、`Act1Scene1` 依次退出 0，耗时 123.109、113.997、115.019 秒，峰值 RSS 依次 9,361,556、9,346,792、9,261,156 KiB。45/45 个新增公开声明逐名通过公理核对；全部 2229 个打印声明仅含 `propext`、`Classical.choice`、`Quot.sound`，无 `sorryAx`，公理审计和聚合日志无 warning。静态导入审计覆盖 484 个可达本工程模块，全部 import 行形式均受扫描器覆盖；无 Obligations、Candidate、Scene2、Act2 或 `Iut.*` 导入。

本轮共 7 次直接 Lean 任务（5 成功、2 失败），成功累计 530.871 秒、失败累计 179.835 秒、总计 710.706 秒；进程组峰值 RSS 9,361,556 KiB（8.928 GiB）。全部使用 CPU affinity `0–13`、`LEAN_NUM_THREADS=10`、Lean `-j1`，实际并发 worker 峰值 1；每 0.5 秒采样进程组 RSS，85 GiB 停止线未触发（用户上限 90 GiB）。只用 `lake env lean -j1 -o` 访问现有依赖产物，未调用 Lake build 调度器、冷构建、重编 Mathlib 或变更冻结工具链/依赖。


### Actual factor 轨道与 normalization hull 稳定性、Haar 不变性

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-LOCAL-TENSOR-HULL-INDETERMINACY` | `LocalCompletion.Packet.{factorTensorAut_comp_family,factorTensorAut_image_orbit_subset,factorTensorAut_image_orbit,factorIndeterminacyOrbit_idem,factorTensorAut_image_normalizationHull_subset,factorTensorAut_image_orbitHull,factorIndeterminacyOrbit_orbitHull,factorTensorAut_det_norm,normalizationHaar_factorTensorAut_image,normalizationLogVolume_factorTensorAut_image}`；`Act1Scene1/LocalCompletionTensorHullIndeterminacy.lean` | reference `LocalConstruct/Indeterminacy.lean` 的 mapAlgHom/span transport 以及 ThetaRegion 的 factor-image source 提供具体操作；Joshi III principal hull 与 convex/hull 比较提供 hull 目标。实际 factorTensorAut 的按分量复合由 tensor algHom ext 证明；有限 factor 轨道在各 factorTensorAut 下不变，完整轨道操作幂等。normalization-module span 通过生成元、加法及 normalization 缩放的归纳证明 transport，轨道的 span 因而不变，重复取 factor 轨道也不变。实际 normalization 保持与其 normalizationHaar=1，结合本工程已证 p-adic Haar determinant modulus，证明该 tensor automorphism 的 determinant norm=1；因此对任意集合 U，实际 Haar(φ''U)=Haar(U)，归一化 real log-volume 同样不变，无需另给 Haar-preserving certificate 或正有限／可测输入。对退化集仅声明数值函数的不变性，不赋予其论文 log-volume 语义。 | Scene1/Derived；proved |
| `JT-SCENE1-INITIAL-THETA-FINITE-HULL-INDETERMINACY` | `IutInitialThetaFiniteHullIndeterminacy.{componentPointOrbit_image,componentSource_image,componentHull_image,componentHull_orbit_eq_self,packetMap_image_product,packetMap_image_pointRegion,packetMap_image_sourceRegion,packetMap_image_hullRegion,productMeasure_packetMap_image_product,weightedLogVolume_image_family,productLogVolume_packetMap_image}`；`Act1Scene1/IutInitialThetaFiniteHullIndeterminacy.lean` | 原创实际消费者，同一 D 的全部 p / Fin(j+1) tuple 上独立选择实际 completion-factor 自同构，使用已构造 packetMap。实际 component point orbit 与 thickened source 都是完整 factor 轨道，所以各自 image 等于自身；实际 componentHull 已由上轮识别为 point orbit 的 normalization span，故继承 image/orbit 固定性。packetMap_image_product 从逐分量 image 构造全 tuple witness，得到 packet 的 point/source/hull image 等式。每分量的 Haar 不变性通过实际 Measure.pi_pi 乘积推出任意 product region 的 packetMap-image product Haar 不变，再证明同一 local-degree tuple weights 下的加权 component log 以及 global-degree^(j+1) 分母的 product log 不变。 | Scene1/Derived；proved |

上述命名空间均以前缀 `JoshiTeich.Act1Scene1` 开始。两文件为本工程原创证明，无参考代码复制或许可证增量，不依赖 refer/iut。此次首次把实际 factor 代数自同构作用接到已构造 q-root hull 的稳定性，并从实际 normalization Haar 推导体积不变性，未增加自由的几何或 measure-preserving 输入。按用户指定的 Joshi 优先语义，III 2727–2749 将 Ind2 关联不同 arithmetic holomorphic structures／Fargues–Fontaine points，将 Ind1 关联 anabelomorphy，将 Ind3 关联 crystalline/Frobenius；本轮有限 factor 自同构结果只覆盖当前 container 的明确操作，不足以识别这些论文对象，不以 reference 把它们全称 indeterminacy automorphisms 的说明替代来源比较。真实 theta locus、H¹ₑ/BK、跨 holomorphoid collation、untilt/period 联合来源、selected representative 权重、paper thetaVolume 与最终 3.12 均仍开放，G1–G4 保持 0/4。数学仅在 Scene1/Derived，Core 假设增量 0，Prologue-R5 不变；无动态边界变更或新数学负面证据，不写入 log5。


验收（2026-10-19）：通用叶 `LocalCompletionTensorHullIndeterminacy` 首次通过，66.824 秒、进程组峰值 RSS 5,775,240 KiB；实际 packet 消费者 `IutInitialThetaFiniteHullIndeterminacy` 首次通过，114.514 秒、9,250,928 KiB。两叶最终日志均为空，无错误或 warning。`Checks.SceneBounds`、`Axioms.SceneBounds`、`Act1Scene1` 依次首次通过，耗时 116.984、107.760、109.867 秒，峰值 RSS 依次 9,364,016、9,349,192、9,257,200 KiB。21/21 个新增公开声明逐名通过公理核对；全部 2250 个打印声明仅含 `propext`、`Classical.choice`、`Quot.sound`，无 `sorryAx`，公理审计和聚合日志无 warning。静态导入审计覆盖 486 个可达本工程模块，全部 import 行形式均受扫描器覆盖；无 Obligations、Candidate、Scene2、Act2 或 `Iut.*` 导入。新增源码未含 sorry/admit/自定义 axiom/opaque。

本轮共 5 次直接 Lean 任务，全部成功，无失败或中断，累计 515.949 秒；进程组峰值 RSS 9,364,016 KiB（8.930 GiB）。全部使用 CPU affinity `0–13`、`LEAN_NUM_THREADS=10`、Lean `-j1`，实际并发 worker 峰值 1；每 0.5 秒采样进程组 RSS，85 GiB 停止线未触发（用户上限 90 GiB）。无 heartbeat override。只用 `lake env lean -j1 -o` 访问现有依赖产物，未调用 Lake build 调度器、冷构建、重编 Mathlib 或变更冻结工具链/依赖。


### Actual q-root 单 witness 的 adelic hull-volume 下界

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-INITIAL-THETA-ADELIC-WITNESS-HULL-BOUND` | `IutInitialThetaAdelicWitnessHullBound.{RawPacketFamily,RawFamily,componentHull,componentHull_subset_normalization,componentHull_isCompact,componentHull_haar_pos_lt_top,componentHull_eq_normalization_of_not_bad,hullFamily,hullFamily_support_subset,hullAdmissibleFamily,hullFamily_mono,singletonFamily,singletonFamily_hull_le,singleton_componentHull_eq_principal,singleton_packetLogVolume_eq,packetLogVolume_lower_bound,hullFamily_le_shell,packetLogVolume_nonpos,globalLogVolume_eq_finite_add_arch,singleton_globalLogVolume_eq,globalLogVolume_bounds,processionLogVolume,singleton_processionLogVolume_eq,processionLogVolume_bounds,pointOrbitFamily,sourceRegionFamily,pointOrbit_hullFamily_eq_existing,sourceRegion_hullFamily_eq_existing,pointOrbit_processionLogVolume_eq_existing,sourceRegion_processionLogVolume_eq_existing}`；`Act1Scene1/IutInitialThetaAdelicWitnessHullBound.lean` | Joshi III `le:volume-lemma3`（3576–3588）及 `th:moccor-Mochizuki-form2` 的 standard-point witness（3624–3631）提供“含 tensor witness 后取 hull”的比较方向；reference `Cor312/RightHandSide` 保留 images→hull→procession volume 次序。本轮以真实 InitialThetaData、全部 finite p / Fin(j+1) tuple 的 scaleElt=指定因子 qroot^j² 为 witness。RawPacketFamily 要求 raw set 包含该点并位于实际 normalization 内，无 raw Haar 正性、完整 source／orbit 包含、finite-support 或 volume 下界字段。已有 pure witness 生成定理直接给 normalization span 的紧性、正有限 Haar；在 badChars 外 witness=1，normalization 缩放生成整个 normalization，因此全 adelic hull family 自动在共同 exceptionalPlaces 外等于 integral。无穷处分支明确保留现有实际 π-shell，未从有限 witness 推导其性质。singletonFamily 的 hull 精确为 principalRegion scaleElt，component log 的既有 determinant/norm 身份与 tuple marginal 会计给 packet log=-j² log(p)·actual vbadWeightedFiber；实际 q-pilot regrouping 给 singleton global=A_j-j²Q，标准 procession=A-squareAverage·Q。singleton⊆raw 提供 hull 单调性，因此任意 RawFamily 的 global/procession 均在这一 baseline 与实际 arch contribution 之间，有限处分量 log 非正且 hull≤actual shell。pointOrbitFamily 与 sourceRegionFamily 从现有真实构造提供两种实际 raw 满足者，构造 hull family／procession 体积精确还原已有实际 hull；没有仅建立一个未实例化的 conditional consumer。 | Scene1/Derived；proved |

全部命名空间带前缀 `JoshiTeich.Act1Scene1`。本文件为本工程原创证明，无参考代码复制或许可证增量，不依赖 refer/iut。本单元把局部的 pure-point normalization span 生产者提升为同一 actual q-pilot 的全局有限支撑下界，移除旧区域比较路线对 raw source 正 Haar／包含整个 thickened source 的要求。这里的 normalization-module hull、full torsion-field local-degree 权重和 q-root witness 仍是明确的当前对象；未识别为论文 H¹ₑ/BK witness、theta_M locus、selected representatives/relative-degree 权重或 paper thetaVolume。下界保留 j² 及 squareAverage，不将其改成最终 3.12 系数；无限处贡献保留 A，不假定 adelic log 非正。G1–G4 与最终 3.12 仍未完成。数学只在 Scene1/Derived，Core 假设增量 0，Prologue-R5 不变，无动态边界变更或数学负面证据，不写入 log5。


编辑期失败记录：叶首检 113.933 秒、峰值 RSS 9,261,832 KiB，给 normalizationHull 的 Set coercion 显式 tensor 类型；统一 finsum 改写前展开 hullAdmissibleFamily；无限处 orbit→shell→radialHull 等式方向修正。第二次 116.588 秒、9,257,944 KiB，RawPacketFamily subtype 的 witness 属性使直接改写 scaleElt=1 产生不合法 motive，改用固定 raw set 上的 congrArg 成员命题等价；shell 包含的有限处分支显式 intro c，修正布局解析。没有改变 raw 条件、体积目标或系数，未出现 heartbeat／内存失败。

第三次叶检查 109.848 秒、峰值 RSS 9,257,504 KiB，仅剩 Submodule 成员与显式 Set coercion 在 simpa 后的实例不对齐；改为先 change 到原 Submodule 成员目标，再直接使用 smul_mem 化简后的证明。所有其余声明均已通过该次检查，无 warning。


验收（2026-10-19）：最终叶 `IutInitialThetaAdelicWitnessHullBound` 退出 0，112.945 秒、进程组峰值 RSS 9,259,264 KiB；最终日志为空，无错误或 warning。`Checks.SceneBounds`、`Axioms.SceneBounds`、`Act1Scene1` 依次首次通过，耗时 117.488、113.465、115.040 秒，峰值 RSS 依次 9,366,744、9,351,724、9,232,704 KiB。30/30 个新增公开声明逐名通过公理核对；全部 2280 个打印声明仅含 `propext`、`Classical.choice`、`Quot.sound`，无 `sorryAx`，公理审计和聚合日志无 warning。静态导入审计覆盖 487 个可达本工程模块，全部 import 行形式均受扫描器覆盖；无 Obligations、Candidate、Scene2、Act2 或 `Iut.*` 导入。新增源码未含 sorry/admit/自定义 axiom/opaque。

本轮共 7 次直接 Lean 任务（4 成功、3 失败），成功累计 458.938 秒、失败累计 340.369 秒、总计 799.307 秒；进程组峰值 RSS 9,366,744 KiB（8.933 GiB）。全部使用 CPU affinity `0–13`、`LEAN_NUM_THREADS=10`、Lean `-j1`，实际并发 worker 峰值 1；每 0.5 秒采样进程组 RSS，85 GiB 停止线未触发（用户上限 90 GiB）。无新增 heartbeat override。只用 `lake env lean -j1 -o` 访问现有依赖产物，未调用 Lake build 调度器、冷构建、重编 Mathlib 或变更冻结工具链/依赖。


### Actual witness hull 的有限 Haar 乘积与 selected paper-root 比较

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-INITIAL-THETA-WITNESS-HULL-HAAR-PRODUCT` | `IutInitialThetaWitnessHullHaarProduct.{packetVolume,packetVolume_eq_exp,packetVolume_pos,packetVolume_le_one,packetVolume_eq_one_of_not_bad,finiteVolume,finiteVolume_pos,finiteVolume_le_one,finiteVolume_eq_exp,log_finiteVolume,adelic_exp_eq_finite_mul_arch,finiteVolume_lower_bound,singleton_finiteVolume_eq,finiteProcessionVolume,finiteProcessionVolume_eq_exp,finiteProcessionVolume_pos,finiteProcessionVolume_le_one,log_finiteProcessionVolume,adelicProcession_exp_eq_finite_mul_arch,finiteProcessionVolume_lower_bound,singleton_finiteProcessionVolume_eq,selectedPaperRootProduct_pow_lt_finiteProcessionVolume,neg_abs_log_finiteProcessionVolume,finiteProcessionCost_lt_weightedPaperSum,pointOrbit_finiteProcessionVolume_eq,sourceRegion_finiteProcessionVolume_eq}`；`Act1Scene1/IutInitialThetaWitnessHullHaarProduct.lean` | Joshi III `ss:weighted-vol`、`le:volume-lemma3`、`th:moccor-Mochizuki-form2` 的 multiplicative adelic volume 和 `Cor312/LogVolume.lean` 的 component/packet/procession 独立归一化提供目标。packetVolume 直接定义为已有实际 hull family 的 product Haar 实值的 1/[Kt:Q]^(j+1) 次幂，以前轮已证 Haar 正有限性证明它等于 exp(packetLogVolume)。finiteVolume 为共同 badPrimes 上 packetVolume 的真实有限乘积，证明正性、≤1、集外因子=1，精确 log=实际 adelic global log减实际 arch contribution A_j；完整 exp(adelicLog)=finiteVolume*exp(A_j) 保留无穷处。finiteProcessionVolume 是这些 finiteVolume 的乘积再取 1/ellStar 次幂，log 精确等于已有 procession log减实际 arch procession A。singleton raw witness 的 finite/procession volume 精确为 exp(-j²Q)／exp(-squareAverage·Q)，任意 raw witness family 的实际 Haar product 下界由已有 log 下界推出。actualSelectedPaperRootNormProduct 的严格 q-accounting (`referenceAbsLogQ < selectedPaperSum`) 仅用于有向比较，得 paperProduct^squareAverage < finiteProcessionVolume，等价 negative log成本 < squareAverage*selectedPaperSum。volume∈(0,1] 使 negative absolute log=log，未对完整 adelic log强加符号。最后实际 point-orbit／thickened-source 消费者的 finiteProcessionVolume 都等于相同旧 actual hull procession log减 A 后的 exponential，连接实际生产者。 | Scene1/Derived；proved |

命名空间带前缀 `JoshiTeich.Act1Scene1`。本文件为本工程原创证明，无参考代码复制或许可证增量，不依赖 refer/iut。此次补上前轮 log-volume 下界的真实有限 Haar 乘积和几何平均消费者，而非自由给定一个待证 volume identity；无限处贡献明确保留在乘法分解中。既有 representative ramification gap 只供不等式方向，未把 full torsion-field tuple weights 识别为 paper selected representative／inverse relative-degree 权重，未改写或取消 squareAverage，未把这个实际 finite product 命名为 thetaVolume。真实 theta locus／BK witness、untilt/period 联合模型及 paper thetaVolume 身份仍开放；最终 3.12、G1–G4 均未关闭。数学只在 Scene1/Derived，Core 假设增量 0，Prologue-R5 不变，无动态边界变更或数学负面证据，不写入 log5。


验收（2026-10-19）：叶 `IutInitialThetaWitnessHullHaarProduct` 首次通过，115.479 秒、进程组峰值 RSS 9,239,716 KiB；日志为空，无错误或 warning。`Checks.SceneBounds`、`Axioms.SceneBounds`、`Act1Scene1` 依次首次通过，耗时 123.032、122.134、117.546 秒，峰值 RSS 依次 9,368,656、9,353,300、9,236,136 KiB。26/26 个新增公开声明逐名通过公理核对；全部 2306 个打印声明仅含 `propext`、`Classical.choice`、`Quot.sound`，无 `sorryAx`，公理审计和聚合日志无 warning。静态导入审计覆盖 488 个可达本工程模块，全部 import 行形式均受扫描器覆盖；无 Obligations、Candidate、Scene2、Act2 或 `Iut.*` 导入。新增源码未含 sorry/admit/自定义 axiom/opaque。

本轮共 4 次直接 Lean 任务，全部成功，无失败或中断，累计 478.191 秒；进程组峰值 RSS 9,368,656 KiB（8.935 GiB）。全部使用 CPU affinity `0–13`、`LEAN_NUM_THREADS=10`、Lean `-j1`，实际并发 worker 峰值 1；每 0.5 秒采样进程组 RSS，85 GiB 停止线未触发（用户上限 90 GiB）。无新增 heartbeat override。只用 `lake env lean -j1 -o` 访问现有依赖产物，未调用 Lake build 调度器、冷构建、重编 Mathlib 或变更冻结工具链/依赖。


### Actual 全 finite tuple 的原 integral Kummer normalized-log tensor 与 hull-volume 身份

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-LOCAL-TENSOR-NORMALIZED-LOG-HULL` | `LocalCompletion.Packet.{logHull_norm_prime_lt_one,paperLogScalars,paperLogScalars_norm,paperLogScalars_ne_zero,paperLogPrincipalUnit,paperLogIntegralClass,paperLogIntegralClass_normalizedLog,paperLogIntegralClass_has_integralLift,scalarNormalization_paperLogScalars,factorOrbitScalarRegion_paperLogScalars,singletonHull_paperLogScalars,pointOrbitHull_paperLogScalars}`；`Act1Scene1/LocalCompletionTensorNormalizedLogHull.lean` | Joshi III `eq:bloch-kato-log-class`（3226）、`le:elem-lemma`（3394–3430）与 standard-point witness（3624–3631）给目标表达式。本工程实际 Packet 的每个 factor 提供 completion 的 canonical Qp algebra、连续 action、有限维性和 prime norm<1。对任意因子 integral scalar z_i，构造 principal unit 1+pStar*z_i 及其在该 completion 的 AlgebraicClosure 上的原 principalIntegralClass（standard continuous H¹ coefficient image 中已有 integralKummerSubmodule），由现有 normalizedIntegralKummerLog_principal 证明 normalized ordinary-log 值精确为 paperNormalizedLog，且 class 确实有原 integral coefficient lift。对非零 z_i，已有 elem-lemma norm 等式给 normalized scalar 非零及相同范数；本地 equal-norm scalar lattice／normalization 定理进一步给整个 principal region 相等，因而 thickened finite factor orbit、singleton normalization hull 与 point-orbit-generated module hull均相等。没有用自由 norm、volume 或 cohomology certificate 代替这些证明。 | Scene1/Derived；proved |
| `JT-SCENE1-INITIAL-THETA-FINITE-NORMALIZED-LOG-HULL` | `IutInitialThetaFiniteNormalizedLogHull.{logScalars,integralClass,integralClass_normalizedLog,logScalars_norm,logScalars_ne_zero,witness,witness_eq_integralLogTensor,witness_singletonHull_eq_principal,componentPoints,componentHull,componentHull_eq_existing,thickenedOrbit_eq_source,componentHull_isCompact,componentHull_haar_pos_lt_top,hullFamily,hullFamily_eq_existing,hullAdmissibleFamily,hullAdmissibleFamily_eq_existing,globalLogVolume_eq_existing,processionLogVolume_eq_existing,finitePacketVolume,finitePacketVolume_eq_existing,finiteProcessionVolume,finiteProcessionVolume_eq_existing,selectedPaperProduct_pow_lt_finiteProcessionVolume}`；`Act1Scene1/IutInitialThetaFiniteNormalizedLogHull.lean` | 原创实际消费者，把上述每因子 producer 应用于同一 D、每个有限 p、全部 Fin(j+1) tuple 的真实 scalars（指定因子为 vbadQroot^j²，其余为1）。每个因子的实际 integralClass 由构造给出；witness_eq_integralLogTensor 明确是这些原类的 normalized ordinary-log 值的 pure tensor。注意其余因子是 paperNormalizedLog(1)，不是将 log value 武断设为1；它们的 norm=1 足以保持 principal 区域。normalized-log scalar 的 thickened orbit 精确等于原 q-root source，点轨道 hull 精确等于原 componentHull；从该 hull 的实际紧性／正有限 Haar 构造统一 family，证明它与旧 actual point-orbit hull family相同，所以同一有限支撑、global/procession log-volume 身份均从对象等式得到。finitePacketVolume 直接使用新 normalized-log hull 的 product Haar 及实际全局次数根，finiteProcessionVolume 使用共同 badPrimes 与独立 capsule 几何平均；证明其等于已有实际 Haar product，继承 selected paperRootProduct^squareAverage 的严格下界。无限处分支明确保留已有实际径向 hull。 | Scene1/Derived；proved |

声明命名空间均带前缀 `JoshiTeich.Act1Scene1`。两文件为本工程原创证明，无参考源码复制或许可证增量，不依赖 refer/iut。该单元把已有单处／selected block 的 ordinary-log/Kummer 来源接到当前 full finite-place tuple container 与真实 Haar 产品，减少后续消费者需外给 normalized-log witness／hull identity 的负担。它未把 ordinary normalized map 改名为 BK log，也未将 integralKummerSubmodule 识别为论文 H¹ₑ；跨 holomorphoid collation、different-untilt j²/n² 估值关系、paper selected representative 权重与 thetaVolume 身份仍需证明。保留 squareAverage 及原 q-pilot accounting，最终 3.12 与 G1–G4 均未关闭。数学只在 Scene1/Derived，Core 假设增量 0，Prologue-R5 不变；无动态边界变更或数学负面证据，不写入 log5。


编辑期记录：通用叶首版 proof 全部通过，67.873 秒、峰值 RSS 5,781,580 KiB；移除 norm-prime、factor norm、normalized-log 和 integral-lift 定理冗余的 Fact／Fintype section 参数 warning 后重检。实际消费者首检失败，106.831 秒、9,249,288 KiB：normalization-module 等式转 Set 等式的 congrArg lambda 需显式标注 Submodule 类型，补齐后复验；其余所有实际消费者及 Haar product 连接均通过该次检查，无 warning。没有改变数学前提或目标，无 heartbeat／内存失败。


验收（2026-10-19）：最终通用叶 `LocalCompletionTensorNormalizedLogHull` 退出 0，69.402 秒、进程组峰值 RSS 5,770,768 KiB；实际消费者 `IutInitialThetaFiniteNormalizedLogHull` 退出 0，107.811 秒、9,249,376 KiB。两叶最终日志均为空，无错误或 warning。`Checks.SceneBounds`、`Axioms.SceneBounds`、`Act1Scene1` 依次首次通过，耗时 121.584、112.886、111.431 秒，峰值 RSS 依次 9,372,228、9,357,176、9,258,424 KiB。37/37 个新增公开声明逐名通过公理核对；全部 2343 个打印声明仅含 `propext`、`Classical.choice`、`Quot.sound`，无 `sorryAx`，公理审计和聚合日志无 warning。静态导入审计覆盖 490 个可达本工程模块，全部 import 行形式均受扫描器覆盖；无 Obligations、Candidate、Scene2、Act2 或 `Iut.*` 导入。新增源码未含 sorry/admit/自定义 axiom/opaque。

本轮共 7 次直接 Lean 任务（6 成功、1 失败；包括首版有 warning 的通用叶成功编译），成功累计 590.987 秒、失败累计 106.831 秒、总计 697.818 秒；进程组峰值 RSS 9,372,228 KiB（8.938 GiB）。全部使用 CPU affinity `0–13`、`LEAN_NUM_THREADS=10`、Lean `-j1`，实际并发 worker 峰值 1；每 0.5 秒采样进程组 RSS，85 GiB 停止线未触发（用户上限 90 GiB）。无新增 heartbeat override。只用 `lake env lean -j1 -o` 访问现有依赖产物，未调用 Lake build 调度器、冷构建、重编 Mathlib 或变更冻结工具链/依赖。


### Actual normalized-log collation 的原始 hull 下界与 integral-class image 消费者

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-INITIAL-THETA-NORMALIZED-LOG-COLLATION` | `IutInitialThetaNormalizedLogCollation.{RawFamily,witness_mem_normalization,rootWitness_mem_normalizationHull,rootAdapter,normalizationHull_rootAdapter,componentHull,componentHull_eq_adapter,componentHull_isCompact,componentHull_haar_pos_lt_top,hullFamily,hullFamily_eq_adapter,hullAdmissibleFamily,hullAdmissibleFamily_eq_adapter,globalLogVolume_bounds,finiteProcessionVolume,finiteProcessionVolume_eq_adapter,finiteProcessionVolume_bounds,IntegralClassTuple,classLogScalar,classLogTensor,standardClassTuple,standardClassTuple_log,ClassFamily,rawLogImage,singletonClassFamily,singletonClassFamily_image,singletonClassFamily_hullFamily,classImageVolume,classImageVolume_bounds,singletonClassImageVolume_eq}`；`Act1Scene1/IutInitialThetaNormalizedLogCollation.lean` | Joshi III `pr:general-cohomology-set-const`（3261–3271）的 class images、`eq:bloch-kato-log-class`（3226）及 `th:moccor-Mochizuki-form2` 的 standard-point containment（3624–3631）提供消费顺序。RawFamily 的原始 tensor set 只要求含实际 normalized ordinary-log witness 且位于 normalization 内；由该 witness 的 singleton normalization hull=实际 q-root principalRegion，推出 q-root 属于原始 span。rootAdapter 在 raw set 中 insert q-root 以接入已有 consumer，但 normalizationHull_rootAdapter 证明 span 完全不变；公开 componentHull 仍直接定义为原始 set 的 normalizationHull。由此构造紧正有限 Haar 的实际 hull family 及其有限支撑 AdmissibleFamily，global log 的上下界和 actual finiteProcessionVolume 的正性／≤1／selected paper product 下界均从同一 span 身份传递，而非假定 raw Haar 正性或 volume identity。IntegralClassTuple 是每个实际 completion 的原 integralKummerSubmodule 的 dependent tuple；classLogScalar 为真实 normalizedIntegralKummerLogEquiv，classLogTensor 为它们的 pure tensor。ClassFamily 要求标准 actual class tuple 成员性及各 normalized-log norm≤1，rawLogImage 从真实 image 构造 tensor set，单位格包含于 normalization 提供上界。singletonClassFamily 使用已构造实际 integralClass，并从其 normalizedLog／norm 定理证明全部输入；像集精确为 normalized-log witness 单点，其 hull family 精确为旧 q-root singleton baseline，classImageVolume 精确为 exp(-squareAverage*Q)。 | Scene1/Derived；proved |

全部命名空间带前缀 `JoshiTeich.Act1Scene1`。本文件为本工程原创证明，无参考源码复制或许可证增量，不依赖 refer/iut。本单元不再要求 normalized-log collation 本身含原 q-root，仍按原始像集取 hull；adapter 只用于证明复用，并已证明不改变对象。class-image 的 norm≤1 是显式几何条件，标准 singleton 真实 producer 提供满足模型，无 raw positive-Haar、finite-support 或定量下界作为输入。它只消费同一组 completions 内的 standard continuous H¹ integral images，不构造来自不同 arithmeticoids 的传递同构，也不声称这些类为 H¹ₑ/BK。跨 holomorphoid collation、different-untilt 估值／paper weights／theta locus 与 thetaVolume 身份仍开放；保留 squareAverage 和实际无限处贡献，G1–G4 及最终 3.12 未关闭。数学仅在 Scene1/Derived，Core 假设增量 0，Prologue-R5 不变，无动态边界变更或数学负面证据，不写入 log5。


编辑期记录：class-image collation 叶首检在默认 200000 heartbeat 下 172.683 秒、峰值 RSS 9,385,900 KiB 超时；依用户顺序将该 class-dependent 段一次提高到 `maxHeartbeats 1000000` 后通过，耗时 152.618 秒、峰值 RSS 9,395,772 KiB，日志为空。未进行额外优化或继续翻倍。

验收（2026-10-19）：`IutInitialThetaNormalizedLogCollation` 最终退出 0，152.618 秒、进程组峰值 RSS 9,395,772 KiB；最终日志为空，无错误或 warning。`Checks.SceneBounds`、`Axioms.SceneBounds`、`Act1Scene1` 依次首次通过，耗时 124.130、（同一审计进程最终日志无 warning）、112.932 秒，峰值 RSS 依次 9,372,656、9,357,176、9,237,724 KiB。30/30 个新增公开声明逐名通过公理核对；全部 2373 个打印声明仅含 `propext`、`Classical.choice`、`Quot.sound`，无 `sorryAx`。静态导入审计覆盖 491 个可达本工程模块，全部 import 行形式均受扫描器覆盖；无 Obligations、Candidate、Scene2、Act2 或 `Iut.*` 导入。新增源码未含 sorry/admit/自定义 axiom/opaque。

本轮共 7 次直接 Lean 任务（6 成功、1 次 heartbeat 失败后按约定重试成功），成功累计 676.255 秒、失败累计 172.683 秒、总计 848.938 秒；进程组峰值 RSS 9,395,772 KiB（8.961 GiB）。全部使用 CPU affinity `0–13`、`LEAN_NUM_THREADS=10`、Lean `-j1`，85 GiB 停止线未触发；未重编 Mathlib。


上一单元资源记录更正（依据 `/tmp/scene1-log-collation-{leaf-1,leaf-2,final-audit-metrics}.jsonl` 的实际任务记录）：`Axioms.SceneBounds` 耗时为 111.425 秒、进程组峰值 RSS 9,359,904 KiB。直接 Lean 任务共 5 次（4 成功、1 heartbeat 失败），成功累计 501.105 秒、失败 172.683 秒、总计 673.788 秒；先前的“7 次／676.255 秒／848.938 秒”和公理任务峰值不正确，以上数值取代它们。该更正不涉及任何数学验收结论。


### Actual normalized-log collation 的 factor 轨道饱和与 hull/volume 消费

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-INITIAL-THETA-LOG-COLLATION-ORBIT` | `IutInitialThetaLogCollationOrbit.{saturate,subset_saturate,saturate_mono,saturate_idem,saturate_component_image,saturatedHull_component_image,saturatedHull_packet_image,hullFamily_mono,hullFamily_le_saturatedHull,globalLogVolume_le_saturatedHull,finiteProcessionVolume_mono,finiteProcessionVolume_le_saturatedHull,standardOrbitFamily,standardOrbitFamily_component,standardOrbitFamily_hullFamily,standardOrbitFamily_globalLogVolume,standardOrbitFamily_finiteProcessionVolume,standardOrbitFamily_volume_bounds}`；`Act1Scene1/IutInitialThetaLogCollationOrbit.lean` | reference `LocalConstruct/Indeterminacy.lean` 的实际 factor tensor maps／span transport 与 `Cor312/RightHandSide.lean` 的 images→hull→volume 组织为明确操作来源；Joshi III `pr:general-cohomology-set-const`、`th:thetam-construction` 给后续来源比较目标。saturate 对任意实际 normalized-log RawFamily 逐 p／tuple 取已构造全部 factor 自同构的 orbit，identity image 保留 witness，实际 normalization 稳定性给 upper containment。证明 saturation 扩张、单调、幂等，饱和 raw 集及其 normalization span 在每个 factorTensorAut 下不变，进一步证明独立逐 tuple 自同构的 packetMap 保持整个 hull 产品。hull inclusion 推出 actual global log 在 saturation 下不减，有限支撑由既有原始 witness hull family 构造提供；finiteProcessionVolume_mono 直接以 actual product Haar 的单调性和正有限性，在同一全局次数根和 capsule root下证明包含单调，再消费于 saturation。standardOrbitFamily 是真实 standard integralClass tuple 的 singleton normalized-log image 的 full factor orbit，逐分量等于已验收 normalized-log componentPoints，故其整个 hull family／global log／finite procession Haar product 均精确等于现有 actual normalized-log orbit hull，并继承正性、≤1 与 paperRootProduct^squareAverage 严格下界。 | Scene1/Derived；proved |

全部声明带命名空间前缀 `JoshiTeich.Act1Scene1`。本文件为本工程原创证明，无新参考源码复制或许可证增量，不依赖 refer/iut。该单元闭合当前实际 normalized-log class-image 在有限 factor 操作下的饱和与 hull/volume 连接，生产者是真实 integralClass singleton 的 normalized-log image，操作来自真实 completion-factor algebra automorphisms。它不在 cohomology 上人为共轭 normalized-log 来宣称一个来源同构，不识别不同 arithmetic holomorphic structures 或 Fargues–Fontaine points，亦未识别 Joshi 的全部 Ind1–Ind3、H¹ₑ/BK／跨 arithmeticoid collation 或 paper theta locus/volume。权重、squareAverage、无限处实际贡献均沿用之前定义；最终 3.12、G1–G4 仍开放。数学只在 Scene1/Derived；Core 假设增量 0，Prologue-R5 不变，无动态边界变更或数学负面证据，不写入 log5。


编辑期失败记录：新叶首检 114.495 秒、峰值 RSS 9,255,016 KiB，标准 singleton class image 的饱和 hull 等式中 `change` 需要显式标注 Submodule-to-Set 的 tensor 元素类型，补齐后复验；其余全部声明通过首检，无 warning。没有 heartbeat 或内存失败，未改变数学目标或前提。


验收（2026-10-19）：最终叶 `IutInitialThetaLogCollationOrbit` 退出 0，115.476 秒、进程组峰值 RSS 9,252,396 KiB；日志为空，无错误或 warning。`Checks.SceneBounds`、`Axioms.SceneBounds`、`Act1Scene1` 依次首次通过，耗时 122.593、128.784、121.225 秒，峰值 RSS 依次 9,376,952、9,361,808、9,258,304 KiB。18/18 个新增公开声明逐名通过公理核对；全部 2391 个打印声明仅含 `propext`、`Classical.choice`、`Quot.sound`，无 `sorryAx`，公理审计和聚合日志无 warning。静态导入审计覆盖 492 个可达本工程模块，全部 import 行形式均受扫描器覆盖；无 Obligations、Candidate、Scene2、Act2 或 `Iut.*` 导入。新增源码未含 sorry/admit/自定义 axiom/opaque。

本轮共 5 次直接 Lean 任务（4 成功、1 失败），成功累计 488.078 秒、失败累计 114.495 秒、总计 602.573 秒；进程组峰值 RSS 9,376,952 KiB（8.943 GiB）。全部使用 CPU affinity `0–13`、`LEAN_NUM_THREADS=10`、Lean `-j1`，实际并发 worker 峰值 1；每 0.5 秒采样进程组 RSS，85 GiB 停止线未触发（用户上限 90 GiB）。无新增 heartbeat override。只用 `lake env lean -j1 -o` 访问现有依赖产物，未调用 Lake build 调度器、冷构建、重编 Mathlib 或变更冻结工具链/依赖。


### Actual completion 整数环的 p-adic 完备性及 Fontaine 代数桥接

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-LOCAL-COMPLETION-ADIC-FONTAINE` | `LocalCompletion.{integerRing_prime_norm_lt_one,integerRing_prime_nonunit,integerRing_isAdic,integerRing_isAdicComplete,integerRing_primeNonunitFact,integerCoefficientMap,integerCoefficientMap_coe,integerCoefficientMap_injective,completionPlaceData,completionPlaceData_laws,completionBridgeData,completionBridgeData_laws}`；`Act1Scene1/LocalCompletionAdicFontaine.lean` | Mathlib `RingTheory/AdicCompletion/Topology.lean` 的 `isAdic_iff`、`IsAdic.isAdicComplete_iff`，`NumberTheory/NumberField/Completion/FinitePlace.lean` 的实际 completion embedding／整数范数界，以及现有 `LocalCompletionHaarIndex` 的主理想闭球／开性和紧整数环。对实际 `O_w = integerRing w`、`p = Arithmetic.residueChar w`，证明 `‖(p : completionAt K w)‖ < 1`、`¬IsUnit (p : O_w)` 及 `IsAdic (Ideal.span {(p : O_w)})`：每个主理想幂非零因而开；`‖p‖^n → 0` 保证理想幂包含于每个原拓扑零邻域。已有紧性给 CompleteSpace，Hausdorff 性给 T2，再由 Mathlib 等价得到实际 `IsAdicComplete (Ideal.span {(p : O_w)}) O_w`，不重新定义拓扑。`integerCoefficientMap : 𝓞 K →+* O_w` 为实际 completion embedding 的整数限制，其底层值等于 `FinitePlace.embedding w.maximalIdeal (a : K)`，由原嵌入单射证明它单射。canonical PreTilt untiltMap／Witt-vector thetaMap 据此产生现有 `PerfectoidPlaceData` 及法律，并对每个 `L : AdelicThetaLinkData K` 和 `hw : w ∈ L.places` 提供 `PerfectoidBridgeData L p (completionPlaceData w)` 与 `PerfectoidBridgeLaws`。 | Scene1/Derived；proved |
| `JT-SCENE1-INITIAL-THETA-COMPLETION-FONTAINE` | `InitialThetaCompletionFontaine.{placeData,placeData_place,placeData_laws,bridgeData,bridgeData_laws,bridgeData_coefficientMap,bridgeData_coefficientMap_injective}`；`Act1Scene1/IutInitialThetaCompletionFontaine.lean` | Joshi III `se:theta-data` 和实际 `IutInitialThetaLinkSource` 的 Tate 支持处给出消费者位置。对同一 `D : InitialThetaData AG TG` 及 `w : (iutInitialThetaTateParameterData D).places`，`placeData` 的底环取实际 `LocalCompletion.integerRing w.1`、素数取实际剩余特征、处精确等于 `w.1`；其法律由通用叶生产。`bridgeData` 接入同一 `AdelicThetaLinkData.ofInitialThetaData D theta thetaBase packetHull heightData ramification logVolume processionLength`，支持法律直接消费 `w.2`；其 coefficient map 的底层值精确等于实际 `FinitePlace.embedding w.1.maximalIdeal (a : D.F)`，单射性由生产者给出。theta／thetaBase／packetHull／heightData／ramification／logVolume／processionLength 仍为显式参数，不宣称本单元构造它们。 | Scene1/Derived；proved |

上述声明均带前缀 `JoshiTeich.Act1Scene1`，包括两个新的公开 instance `integerRing_isAdicComplete`、`integerRing_primeNonunitFact`，全部登记于 Checks／Axioms 家族。两叶均为本工程原创证明，无参考代码复制或许可证增量，不导入 refer/iut。

来源身份范围：Joshi I `def:arith-hol-strs`（766 起）、`def:untilt-galois`（1470 起）以及 `Arithmetic Holomorphic Structures.tex` 的 `lem:perfectoid`（574–581）使用带 isometric embedding 的代数闭、完备非阿基米德域及其 tilt／untilt。这里的 `completionAt K w` 是实际数域有限处的 completion；本轮没有将其离散赋值整数环识别为论文的 perfectoid 对象。Mathlib Fontaine theta 的定义及本工程 `canonicalPerfectoidData_laws` 只需 p-adic 完备代数输入，并不证明 perfectoidness、theta 满射或选定 holomorphoid 的 untilt 身份。因此只勾选实际 completion 代数输入子项，来源 bridge 父项仍开放；后续须对选定 holomorphoid 的局部对象建立真正来源连接。此处尊重 Joshi 的对象定义，不以 Mochizuki 的弱接口覆盖该身份义务。现有 `IutInitialThetaCanonicalActualHullData.AnalyticInput` 未改签名，本轮也不宣称它的自由 placeData／bridge 字段已经消除。H¹ₑ/BK、period／theta 联合来源、paper thetaVolume 以及最终 3.12、G1–G4 仍开放。

数学仅在 Scene1/Derived，Core 假设增量 0，Prologue-R5 不变，无动态边界变更或新数学负面证据，不写入 log5。


编辑期失败记录：通用叶首检 69.389 秒、进程组峰值 RSS 5,489,684 KiB，缺少整数子环 CharZero 实例、metric ball 成员展开和 coefficient ring hom 强制转换；改为从 completion／子环得到特征零、显式展开球，并用真实 embedding 的 `comp`／`codRestrict` 构造整数映射。第二次检查 77.581 秒、5,492,416 KiB，子环特征零转移方向及子环幂强制转换仍需修正；改用 subtype ring hom 的 `charZero` 与显式 `Subring.coe_pow`／`Subring.coe_natCast` 后通用叶通过。两次均为类型/API 问题，无 heartbeat 或内存失败，未改变数学目标或前提。


验收（2026-10-19）：最终通用叶 `LocalCompletionAdicFontaine` 退出 0，74.016 秒、进程组峰值 RSS 5,490,092 KiB；实际消费者 `IutInitialThetaCompletionFontaine` 首检通过，111.918 秒、9,075,076 KiB。两叶最终日志均为空，无错误或 warning。`Checks.SceneBounds`、`Axioms.SceneBounds`、`Act1Scene1` 依次首次通过，耗时 123.575、118.074、116.047 秒，峰值 RSS 依次 9,379,024、9,363,588、9,259,996 KiB。19/19 个新增公开声明逐名通过公理核对；全部 2410 个打印声明仅含 `propext`、`Classical.choice`、`Quot.sound`，无 `sorryAx`，类型／公理审计无 warning，聚合日志为空。静态导入审计覆盖聚合和两个审计入口的 496 个可达本工程模块，扫描覆盖全部 import 行形式；无 Obligations、Candidate、Scene2、Act2 或 `Iut.*` 导入。新增源码未含 sorry/admit/自定义 axiom/opaque。

本轮共 7 次直接 Lean 任务（5 成功、2 失败），成功累计 543.630 秒、失败累计 146.970 秒、总计 690.600 秒；进程组峰值 RSS 9,379,024 KiB（8.945 GiB）。全部使用 CPU affinity `0–13`、`LEAN_NUM_THREADS=10`、Lean `-j1`，实际并发 worker 峰值 1；每 0.5 秒采样进程组 RSS，85 GiB 停止线未触发（用户上限 90 GiB）。无 heartbeat override。只用 `lake env lean -j1 -o` 访问现有依赖产物，未调用 Lake build 调度器、冷构建、重编 Mathlib 或变更冻结工具链/依赖。


### Geometric coefficient field 的实际整数环、Frobenius 与 Fontaine θ 满射

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-ALGEBRAICALLY-CLOSED-FONTAINE` | `LocalGeometricFontaine.{integerRing,mem_integerRing,integerRing_eq_closedBall,principalIdeal_eq_closedBall,principalIdeal_isOpen,integerRing_completeSpace,prime_nonunit,primeNonunitFact,integerRing_isAdic,integerRing_isAdicComplete,integral_pow_surjective,exists_norm_between,frobenius_modP_surjective,theta_surjective}`；`Act1Scene1/AlgebraicallyClosedFontaine.lean` | Joshi `Arithmetic Holomorphic Structures.tex` 的 `lem:perfectoid`（574–581）明确以代数闭完备 rank-one valued field 的非离散性、`|p|<1` 和整数环模 p Frobenius 满射为论证；Mathlib `NormedField.valuation`、`IsAlgClosed.exists_pow_nat_eq`、`IsAdic.isAdicComplete_iff`、`surjective_fontaineTheta` 提供基础 API。对实际 `Ω`、`[NormedField Ω] [IsUltrametricDist Ω]` 定义 `integerRing Ω := (NormedField.valuation (K := Ω)).integer`，证明它的集合恰为原范数闭单位球，每个主理想恰为对应标量半径闭球的 subtype 原像，非零主理想开。Ω 完备时，该闭整数环原拓扑完备。对素数 p 和显式 `0 < ‖(p : Ω)‖ ∧ ‖(p : Ω)‖ < 1`，证明 p 非单位及理想幂的原拓扑共尾性，得到 p-adic 完备实例。`[IsAlgClosed Ω]` 下，对任意 n>0 及 a∈OΩ，域中 n 次根 z 的 `‖z‖^n=‖a‖≤1` 强制 z∈OΩ，故 OΩ 上取 n 次幂满射；取 p 次根并下传商环，证明 `Function.Surjective (frobenius (ModP (integerRing Ω) p) p)`，再消费 Mathlib 定理得到 `Function.Surjective (Perfectoid.thetaMap (O := integerRing Ω) (p := p))`。独立平方根论证证明 `∀ x, 0<‖x‖ → ‖x‖<1 → ∃y, ‖x‖<‖y‖ ∧ ‖y‖<1`，即实际范数值在 1 下方无最大元。 | Scene1/Derived；proved |
| `JT-SCENE1-INITIAL-THETA-GEOMETRIC-FONTAINE` | `InitialThetaGeometricFontaine.{embedding_norm_eq,prime_norm_bounds,primeNormFact,coefficientMap,coefficientMap_coe,coefficientMap_injective,placeData,placeData_place,placeData_laws,placeData_theta_surjective,exists_norm_between_prime,placeData_frobenius_surjective,bridgeData,bridgeData_laws,bridgeData_coefficientMap}`；`Act1Scene1/IutInitialThetaGeometricFontaine.lean` | Joshi I `def:arith-hol-strs`（766 起）、`de:geom-base-points`（778 起）、`def:untilt-galois`（1470 起）使用实际局部域的等距扩张 Ω 作为几何系数域。对同一 `D : InitialThetaData AG TG`、`w : (iutInitialThetaTateParameterData D).places` 和显式 `ι : LocalCompletion.completionAt D.F w.1 →+* Ω`、`hι : Isometry ι`，由等距性和真实 completion 的素数范数界推导 `0<‖residueChar w‖<1`。系数映射 `𝓞 D.F →+* LocalGeometricFontaine.integerRing Ω` 是实际 completion embedding 后接 ι 的整数限制，值和单射性均有 proof term。实际几何整数环据此满足现有 canonical place/bridge 输入，处等于 w，支持证明直接消费 w.2；其 θ 和模 p Frobenius 满射性来自通用叶，同时给实际 p 范数上方的非离散 witness。bridge 对同一 `AdelicThetaLinkData.ofInitialThetaData` 保留显式 theta／thetaBase／packetHull／height／ramification／volume／length 参数。 | Scene1/Derived；proved |

全部声明带前缀 `JoshiTeich.Act1Scene1`；29 个公开名称包括 `integerRing` abbrev 及三个通用实例，逐名登记于 Checks／Axioms 家族。两叶均为本工程原创证明，无参考工程源码复制或许可证增量，不导入 refer/iut。新增 Mathlib import 的现有 olean 均在构建前确认存在。

本单元按 Joshi `lem:perfectoid` 的特征零论证闭合局部整数环、取根、范数非离散 witness 和 Frobenius／θ 满射的具体证明内容；未新增一个仅改名的 Perfectoid 公理接口。通用叶使用真实 norm valuation ring 和原拓扑，消费者使用实际 completion 的等距嵌入，不把上一轮的离散赋值 completion 自身当作该几何系数域。Ω、代数闭／完备／ultrametric 结构以及到 Ω 的等距嵌入是显式几何输入，尚未从共同全局 Initial Θ-data 构造它们；也未给指定 tilt 身份、Berkovich 基点、tempered marking 或跨 holomorphoid transport。因此仅追加来源 bridge 的窄子项，父项、H¹ₑ/BK／period 身份、paper thetaVolume、3.12 及 G1–G4 仍开放。`CanonicalActualHull.AnalyticInput` 未改签名。

数学仅在 Scene1/Derived；Core 假设增量 0，Prologue-R5 不变，无动态边界移动或数学负面证据，不写入 log5。


编辑期检查记录：通用叶首检 64.254 秒、峰值 RSS 5,488,844 KiB，集合 membership 的隐式转换需先 change、`ModP` 为根命名空间 API，并清除无用 section 实例的 warning；第二次 64.817 秒、5,495,340 KiB，`omit` 必须置于 doc comment 之前，取根 surjectivity witness 的 lambda 需先显式 change 成幂等式再改写商环。修正后通用叶 63.340 秒、5,489,244 KiB 通过且日志为空。消费者首检 111.995 秒、9,092,268 KiB，等距性 section proof 未出现于定理目标，需显式 include 才能在证明和下游参数中使用；由此引起的连锁类型错误已按真实参数依赖修正。上述为 Lean 类型/API 问题，不改变数学目标或假设，无 heartbeat 或内存失败。


消费者第二次检查 108.392 秒、9,094,900 KiB：Lean 拒绝从输出范数命题中无法推断的 ι／等距证明参数注册局部 instance。将等距性作为相同内容的显式 `Fact (Isometry ι)` 输入，使规范范数实例可由它推断；没有加入范数界、完备性或 θ 满射的自由证书，数学输入仍仅为实际域嵌入及其等距性。此次无 heartbeat 或内存失败。


消费者第三次检查 114.499 秒、9,095,564 KiB：Fact 等距性仍不足以为带未定嵌入参数的规范范数实例决定 synthesis order。最终移除该参数化局部 instance，将同一个范数界证明包装为普通生产者 `primeNormFact`，在各公开构造内部以显式局部 `letI` 消费；公开输入恢复 `ι` 与普通证明 `hι : Isometry ι`，没有自由的 norm/completeness/theta 证书。此前尝试的 Fact 输入写法未进入最终接口。此次无 heartbeat 或内存失败。


消费者第四次检查 111.991 秒、9,091,580 KiB：数据投影的公开类型也须局部绑定已证明的素数范数实例；补齐这些类型中的绑定，并将命题类的生产者写为 theorem，证明内 letI 改为 let 以清除冻结版 linter 警告。此次无 heartbeat 或内存失败。


消费者第五次检查退出 0，109.869 秒、9,093,828 KiB，但编译所读源码仍含 `primeNormFact` 上无用 `IsUltrametricDist` section 实例的 warning，不作为最终验收。已将该生产者移到 ultrametric 变量声明之前，继续重检最终源码。一次收尾 Checks 任务被提前启动后主动中断：退出 -15，17.228 秒、峰值 RSS 951,096 KiB、实际 Lean worker 峰值 0；该中断不计作成功检查，公理／聚合任务未启动。后续最终验收使用清理后的产物。上述均无 heartbeat／内存停止。


验收（2026-10-19）：最终通用叶 `AlgebraicallyClosedFontaine` 退出 0，63.340 秒、进程组峰值 RSS 5,489,244 KiB；最终实际消费者 `IutInitialThetaGeometricFontaine` 退出 0，113.996 秒、9,091,328 KiB。两叶最终日志均为空，无错误或 warning。最终 `Checks.SceneBounds`、`Axioms.SceneBounds`、`Act1Scene1` 依次退出 0，耗时 125.174、120.595、119.143 秒，峰值 RSS 依次 9,381,164、9,366,188、9,241,448 KiB。29/29 个新增公开声明逐名通过公理核对；全部 2439 个打印声明仅含 `propext`、`Classical.choice`、`Quot.sound`，无 `sorryAx`；最终类型／公理审计无 warning，聚合日志为空。静态导入审计覆盖聚合及两个审计入口的 498 个可达本工程模块，扫描覆盖全部 import 行形式；无 Obligations、Candidate、Scene2、Act2 或 `Iut.*` 导入。新增源码未含 sorry/admit/自定义 axiom/opaque。打印类型确认实际消费者的 θ 满射定理只接收同一 D／w、Ω 的 normed field／ultrametric／complete／algebraically closed 结构及实际 completion 的等距 ring hom；范数界／p-adic 完备性／Frobenius／θ 满射性均由证明提供。

本轮共 13 次直接 Lean 任务：6 次退出 0（其中 1 次带 warning 的编辑期成功不作最终验收）、6 次编辑期失败、1 次主动中断；退出 0 累计 652.117 秒、失败累计 575.948 秒、中断 17.228 秒，总计 1245.293 秒。进程组峰值 RSS 9,381,164 KiB（8.947 GiB）。全部使用 CPU affinity `0–13`、`LEAN_NUM_THREADS=10`、Lean `-j1`，实际并发 worker 峰值 1（中断任务在 Lean 启动前停止，worker 峰值 0）；每 0.5 秒采样进程组 RSS，85 GiB 停止线未触发（用户上限 90 GiB）。无 heartbeat override。只用 `lake env lean -j1 -o` 访问现有依赖产物，未调用 Lake build 调度器、冷构建、重编 Mathlib 或变更冻结工具链/依赖。


### 从实际 completion 构造规范几何系数域及 Fontaine bridge

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-COMPLETED-ALGEBRAIC-CLOSURE` | `CompletedAlgebraicClosure.{Algebraic,algebraicField,algebraicAlgebra,algebraicIsAlgebraic,algebraicIsAlgClosed,algebraicNontriviallyNormedField,algebraicNormedAlgebra,algebraicUltrametric,Field,completedNontriviallyNormedField,completedUltrametric,embedding,embedding_norm,embedding_isometry,embedding_injective,algebraic_denseRange,algebraicCharZero,completedCharZero,completedIsAlgClosed,Extension,ofNormedField}` 及 `Extension.{mk,Carrier,normedField,nontrivialNorm,completeSpace,ultrametric,charZero,isAlgClosed,embedding,embedding_isometry}`；`Act1Scene1/CompletedAlgebraicClosure.lean` | Joshi I `de:geom-base-points`（778 起）使用代数闭完备域及局部域的等距嵌入；`Arithmetic Holomorphic Structures.tex` 的 `lem:perfectoid` 与例子（574–589）明确使用代数闭包的完备化。Mathlib `spectralNorm.nontriviallyNormedField`／`spectralNorm.normedAlgebra`、`isNonarchimedean_spectralNorm`、`UniformSpace.Completion`、`IsAlgClosed.of_denseRange` 给出实际构造及核心定理。对 E 的非平凡范数、完备性和 ultrametric 结构，`Algebraic E` 是 `AlgebraicClosure E` 的独立载体，仅在该载体上装配谱范数，避免改变 Mathlib 原 carrier 的全局实例。得到 normed algebra、代数闭性和 ultrametric 结构。`Field E := Completion (Algebraic E)` 使用原拓扑的真实完备化，其范数非平凡性由原非平凡元素的 coe 保范数产生，ultrametric 三角律由稠密 coe 的二元归纳及闭关系下传。规范 `embedding : E →+* Field E` 为实际 algebraMap，`embedding_norm`／`embedding_isometry`／`embedding_injective` 分别证明保范数、等距、单射。`algebraic_denseRange` 是真实代数闭子域到完备化的稠密性；E 特征零时，实际嵌入给完备化特征零，再由 `IsAlgClosed.of_denseRange (K := Algebraic E) (L := Field E)` 得到完备化代数闭性。`Extension B` 将该实际 carrier、范数、非平凡性、完备性、ultrametric、CharZero、IsAlgClosed、嵌入及等距证明一起保存，`ofNormedField` 从已有 NormedField／complete／ultrametric／CharZero 及非平凡范数 witness 构造全部字段。没有外给代数闭完备系数域或它的等距嵌入。 | Scene1/Derived；proved |
| `JT-SCENE1-INITIAL-THETA-CANONICAL-GEOMETRIC-FONTAINE` | `InitialThetaCanonicalGeometricFontaine.{geometricExtension,coefficientField,coefficientField_normedField,coefficientField_nontriviallyNormedField,coefficientField_completeSpace,coefficientField_ultrametric,coefficientField_charZero,coefficientField_isAlgClosed,completionEmbedding,completionEmbedding_isometry,completionEmbedding_norm,primeNormFact,coefficientMap,coefficientMap_coe,coefficientMap_injective,placeData,placeData_place,placeData_laws,theta_surjective,frobenius_surjective,bridgeData,bridgeData_laws,bridgeData_coefficientMap}`；`Act1Scene1/IutInitialThetaCanonicalGeometricFontaine.lean` | 同一 Joshi 来源及已验收 `InitialThetaGeometricFontaine` 消费者。对任意实际 `D : InitialThetaData AG TG` 和 `w : (iutInitialThetaTateParameterData D).places`，先由 `CompletedAlgebraicClosure.ofNormedField` 对实际 completion 构造全部结构与法律的 `geometricExtension D w`，再取 `coefficientField D w := (geometricExtension D w).Carrier`（其生产者的域为 `CompletedAlgebraicClosure.Field (LocalCompletion.completionAt D.F w.1)`），全部 normed field／complete／ultrametric／CharZero／IsAlgClosed 结构由实际 completion 和通用生产者给出；实际 completion 的 CharZero 直接由数域的 completion embedding 证明。`completionEmbedding` 及其等距性、保范数均来自规范生产者。此前外给 Ω／等距性参数不再出现在这一消费者的接口。`primeNormFact` 将真实剩余素数范数界作为普通证明产生，构造内部的 let 实例消费它；实际单射 `coefficientMap : 𝓞 D.F →+* LocalGeometricFontaine.integerRing (coefficientField D w)` 的值精确等于规范 completionEmbedding 后接数域 completion embedding。该真实几何整数环产生 canonical placeData、法律、θ 满射及模 p Frobenius 满射，支持处精确为 w；对同一 `AdelicThetaLinkData.ofInitialThetaData` 产生 bridge、法律及真实系数映射公式。theta／thetaBase／packetHull／height／ramification／logVolume／processionLength 仍为显式下游参数。 | Scene1/Derived；proved |

上述声明均带前缀 `JoshiTeich.Act1Scene1`，54 个公开名称包括 carrier／abbrev、Extension 类型／构造子／字段和全部新全局实例，逐名登记于 Checks／Axioms 家族。两叶为本工程原创 adapter／证明，没有复制 reference 工程代码，没有许可证增量，不导入 refer/iut。新增直接 Mathlib 导入的已有 olean 在构建前确认存在，冻结工具链和依赖不变。

本单元具体消除上一轮局部 Fontaine 构造对自由几何域 Ω、代数闭／完备／ultrametric 结构和等距嵌入证书的依赖，给出实际有限处的一个规范局部几何系数域。它提供 Joshi 几何基点定义中所需的域部分；未构造指定 tilt 身份 `K^flat ≅ F`、Berkovich 基点、tempered marking、不同 holomorphoids 的族及跨来源比较。因此仅勾选局部规范系数域子项，不宣称该域已识别为论文选定 holomorphoid，来源 bridge 父项仍开放。`CanonicalActualHull.AnalyticInput` 与 Prologue 接口均未改签名；H¹ₑ/BK、theta／period 联合来源、paper thetaVolume、3.12 及 G1–G4 仍开放。数学仅在 Scene1/Derived；Core 假设增量 0，Prologue-R5 不变，无动态边界变更或数学负面证据，不写入 log5。 构造沿用既有 finite-place norm，谱范数扩张及完备化保持该范数；未在本单元重定标 q-norm 或另称标准 ℚp 等距归一化已经完成。


编辑期首检：通用叶退出 1，68.950 秒、进程组峰值 RSS 4,634,284 KiB；完备化的 NontriviallyNormedField 父实例改用显式 `toNormedField` 字段，`norm_algebraMap'` 补目标域参数，稠密子域代数闭性定理补显式 K／L。失败为 Lean 实例／API 参数问题，未改变数学目标或前提，无 heartbeat 或内存停止。


实际消费者首检退出 1，114.066 秒、峰值 RSS 9,089,172 KiB；需要显式启用 Mathlib `Valued` scoped instance `Valued.toNontriviallyNormedField`，以使用已有实际 finite-place rank-one valuation 的非平凡范数结构。已在该叶启用作用域；这是已有赋范结构的实例装配，不另给非平凡性证书或改变 completion 的范数。下游错误由最初的 carrier elaboration 失败引起。无 heartbeat 或内存停止。


性能诊断：启用 Valued 作用域后的消费者检查持续运算且日志为空，主动中断以定位实例装配成本；退出 -15，542.571 秒、进程组峰值 RSS 9,511,260 KiB。随后不改数学陈述，仅启用 trace.profiler 的诊断检查也未返回可定位输出；主动 SIGINT 收集诊断，退出 130，145.886 秒、9,506,752 KiB。二者均为主动中断，不计为成功或 heartbeat 失败，内存停止线未触发。继续用仅包含规范域／基础实例的临时前缀模块定位；不改变证明目标或增加数学输入。


前缀 profiler：退出 1，164.586 秒、进程组峰值 RSS 9,519,540 KiB。临时即时标记与 doc comment 之间的一处顺序错误另行修正；两个实际域实例也分别明确触发 `(kernel) deterministic timeout`。profile 显示 `coefficientField_charZero` elaboration 0.127427 秒、kernel 29.537284 秒；`coefficientField_isAlgClosed` elaboration 0.119166 秒、kernel 29.058153 秒，故成本在具体实例的 kernel 转换检查，而非域的数学存在性。按用户 heartbeat 流程，第一次确定的 timeout 后将 `maxHeartbeats` 提到 1,000,000，并对第一个实例复查。


首轮提高到 1,000,000 后的特征零实例复查仍退出 1：262.270 秒、峰值 RSS 11,136,444 KiB，kernel 检查 148.897624 秒后 deterministic timeout。遵循用户规则，第二次 timeout 后实施一次实例连接优化并将 maxHeartbeats 翻倍到 2,000,000：移除宽泛 Valued scope 激活，局部 NontriviallyNormedField 的父实例显式复用实际 finite-place 原 NormedField，非平凡性由实际剩余素数的逆元范数大于 1 证明；实际系数域的 CharZero 直接由实际代数嵌入单射证明，IsAlgClosed 直接消费真实稠密代数闭子域定理，避免在具体 carrier 之间搬运通用结论时的赋范字典转换。范数、公开数学前提及目标不变，先用临时域前缀 profiler 复查。


第二个优化实现：旧的未封装前缀检查尚在运行时，已将规范域及其已证明结构一起封装；旧前缀对应的实现已被替换，主动停止该诊断，退出 -15，526.591 秒、13,189,444 KiB，不记作新的已确认 timeout。新版本保持 maxHeartbeats 2,000,000：通用 `ofNormedField` 在抽象源域上构造完整 `Extension`，实际生产者 `geometricExtension` 只对同一 completion 实例化该构造；系数域和全部类实例、嵌入从该已构造值投影得到，kernel 可复用相同结构投影，避免在具体完备化 carrier 上反复比较赋范实例。所有字段都有生产者 proof term，不是把几何存在性或法律改成外给结构假设；原范数、数学目标及实际 D／w 输入不变。


封装优化结果：最终通用叶（含 `Extension`／`ofNormedField`）退出 0，57.683 秒、4,663,792 KiB，日志为空；最终实际消费者退出 0，105.887 秒、9,092,128 KiB，日志为空。相比未封装具体实例在 kernel 29.5 秒／148.9 秒后分别超限，新版本完整消费者已通过。源域、谱范数、实际完备化数学构造、目标及 D／w 输入不变；最终消费者保留 `maxHeartbeats 2000000`，不需要继续翻倍。临时前缀 profiler 源码已移除，构建缓存保留。


验收（2026-10-19）：最终通用叶 `CompletedAlgebraicClosure` 退出 0，57.683 秒、进程组峰值 RSS 4,663,792 KiB；最终实际消费者 `IutInitialThetaCanonicalGeometricFontaine` 退出 0，105.887 秒、9,092,128 KiB。两叶最终日志均为空，无错误或 warning。`Checks.SceneBounds`、`Axioms.SceneBounds`、`Act1Scene1` 依次首次通过，耗时 124.206、122.676、110.921 秒，峰值 RSS 依次 9,386,836、9,370,684、9,270,448 KiB。54/54 个新增登记声明逐名通过公理核对；全部 2493 个打印声明仅含 `propext`、`Classical.choice`、`Quot.sound`，无 `sorryAx`；类型／公理日志无 warning，聚合日志为空。静态导入审计覆盖聚合及两个审计入口的 500 个可达本工程模块，扫描覆盖全部 import 行形式；无 Obligations、Candidate、Scene2、Act2 或 `Iut.*` 导入。新增源码未含 sorry/admit/自定义 axiom/opaque。打印签名确认 `coefficientField_isAlgClosed` 和 `theta_surjective` 除原始 D／w 及原有隐式 AG／TG 外，没有 Ω、等距嵌入、赋范／完备／代数闭或 theta 证书输入。

本轮共 13 次直接 Lean 任务（6 次成功、4 次失败、3 次主动中断，含临时前缀性能诊断）；成功累计 580.168 秒、失败累计 609.872 秒、中断累计 1215.048 秒，总计 2405.088 秒；进程组峰值 RSS 13,189,444 KiB（12.578 GiB）。全部使用 CPU affinity `0–13`、`LEAN_NUM_THREADS=10`、Lean `-j1`，实际并发 worker 峰值 1；每 0.5 秒采样进程组 RSS，85 GiB 停止线未触发（用户上限 90 GiB）。确定的 kernel timeout 按约定先提高到 1,000,000，仍失败后实施优化并提高到 2,000,000，最终生产者通过；此数值只作用于新消费者，不改变数学前提或 Prologue 合约。只用 `lake env lean -j1 -o` 访问现有依赖产物，未调用 Lake build 调度器、冷构建、重编 Mathlib 或变更冻结工具链/依赖。


### 实际几何整数环的代数 tilt 域、特征 p／Frobenius 与估值延拓

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-GEOMETRIC-TILT-FIELD` | `GeometricTiltField.{Source,source_isDomain,sourceValuation,sourceValuation_eq_zero_iff,FractionField,fractionField_charP,fractionField_perfect,denominators_le_primeCompl,fractionValuation,fractionValuation_inclusion,fractionValuation_div,fractionField_eq_mathlibTilt,Data,ofField}` 及 `Data.{mk,Carrier,field,charP,perfect,sourceValuation,valuation,inclusion,inclusion_injective,valuation_inclusion}`；`Act1Scene1/GeometricTiltField.lean` | Joshi `Arithmetic Holomorphic Structures.tex` 的 tilt 讨论（587–599）及 I `def:arith-hol-strs` 要求特征 p 的 tilt；Mathlib `RingTheory/Perfection.lean` 的 `PreTilt.val`、`PreTilt.isDomain`、`Tilt`（约 786–838）给出现有代数 carrier 和整数环估值，文件 TODO 明确尚未在 Tilt 上定义估值和 characteristic predicate。对实际 `[NormedField Ω] [IsUltrametricDist Ω]`、素数 p 及 `0<‖(p:Ω)‖<1`，取 `Source Ω p := PreTilt (LocalGeometricFontaine.integerRing Ω) p`。实际 norm valuation 的 integer ring 由 `Valuation.integer.integers` 给出，Mathlib 的 val 与零核定理证明该 PreTilt 为整域及 sourceValuation 的零核。`FractionField Ω p := FractionRing (Source Ω p)`，由真正的 fraction-field 注入导出 CharP p；任意分式的分子／分母分别取原 perfect PreTilt 中的 p 次根，证明分式域 Frobenius 满射，再由 field reducedness 得 PerfectRing。估值的零核保证非零分母都在 supp 的补集中，`Valuation.extendToLocalization` 由此构造实际 fractionValuation，并证明它在原 PreTilt 嵌入上精确等于 sourceValuation，对分式给出 v(a)/v(b)。`fractionField_eq_mathlibTilt` 定义性识别本 carrier 与 Mathlib Tilt，而非识别任意指定的论文 F。`Data R p` 保存构造出的域、特征 p、perfectness、原／新估值、原环嵌入、单射和估值身份；`ofField` 逐字段生产这些值和证明，调用者不提供该 Data。 | Scene1/Derived；proved |
| `JT-SCENE1-INITIAL-THETA-TILT-FIELD` | `InitialThetaTiltField.{Source,data,Carrier,carrierField,carrierCharP,carrierPerfect,inclusion,inclusion_injective,sourceValuation,valuation,sourceValuation_eq,valuation_inclusion,valuation_div,valuation_eq_zero_iff,frobenius_bijective,inclusion_frobenius,valuation_frobenius,valuation_inverseFrobenius_pow}`；`Act1Scene1/IutInitialThetaTiltField.lean` | 对同一 `D : InitialThetaData AG TG` 和 `w : (iutInitialThetaTateParameterData D).places`，只消费此前已构造的 `InitialThetaCanonicalGeometricFontaine.coefficientField D w` 和由同一来源证明的 primeNormFact。`data` 取通用生产者对该真实系数域／整数环的值，`Carrier`、Field／CharP／PerfectRing 实例、source 与 fraction 估值以及 PreTilt inclusion 全由同一构造投影取得，避免具体 carrier 的重复实例转换。`sourceValuation_eq` 将投影的原估值精确接回通用实际 PreTilt.val；`valuation_inclusion` 和 `valuation_div` 消费同一嵌入，`valuation_eq_zero_iff` 在实际 field 上由逆元关系证明估值零核。`frobenius_bijective` 来自已证明 perfectness，`inclusion_frobenius` 是原 PreTilt 与分式域上的 Frobenius 交换式；`valuation_frobenius` 及 `valuation_inverseFrobenius_pow` 给 p 次幂和逆 Frobenius 的实际估值幂身份。没有自由的 tilt field、特征 p／perfectness、注入或估值法律输入。 | Scene1/Derived；proved |

以上声明均带前缀 `JoshiTeich.Act1Scene1`；42 个新增登记名称包括全部显式声明、Data 构造子／字段和新实例，加入 Checks／Axioms 家族及 Scene1 聚合。两叶为原创证明／adapter，无 reference 工程代码复制或许可证增量；新增 Mathlib 导入的现有 olean 已在检查前确认存在。

来源范围：本单元构造的是同一实际几何域的 PreTilt 分式域，配上 Mathlib PreTilt.val 的真实延拓，闭合代数 carrier 的特征 p／perfectness 和估值连接；不是一个任意假定的 field 或任意选择的 valuation。它尚未证明该 tilt 的拓扑／完备性／代数闭性、sharp 与范数的比较、指定 `K^flat ≅ F`、Berkovich 基点或 tempered marking，不能据此关闭论文 holomorphoid 身份。规范实际 untilt／Fontaine 输入已存在，但本轮没有把现有 UntiltingLaws 当作这些进一步几何身份的替代。H¹ₑ/BK、theta／period／paper volume 及最终 3.12、G1–G4 仍开放。数学仅在 Scene1/Derived；Core 假设增量 0，Prologue-R5 不变，无动态边界变更或数学负面证据，不写入 log5。


编辑期首检：通用叶退出 1，67.467 秒、进程组峰值 RSS 5,490,908 KiB；缺少 NNReal scoped notation 导致 ℝ≥0 类型被误解析，`PerfectRing.bijective_frobenius` 的参数名应为 R，并将 prime valuation 非一性改为显式 NNReal→Real 的 congrArg 证明。修正后复查；类型／记号及 API 参数问题，未改变数学目标或前提，无 heartbeat／内存失败。


验收（2026-10-19）：最终通用叶 `GeometricTiltField` 退出 0，72.067 秒、进程组峰值 RSS 5,498,800 KiB；实际消费者 `IutInitialThetaTiltField` 首检通过，110.455 秒、9,088,764 KiB。两叶最终日志均为空，无错误或 warning。`Checks.SceneBounds`、`Axioms.SceneBounds`、`Act1Scene1` 依次首次通过，耗时 116.927、117.015、119.075 秒，峰值 RSS 依次 9,390,688、9,374,136、9,253,884 KiB。42/42 个新增登记声明逐名通过公理核对；全部 2535 个打印声明仅含 `propext`、`Classical.choice`、`Quot.sound`，无 `sorryAx`，类型／公理日志无 warning，聚合日志为空。静态导入审计覆盖聚合及两个审计入口的 502 个可达本工程模块，扫描覆盖全部 import 行形式；无 Obligations、Candidate、Scene2、Act2 或 `Iut.*` 导入。新增源码未含 sorry/admit/自定义 axiom/opaque。打印签名确认实际 perfectness、估值嵌入身份及逆 Frobenius 估值关系除 D／支持处 w／所作用元素和原隐式 AG／TG 外，不接收 tilt 或估值法律证书。

本轮共 6 次直接 Lean 任务（5 成功、1 失败），成功累计 535.539 秒、失败累计 67.467 秒、总计 603.006 秒；进程组峰值 RSS 9,390,688 KiB（8.956 GiB）。全部使用 CPU affinity `0–13`、`LEAN_NUM_THREADS=10`、Lean `-j1`，实际并发 worker 峰值 1；每 0.5 秒采样进程组 RSS，85 GiB 停止线未触发（用户上限 90 GiB）。无 heartbeat override。只用 `lake env lean -j1 -o` 访问现有依赖产物，未调用 Lake build 调度器、冷构建、重编 Mathlib 或变更冻结工具链/依赖。


### 同一实际 tilt 的 sharp、范数身份、满射性及 Fontaine θ 连接

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-GEOMETRIC-TILT-SHARP` | `GeometricTiltSharp.{integralSharp,integralSharp_eq_untilt,sourceValuation_eq_sharp_norm,integralSharp_eq_zero_iff,integralSharp_denominator_units,sharp,sharp_inclusion,sharp_div,sharp_norm,integralRoot,integralRoot_pow,rootTower,rootTower_pow,rootLift,untilt_rootLift,integralSharp_rootLift,sharp_surjective,Data,ofField}` 及 `Data.{mk,map,norm_map,surjective,on_integral}`；`Act1Scene1/GeometricTiltSharp.lean` | Joshi `Arithmetic Holomorphic Structures.tex` 的 tilt／untilt（587–599）及 value-group 比较讨论（734、783），I `def:arith-hol-strs`；Mathlib `PreTilt.coeff_iterate_frobeniusEquiv_symm`、`PreTilt.mk_untilt_eq_coeff_zero`、`PreTilt.untilt_iterate_frobeniusEquiv_symm_pow`、`ModP.preVal_mk`、`PreTilt.valAux_eq` 和 `Perfection.teichmuller_spec` 提供确切基础 API。源为实际 `Ω`、其 norm valuation integer ring、满足 `0<‖(p:Ω)‖<1` 的真实素数范数及原拓扑完备性。`integralSharp : Source Ω p →*₀ Ω` 为 canonical Teichmüller₀ followed by integer inclusion，其函数值精确等于现有 canonical untilt。若 x≠0，选 n 使 coeff_n(x)≠0；y=Frob^(-n)(x) 的 untilt 模 p 还原为 coeff_n(x)，因此 `preVal(coeff_n(x))=‖y^sharp‖₊`；Frobenius 的幂关系和 `valAux_eq` 给 `sourceValuation(x)=‖x^sharp‖₊`。零情形由实际零保持性处理。零核身份保证每个非零分母的 sharp 像为 Ω 单位，以 `Submonoid.LocalizationMap.lift₀` 构造同一 `FractionField Ω p →*₀ Ω`，证明 inclusion／division 公式及全域 `‖sharp x‖₊=fractionValuation x`，没有给入这条范数比较。Ω 代数闭时，原 integer ring 中选择真实 p 次根，递归构造 r_(n+1)^p=r_n、r_n^(p^n)=a 的 tower，降 mod p 得原 PreTilt 的 rootLift；`teichmuller_spec` 证明其 untilt=a。任意 x∈Ω 先选 b=p^n 使 a=b*x 整，再取 rootLift(a)/rootLift(b) 给 sharp 原像，证明全域 sharp 满射。`Data` 只保存构造的同一 carrier 上的 map、norm、满射性和 integral compatibility；`ofField` 生产全部字段，不接收 sharp 或范数／满射 certificate。 | Scene1/Derived；proved |
| `JT-SCENE1-INITIAL-THETA-TILT-SHARP` | `InitialThetaTiltSharp.{data,sharp,sharp_norm,sharp_norm_real,sharp_surjective,sharp_eq_zero_iff,sharp_inclusion,untilt_norm,theta_teichmuller_eq_sharp,theta_teichmuller_norm,sharp_frobenius,sharp_inverseFrobenius_pow,valuation_range,exists_contracting}`；`Act1Scene1/IutInitialThetaTiltSharp.lean` | 对同一 `D : InitialThetaData AG TG` 及 `w : (iutInitialThetaTateParameterData D).places`，使用已经构造的 `InitialThetaTiltField.Carrier D w` 与 canonical geometric coefficient field Ω，未另造独立 tilt carrier。原 Ω 的 complete／algebraically closed 结构和实际 p 范数界全由此前 source 生产者给出。`data` 消费上述通用构造，其 map 为实际 sharp；`sharp_norm`／`sharp_norm_real` 将该 map 的原域范数精确识别为上一单元的实际 tilt valuation，且 sharp 满射并有零核。`sharp_inclusion` 将 map 接回同一 placeData 的 canonical untilt；原 PreTilt untilt 范数等于其实际 sourceValuation。`theta_teichmuller_eq_sharp` 将同一 placeData 的 θ([x]) 接到 sharp(inclusion x)，并证明对应范数身份。sharp 与 Frobenius／逆 Frobenius 的 p 次幂关系直接由乘法 map 及实际 field Frobenius equivalence 证明。满射性及范数身份给 `Set.range valuation = Set.range nnnorm`；取实际剩余素数 p 的 sharp 原像，证明存在 0<v(x)<1 的真实 tilt 元素，未外给 valuation nontriviality。 | Scene1/Derived；proved |

所有声明带前缀 `JoshiTeich.Act1Scene1`，38 个新增登记名称包括所有显式声明和 Data 的构造子／字段，登记于 Checks／Axioms 家族及 Scene1 聚合。新增 direct Mathlib import 的已有 olean 在构建前确认存在。两叶均为本工程原创证明／adapter，无 reference 工程源码复制或许可证增量，不导入 refer/iut。

本单元实际闭合上一单元尚未证明的 sharp／范数比较，并将其与同一 untilt／θ source 接通；sharp 的类型为保零乘法映射，未将它改成跨特征的 ring hom。满射证明使用真实 compatible integral roots 和 Teichmüller 极限的唯一性；实际 value ranges 相等是同一 Ω／tilt 上的证明，没有把不同 holomorphoids 的比较或指定 F 的等距身份当作结论。tilt 的拓扑、完备性、代数闭性、指定 F／Berkovich 基点／tempered marking、H¹ₑ/BK、theta／period／paper volume 与最终 3.12、G1–G4 仍开放；checkbox 父项未关闭。数学只在 Scene1/Derived，Core 假设增量 0，Prologue-R5 不变，无动态边界变更或数学负面证据，不写入 log5。


编辑期首检：通用叶退出 1，76.097 秒、进程组峰值 RSS 5,500,368 KiB；`teichmuller₀` 需 Perfection 命名空间，直到完成 O-valued untilt 的类型推断后才能显式 coercion 到 Ω，Perfection ext 的末端须显式用 map_zero 连接系数；同时将已弃用 push_neg 替换为 push Not。修正这些记号／类型 API 后，扩展加入实际 compatible-root tower／sharp 满射性证明，并复查。未改变范数身份的数学前提或目标，无 heartbeat／内存失败。


验收（2026-10-19）：最终通用叶 `GeometricTiltSharp` 退出 0，69.919 秒、进程组峰值 RSS 5,512,992 KiB；实际消费者 `IutInitialThetaTiltSharp` 首检通过，107.307 秒、9,089,512 KiB。两叶最终日志均为空，无错误或 warning。`Checks.SceneBounds`、`Axioms.SceneBounds`、`Act1Scene1` 依次首次通过，耗时 129.751、129.889、112.912 秒，峰值 RSS 依次 9,393,196、9,377,976、9,242,596 KiB。38/38 个新增登记声明逐名通过公理核对；全部 2573 个打印声明仅含 `propext`、`Classical.choice`、`Quot.sound`，无 `sorryAx`；类型／公理日志无 warning，聚合日志为空。静态导入审计覆盖聚合及两个审计入口的 504 个可达本工程模块，扫描覆盖全部 import 行形式；无 Obligations、Candidate、Scene2、Act2 或 `Iut.*` 导入。新增源码未含 sorry/admit/自定义 axiom/opaque。打印签名确认 sharp 满射性、θ 的 Teichmüller 范数身份及 contracting tilt witness 只接收实际 D／w（及所作用元素，原隐式 AG／TG），没有新的几何、范数或满射证书参数。

本轮共 6 次直接 Lean 任务（5 成功、1 失败），成功累计 549.778 秒、失败累计 76.097 秒、总计 625.875 秒；进程组峰值 RSS 9,393,196 KiB（8.958 GiB）。全部使用 CPU affinity `0–13`、`LEAN_NUM_THREADS=10`、Lean `-j1`，实际并发 worker 峰值 1；每 0.5 秒采样进程组 RSS，85 GiB 停止线未触发（用户上限 90 GiB）。无 heartbeat override。只用 `lake env lean -j1 -o` 访问现有依赖产物，未调用 Lake build 调度器、冷构建、重编 Mathlib 或变更冻结工具链/依赖。


### 同一实际 tilt 的赋范／valued topology、rank one 与 Frobenius 同胚

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-INITIAL-THETA-TILT-TOPOLOGY` | `InitialThetaTiltTopology.{absoluteValue,carrierNormedField,norm_eq_valuation,nnnorm_eq_valuation,norm_sharp,carrierUltrametric,carrierNontriviallyNormedField,carrierValued,valued_eq_actual,valuationRankOne,frobenius_dist,inverseFrobenius_dist_pow,frobenius_uniformContinuous,inverseFrobenius_uniformContinuous,frobeniusHomeomorph,exists_norm_between,sharp_continuousAt_zero}`；`Act1Scene1/IutInitialThetaTiltTopology.lean` | Joshi `Arithmetic Holomorphic Structures.tex` 的 tilt／untilt（587–599）要求特征 p 的非阿基米德赋值域及最终的等距 tilt 身份，共同 value-group 的比较见 734、783；Mathlib `AbsoluteValue.toNormedField`、`NormedField.toValued`、`NormedField.valuation` 的 rank-one 实例与 metric epsilon–delta 连续性 API 为基础。对同一 `D : InitialThetaData AG TG`、`w : (iutInitialThetaTateParameterData D).places`，始终使用 `InitialThetaTiltField.Carrier D w`，`absoluteValue` 是已证明 actual tilt valuation 的实值 coercion，乘法／零核／三角律均由该真实估值证明，不添加新 norm 假设。`carrierNormedField` 据此赋范；`norm_eq_valuation`／`nnnorm_eq_valuation` 的原范数身份由定义证明，`norm_sharp` 消费同一 sharp 的此前身份。真实 valuation 的 ultrametric 三角律给 `carrierUltrametric`；sharp 满射所产生的真实 contracting tilt 元素的逆元证明范数非平凡，构造 `carrierNontriviallyNormedField`。`carrierValued := NormedField.toValued` 使用同一 norm 的 uniform topology，`valued_eq_actual` 明确证明其 Valued.v 恰等于此前延拓来的 actual valuation；据此给该实际估值 rank-one 实例。char p 中 Frobenius 是 ring hom，因此减法及 norm_pow 给精确 `dist(Frob x,Frob y)=dist(x,y)^p`，逆 Frobenius 的 p 次幂距离等于原距离。正向以 δ=min(ε,1)、反向以 δ=ε^p 证明全域一致连续，构造来自实际 frobeniusEquiv 的 `frobeniusHomeomorph`。任意 norm∈(0,1) 的元素经 inverse Frobenius 得范数更大且仍<1，证明范数值非离散。`sharp_continuousAt_zero` 只用 sharp 保零和 norm_sharp 证明零点连续，未将跨特征乘法 sharp 误称 additive isometry 或 ring hom。 | Scene1/Derived；proved |

声明均带前缀 `JoshiTeich.Act1Scene1`；17 个新增登记名称包含新的 NormedField／ultrametric／nontrivial norm／Valued／RankOne 实例，逐名登记于 Checks／Axioms 家族及 Scene1 聚合。该叶为原创证明／adapter，没有复制 reference 工程源码或许可证增量，没有新 direct Mathlib import，既有依赖产物保留。

本单元闭合 actual tilt carrier 上范数、topology 和 Frobenius 的拓扑法律；所有构造都从同一 D／w 的已有 field、valuation、char p、perfectness 和 sharp 生产者导出，不给入新拓扑／rank-one／连续性法律。NormedField 作用于此前尚无拓扑的 tilt carrier，Valued 保持这同一个 uniform topology，并由估值等式记录来源。未证明该域完备或代数闭，未声明它与论文指定 F 等距、也未构造全局 holomorphoid／Berkovich 基点／tempered marking。H¹ₑ/BK、theta／period／paper volume 与最终 3.12、G1–G4 仍开放，来源 bridge 父项未关闭。数学只在 Scene1/Derived，Core 假设增量 0，Prologue-R5 不变，无动态边界变更或数学负面证据，不写入 log5。


编辑期首检退出 1，118.183 秒、进程组峰值 RSS 9,097,292 KiB：valued_eq_actual 的 ext 目标在实数 coercion 层，需要 congrArg 将 NNReal 等式传到 Real；所用 pow_le_self₀ 并非当前 API，改由 n>0 的 successor 展开、`pow_le_one₀` 及非负乘法推出 a^n≤a。数学目标／前提不变，无 heartbeat 或内存失败。


验收（2026-10-19）：最终叶 `IutInitialThetaTiltTopology` 退出 0，115.596 秒、进程组峰值 RSS 9,096,032 KiB，日志为空，无错误或 warning。`Checks.SceneBounds`、`Axioms.SceneBounds`、`Act1Scene1` 依次首次通过，耗时 130.259、114.439、114.420 秒，峰值 RSS 依次 9,394,948、9,379,668、9,262,408 KiB。17/17 个新增登记声明逐名通过公理核对；全部 2590 个打印声明仅含 `propext`、`Classical.choice`、`Quot.sound`，无 `sorryAx`；类型／公理日志无 warning，聚合日志为空。静态导入审计覆盖聚合及两个审计入口的 505 个可达本工程模块，扫描覆盖全部 import 行形式；无 Obligations、Candidate、Scene2、Act2 或 `Iut.*` 导入。新增源码未含 sorry/admit/自定义 axiom/opaque。打印签名确认 actual tilt 的 NormedField 结构及 Frobenius 同胚只依赖实际 D／支持处 w（和原隐式 AG／TG），不接收额外赋范／拓扑／连续性 certificate。

本轮共 5 次直接 Lean 任务（4 成功、1 失败），成功累计 474.714 秒、失败累计 118.183 秒、总计 592.897 秒；进程组峰值 RSS 9,394,948 KiB（8.960 GiB）。全部使用 CPU affinity `0–13`、`LEAN_NUM_THREADS=10`、Lean `-j1`，实际并发 worker 峰值 1；每 0.5 秒采样进程组 RSS，85 GiB 停止线未触发（用户上限 90 GiB）。无 heartbeat override。只用 `lake env lean -j1 -o` 访问现有依赖产物，未调用 Lake build 调度器、冷构建、重编 Mathlib 或变更冻结工具链/依赖。


### 原 PreTilt 的系数逆极限完备性及其在实际 tilt 中的闭完备像

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-GEOMETRIC-PRETILT-COMPLETENESS` | `GeometricPreTiltCompleteness.{absoluteValue,sourceNormedRing,norm_eq_valuation,coeff_eq_zero_iff,coeff_eq_iff_dist_le,exists_coeffRadius_lt,cauchySeq_coeff_stable,cauchyLimit,coeff_cauchyLimit_eventually,cauchyLimit_tendsto,sourceCompleteSpace}`；`Act1Scene1/GeometricPreTiltCompleteness.lean` | Joshi `Arithmetic Holomorphic Structures.tex` 的 tilt 为完备非阿基米德域的来源目标（587–599）；Mathlib `PreTilt` 为 `Perfection (O/(p)) p` 的真实系数逆极限（Perfection.lean），`PreTilt.coeff_iterate_frobeniusEquiv_symm`、`mk_untilt_eq_coeff_zero`、`untilt_iterate_frobeniusEquiv_symm_pow`，现有 actual untilt／sharp 范数比较及 `Metric.complete_of_cauchySeq_tendsto` 为具体 API。对实际 Ω 的原 norm valuation integer ring、p 素数、0<‖p‖<1 和 Ω 完备性，`absoluteValue` 为已有 actual sourceValuation 的 Real coercion，`sourceNormedRing` 由其建立，不更换 PreTilt carrier。取 y=Frob^(-n)(x)，其 untilt 模 p 等于 coeff_n(x)，系数零等价于 untilt(y)∈(p)，已证实际主理想闭球身份使之等价于 ‖untilt(y)‖≤‖p‖。又 x 的 sharp 范数等于 ‖untilt(y)‖^(p^n)，因此给出精确闭球判据 `coeff_n(x)=0 ↔ ‖x‖≤‖p‖^(p^n)`，对差得到 `coeff_n(x)=coeff_n(y) ↔ dist(x,y)≤‖p‖^(p^n)`。p≥2 给 n≤p^n，而 ‖p‖<1 的幂趋零，证明系数球共尾于所有正 metric 半径。Cauchy criterion 因此使每个系数最终稳定；`cauchyLimit` 取每个系数的实际稳定值，在两个稳定阈值的 max 之后证明 r_(n+1)^p=r_n，故直接构造原 PreTilt 元素。`coeff_cauchyLimit_eventually`／`cauchyLimit_tendsto` 由系数球共尾性证明该原对象是 Cauchy 极限，得到 CompleteSpace。没有假设逆极限已经完备或另造新 completion 取代它。 | Scene1/Derived；proved |
| `JT-SCENE1-INITIAL-THETA-PRETILT-COMPLETENESS` | `InitialThetaPreTiltCompleteness.{sourceNormedRing,sourceCompleteSpace,norm_eq_sourceValuation,coeff_eq_iff_dist_le,inclusion_norm,inclusion_isometry,inclusion_isClosedEmbedding,inclusion_range_isComplete,inclusion_range_isClosed,cauchySeq_converges}`；`Act1Scene1/IutInitialThetaPreTiltCompleteness.lean` | 对同一 `D : InitialThetaData AG TG` 和 `w : (iutInitialThetaTateParameterData D).places`，Ω 仍是已构造 canonical geometric coefficient field；其完备性、p 范数界及实际 `InitialThetaTiltField.Source D w` 均由原 source 生产者提供。通用 norm／complete 实例装配为 actual PreTilt 的实例。actual coeff／distance 判据直接消费通用证明。此前 `InitialThetaTiltTopology` 的 norm valuation 公式与 `InitialThetaTiltField.valuation_inclusion`，结合真实 source norm，证明同一个 ring-hom inclusion 保范数；map_sub 使之等距。Mathlib 的 complete-domain isometry closed embedding 定理给真实包含映射的 IsClosedEmbedding，uniform inducing 的 complete-range 定理给其像的 IsComplete 和闭性。最后在原 actual PreTilt 上提供 Cauchy sequence convergence。完备性并非外给模型或额外 certificate。 | Scene1/Derived；proved |

所有声明带前缀 `JoshiTeich.Act1Scene1`；21 个新增登记名称包括新 norm／complete 实例，加入 Checks／Axioms 家族及 Scene1 聚合。两叶为原创证明／adapter，无参考源码复制或许可证增量，不导入 refer/iut。新 direct Mathlib import 使用现有预编译产物，缓存／冻结依赖保持。

本单元完成实际 PreTilt 的完备性以及该载体在同一 normed tilt 中的闭完备像；这是继续证明 tilt fraction field 完备性的实际基础，未把该闭子环与整个 tilt 的 closed unit ball 身份直接假定为真，也未仅凭它的完备性推断分式域完备。下一步仍须证明足够的邻域／整除连接并在同一分式域上给出 Cauchy 极限。tilt 分式域的完备性／代数闭性、指定 F、全局 holomorphoid／Berkovich 基点／tempered marking、H¹ₑ/BK 和 theta／period／paper volume 及最终 3.12、G1–G4 仍开放，来源 bridge 父项未关闭。数学只在 Scene1/Derived；Core 假设增量 0，Prologue-R5 不变，无动态边界变更或数学负面证据，不写入 log5。


编辑期首检退出 1，64.799 秒、进程组峰值 RSS 5,495,912 KiB：principal ideal membership 须先显式 change 为 Set 后应用 closed-ball identity；将不存在的幂单调 API 名改为 `pow_le_pow_of_le_one`；兼容系数构造和最终稳定系数证明先展开 lambda／cauchyLimit 投影，补显式 change。清除 norm_eq_valuation 无用 CompleteSpace section 实例。类型／API／展开问题，不改变数学目标和前提，无 heartbeat 或内存失败。


通用叶第二次检查退出 1，72.018 秒、峰值 RSS 5,494,456 KiB，仅剩 `Nat.lt_two_pow_self` 的自然数参数在当前版本为 implicit，改为显式目标 `show m < 2^m` 后让其推断。系数球判据、逆极限极限构造与收敛证明未再报错；没有数学前提或目标变更，无 heartbeat／内存失败。


通用叶第三次检查退出 0，67.450 秒、5,495,512 KiB，完整逆极限完备性证明通过；日志提示 exists_coeffRadius_lt 仍自动带入不使用的 ultrametric／CompleteSpace section 实例。已在该定理前显式 omit，继续最终复验，不把带 warning 的编辑期成功作为最终验收。


验收（2026-10-19）：最终通用叶 `GeometricPreTiltCompleteness` 退出 0，67.360 秒、进程组峰值 RSS 5,496,568 KiB；最终实际消费者 `IutInitialThetaPreTiltCompleteness` 退出 0，119.563 秒、9,088,016 KiB。两叶最终日志均为空，无错误或 warning。`Checks.SceneBounds`、`Axioms.SceneBounds`、`Act1Scene1` 依次首次通过，耗时 127.196、122.152、124.784 秒，峰值 RSS 依次 9,398,268、9,379,476、9,262,812 KiB。21/21 个新增登记声明逐名通过公理核对；全部 2611 个打印声明仅含 `propext`、`Classical.choice`、`Quot.sound`，无 `sorryAx`；类型／公理日志无 warning，聚合日志为空。静态导入审计覆盖聚合及两个审计入口的 507 个可达本工程模块，扫描覆盖全部 import 行形式；无 Obligations、Candidate、Scene2、Act2 或 `Iut.*` 导入。新增源码未含 sorry/admit/自定义 axiom/opaque。打印签名确认 actual PreTilt 的 CompleteSpace、包含映射的等距性及像的完备性只依赖 D／支持处 w（和原隐式 AG／TG），没有外给完备性、等距或闭像 certificate。

本轮共 9 次直接 Lean 任务（7 次退出 0，其中 1 次编辑期带 warning 不作最终验收；2 次失败），退出 0 累计 745.547 秒、失败累计 136.817 秒、总计 882.364 秒；进程组峰值 RSS 9,398,268 KiB（8.963 GiB）。全部使用 CPU affinity `0–13`、`LEAN_NUM_THREADS=10`、Lean `-j1`，实际并发 worker 峰值 1；每 0.5 秒采样进程组 RSS，85 GiB 停止线未触发（用户上限 90 GiB）。无 heartbeat override。只用 `lake env lean -j1 -o` 访问现有依赖产物，未调用 Lake build 调度器、冷构建、重编 Mathlib 或变更冻结工具链/依赖。


### PreTilt 除法近似、实际 tilt 整数球身份及原分式域完备性

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-GEOMETRIC-PRETILT-DIVISION` | `GeometricPreTiltDivision.{shiftedUntilt,shiftedUntilt_reduction,shiftedUntilt_norm_pow,shiftedUntilt_ne_zero,shiftedUntilt_norm_le,quotientLift,quotientLift_mul,approximation,approximation_coeff,approximation_error_coeff,approximation_error_norm}`；`Act1Scene1/GeometricPreTiltDivision.lean` | Joshi `Arithmetic Holomorphic Structures.tex` 的 tilt／untilt（587–599）与此前 sharp／范数生产者；Mathlib PreTilt.coeff／Frobenius／untilt 及 rootLift 的实际 compatible roots。对实际 norm valuation integer ring 和原 `GeometricTiltField.Source Ω p`，`shiftedUntilt a n := untilt(Frob^(-n) a)` 的模 p 还原恰等于 coeff_n(a)，其 Ω 范数的 p^n 次幂等于 a 的实际 source norm。p^n>0 使 norm 顺序可从 a／b 的 norm 顺序传到两个 shifted untilt，b≠0 给分母 untilt 非零。`quotientLift` 是两个 actual shifted untilt 在 Ω 中的商，norm≤1 的证明使之属于真实 OΩ；在 OΩ 中证明 b_n*quotient=a_n。Ω 代数闭时取该实际整数商的 compatible-root lift，再作用 n 次 Frobenius 得原 PreTilt 中的 approximation c_n。coeff_n(c_n) 是整数商的 mod-p 像，ring-hom reduction 的乘法关系证明 coeff_n(a-b*c_n)=0；此前 exact coefficient-ball 定理因此给 `‖a-b*c_n‖≤‖p‖^(p^n)`。这是原 carrier 内的具体近似，不假设 PreTilt 已是 valuation ring，也不以 sharp 的乘法／范数身份虚构其加法逆映射。 | Scene1/Derived；proved |
| `JT-SCENE1-INITIAL-THETA-TILT-COMPLETENESS` | `InitialThetaTiltCompleteness.{fraction_representation,source_norm_le_one,integral_fraction_mem_closure,norm_le_one_mem_range,inclusion_range_eq_closedBall,closedBall_isComplete,carrierCompleteSpace,cauchySeq_converges,mem_inclusion_range_iff}`；`Act1Scene1/IutInitialThetaTiltCompleteness.lean` | 对同一 `D : InitialThetaData AG TG` 及 `w : (iutInitialThetaTateParameterData D).places`，始终使用此前 `InitialThetaTiltField.Carrier D w` 及已经赋予的 actual norm topology；不取新 completion，也不更改该 norm。`fraction_representation` 展开真实 fraction-field producer，给 x=i(a)/i(b)、b≠0；`source_norm_le_one` 由同一 canonical untilt 落在真实 integer ring 及已证 norm identity 得出。若 ‖a‖≤‖b‖，对任意 ε>0 选 n 使 ‖p‖^(p^n)<ε*‖i(b)‖；通用 c_n 的误差经同一个等距 inclusion 下传，得到 dist(i(a)/i(b),i(c_n))<ε，因此积分分式在原 PreTilt 像的 closure 中。若 tilt 元素 norm≤1，实际分式表示的 norm_div 和分母非零证明 ‖a‖≤‖b‖，此前 `inclusion_range_isClosed` 将 closure membership 升为 exact range membership。反向源 PreTilt 元素 norm≤1，因此 `inclusion_range_eq_closedBall` 给实际像恰等于同一 tilt 的闭单位球。上一轮已证的等距 complete range 让这个闭单位球 IsComplete，Mathlib `NormedField.completeSpace_iff_isComplete_closedBall` 据此证明原 tilt 分式域 CompleteSpace；最后提供 actual Cauchy sequence convergence 和 exact integral range criterion。没有外给 valuation-ring、球身份、complete certificate 或新几何系数域。 | Scene1/Derived；proved |

声明带前缀 `JoshiTeich.Act1Scene1`；20 个新增登记名称包括原 tilt 的新 CompleteSpace 实例，逐名登记于 Checks／Axioms 家族及 Scene1 聚合。两叶为原创证明／adapter，无 reference 工程源码复制或许可证增量，不导入 refer/iut，无新增 direct Mathlib import。仅使用现有预编译依赖，冻结工具链和缓存保持。

本单元实际关闭同一 tilt 分式域的完备性，精确补上此前闭完备 PreTilt 像到整个域的缺失连接：先证明近似，再用闭性得到 actual unit-ball 身份，最后使用 normed-field 完备判据。未仅凭子环完备性推断全域完备，也未把 sharp 当作跨特征加法同构。规范几何系数域的代数闭性用于实际整数商的 compatible-root lift；这是已有 source producer，不是新增输入。tilt 本身的代数闭性、到论文指定 F 的等距身份、Berkovich 基点／tempered marking／全局 holomorphoid、H¹ₑ/BK、theta／period／paper volume 和最终 3.12、G1–G4 仍开放，父项未关闭。数学只在 Scene1/Derived；Core 假设增量 0，Prologue-R5 不变，无动态边界变更或数学负面证据，不写入 log5。


编辑期首检：通用 division 叶退出 1，70.977 秒、进程组峰值 RSS 5,494,464 KiB；范数幂关系的 coe_pow 简化需显式加入 shiftedUntilt 定义；quotientLift_mul 不使用代数闭性，将 IsAlgClosed 实例推迟到实际 compatible-root lift 段。其余除法近似与误差界未报错。类型展开／实例范围问题，不变更数学前提或目标，无 heartbeat／内存失败。


实际消费者首检退出 1，117.081 秒、峰值 RSS 9,089,100 KiB：封装后的 actual tilt carrier 未注册 source→carrier Algebra，fraction_representation 改为显式在原 `GeometricTiltField.FractionField` 生产者上调用 IsFractionRing.div_surjective，再按定义还原 actual inclusion／carrier；不新增 Algebra 或 fraction-field 证书假设。另将分母 norm positivity 的局部 by/simpa 语法拆成显式 hbn 证明。其余任意精度近似、闭单位球身份及完备性步骤未报错；数学对象／前提不变，无 heartbeat／内存失败。


验收（2026-10-19）：最终通用叶 `GeometricPreTiltDivision` 退出 0，66.894 秒、进程组峰值 RSS 5,496,460 KiB；最终实际消费者 `IutInitialThetaTiltCompleteness` 退出 0，111.448 秒、9,092,156 KiB。两叶最终日志均为空，无错误或 warning。`Checks.SceneBounds`、`Axioms.SceneBounds`、`Act1Scene1` 依次首次通过，耗时 122.035、116.444、113.427 秒，峰值 RSS 依次 9,400,708、9,383,904、9,263,368 KiB。20/20 个新增登记声明逐名通过公理核对；全部 2631 个打印声明仅含 `propext`、`Classical.choice`、`Quot.sound`，无 `sorryAx`；类型／公理日志无 warning，聚合日志为空。静态导入审计覆盖聚合及两个审计入口的 509 个可达本工程模块，扫描覆盖全部 import 行形式；无 Obligations、Candidate、Scene2、Act2 或 `Iut.*` 导入。新增源码未含 sorry/admit/自定义 axiom/opaque。打印签名确认 actual tilt 的 closed-unit-ball 身份及 CompleteSpace 只依赖 D／支持处 w（和原隐式 AG／TG），不接收 valuation-ring、球身份、额外 Algebra 或完备性 certificate。

本轮共 7 次直接 Lean 任务（5 成功、2 失败），成功累计 530.248 秒、失败累计 188.058 秒、总计 718.306 秒；进程组峰值 RSS 9,400,708 KiB（8.965 GiB）。全部使用 CPU affinity `0–13`、`LEAN_NUM_THREADS=10`、Lean `-j1`，实际并发 worker 峰值 1；每 0.5 秒采样进程组 RSS，85 GiB 停止线未触发（用户上限 90 GiB）。无 heartbeat override。只用 `lake env lean -j1 -o` 访问现有依赖产物，未调用 Lake build 调度器、冷构建、重编 Mathlib 或变更冻结工具链/依赖。


### 原实际 tilt 的近似多项式根、真根及代数闭性

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-GEOMETRIC-PRETILT-POLYNOMIAL-ROOTS` | `GeometricPreTiltPolynomialRoots.{exists_coeff_root,exists_approx_root}`；`Act1Scene1/GeometricPreTiltPolynomialRoots.lean` | Joshi `Arithmetic Holomorphic Structures.tex` 在 tilt 讨论中明确要求 K^flat 为代数闭特征 p 域（587–599）；Mathlib `Polynomial.lifts_and_natDegree_eq_and_monic`、valuation integers 的 `mem_of_integral`、PreTilt coeff／Frobenius 及实际 rootLift 是具体 API。对原 `PreTilt(OΩ,p)` 上非恒定 monic P，先逐 coeff_n 映射得到 `(OΩ/p)[X]` 中同次数 monic Q，再利用真实 quotient map 的满射性将 Q 提升为 OΩ 中同次数 monic R。原代数闭 untilt Ω 中的 R 根 r 满足 IsIntegral OΩ r，valuation integers 的整性判据证明 r∈OΩ。取真实 rootLift(r)，向前作用 n 次 Frobenius 得 x∈原 PreTilt：coeff_n(x)=r mod p，reduction 的 ring-hom 求值交换式给 coeff_n(P(x))=0；x 的 untilt 在整数环内，故其 actual norm≤1。前轮 exact coefficient-ball 判据及半径趋零证明 `∀ε>0,∃x,‖x‖≤1 ∧ ‖P(x)‖<ε`。未给入原 PreTilt／tilt 中的根或多项式近似 certificate。 | Scene1/Derived；proved |
| `JT-SCENE1-COMPLETE-FIELD-APPROXIMATE-ROOTS` | `CompleteFieldApproximateRoots.{finite_separation,exists_root}`；`Act1Scene1/CompleteFieldApproximateRoots.lean` | Mathlib spectralNorm 的有限代数扩域赋范、complete-domain isometry 的闭像和 polynomial splitting 的有限根乘积公式。通用 complete nontrivially normed ultrametric K 上，对任意 monic P，假设仅为 `∀ε>0,∃x∈K,‖P(x)‖<ε`。在真实 P.SplittingField 上使用谱范数与 NormedAlgebra，其 K→L 映射等距，故 K 的像闭。若 P 在 K 无根，则有限 multiset Q.roots 的每一根不在闭像中；由 metric open-complement 和有限归纳取共同 δ>0，使每个扩域根到任意 K 元素的距离至少 δ。monic splitting 乘积公式给所有 x∈K 的 `‖P(x)‖≥δ^(roots.card)>0`，与任意小求值矛盾，因此根在原 K 中。没有用原 K 的 algebraic closedness，也没有假设某个近似根序列已经收敛；不要求 CharZero。 | Scene1/Derived；proved |
| `JT-SCENE1-INITIAL-THETA-TILT-ALGEBRAICALLY-CLOSED` | `InitialThetaTiltAlgebraicallyClosed.{integral_monic_approx_root,integral_monic_root,exists_integral_scale,monic_root,carrierIsAlgClosed,exists_pow_eq}`；`Act1Scene1/IutInitialThetaTiltAlgebraicallyClosed.lean` | 对同一 D／支持处 w，使用已经构造并证明完备的 `InitialThetaTiltField.Carrier D w` 和其原范数，未更换 carrier。整数系数 monic P 的每个 coefficient 由前轮闭单位球身份落在 actual PreTilt inclusion 的 image，monic lifting 定理给原 source 中同次数 monic R。通用近似根经过原等距 inclusion，给 P 在同一 tilt 的任意小求值；complete-field root criterion 给原域真根。一般 monic P 用 actual contracting tilt 元素 t：取非零 c=t^n 使 ‖c‖<1/max(P.supNorm,1)，`P.scaleRoots c` 的非最高项系数 norm≤supNorm(P)*‖c‖≤1，最高项仍为 1，高次项为 0；scaleRoots 保 monic／degree。取得 scaled polynomial 的原 tilt 根 y 后，非零 c 的求值公式给 y/c 是 P 的根。`IsAlgClosed.of_exists_root` 据此提供同一 actual tilt 的 IsAlgClosed 实例，并提供其任意正次幂方程有解。没有外给 polynomial roots、近似根、原 tilt algebraic closedness 或所选 F 的证书。 | Scene1/Derived；proved |

声明均带前缀 `JoshiTeich.Act1Scene1`，10 个新增登记名称包括原 tilt 的新 IsAlgClosed 实例，逐名登记于 Checks／Axioms 家族及 Scene1 聚合。三个新叶均为原创证明／adapter，无 reference 工程源码复制或许可证增量。新增直接 Mathlib imports 的现有 olean 已确认存在；缓存与冻结依赖保持，不导入 refer/iut。

本单元闭合此前同一 actual tilt carrier 上的代数闭性。原 Ω 的代数闭性用于真实 mod-p 多项式根生产，tilt 的代数闭性由误差趋零、原域完备性和 root-scaling 证明，未转而使用另一代数闭域满足弱接口。得到实际完整的代数闭、完备、非平凡 rank-one 特征 p tilt，sharp 的乘法／范数身份与同一 canonical untilt／Fontaine θ 的连接沿用此前生产者；没有把 sharp 误称跨特征 ring hom。指定 paper F 的等距身份、Berkovich 基点／tempered marking、全局 holomorphoid／跨 arithmeticoid、H¹ₑ/BK、theta／period／paper volume 与最终 3.12、G1–G4 仍开放，父项未关闭。数学只在 Scene1/Derived；Core 假设增量 0，Prologue-R5 不变，无动态边界变更或数学负面证据，不写入 log5。


编辑期：近似根叶首检退出 1，67.349 秒、进程组峰值 RSS 5,486,332 KiB；root 的 IsRoot 谓词／整数子环 coercion 需显式连接到真实 polynomial evaluation，Q 的局部定义须先 change 后改写 monic lift identity。第二次退出 1，67.850 秒、5,489,604 KiB；整数子环不是 IsSimpleRing，不能使用该条件下的 ring-hom.injective convenience API，改用实际 integer subring subtype.injective。均为 Lean 类型/API 问题，数学对象／前提／目标不变，无 heartbeat 或内存失败。

第三次近似根叶退出 1，70.575 秒、进程组峰值 RSS 5,489,596 KiB；subtype ring hom 上的 `.injective` 仍选择要求 IsSimpleRing 的 API，改为 `Subtype.ext`，显式将整数环求值强制到 Ω 后使用 eval_map_apply。无 heartbeat 或内存失败。

近似根叶第四次通过，65.856 秒、进程组峰值 RSS 5,489,488 KiB，日志为空。完备域判据叶首检退出 1，57.310 秒、4,617,832 KiB：归纳的 rfl 替换已消去旧变量 a，ball membership 改用当前 r；乘积范数改写需显式展开 Multiset.map_map／函数复合。同时将两处局部实例的 letI 改为 let 消除风格 warning。实际消费者在首次检查前，按已读 API 显式改写提升多项式的次数，并补 of_exists_root 的域参数。无 heartbeat 或内存失败。

完备域判据叶第二次退出 1，57.707 秒、进程组峰值 RSS 4,624,504 KiB；`NormedField.toMulRingNorm` 的函数值与目标所用 norm 未能经上述 simplification 匹配，改用直接陈述当前范数乘积公式的 `Multiset.norm_prod_map`。无 heartbeat 或内存失败。

验收（2026-10-19）：最终近似根叶 `GeometricPreTiltPolynomialRoots` 退出 0，65.856 秒、进程组峰值 RSS 5,489,488 KiB；完备域判据叶 `CompleteFieldApproximateRoots` 退出 0，55.693 秒、4,624,588 KiB；实际消费者 `IutInitialThetaTiltAlgebraicallyClosed` 首检退出 0，116.606 秒、9,088,788 KiB。三叶最终日志均为空，无错误或 warning。`Checks.SceneBounds`、`Axioms.SceneBounds`、`Act1Scene1` 依次首次通过，耗时 128.208、124.217、117.653 秒，峰值 RSS 依次 9,402,200、9,384,072、9,248,124 KiB。10/10 个新增登记声明逐名通过公理核对；全部 2641 个打印声明仅含 `propext`、`Classical.choice`、`Quot.sound`，无 `sorryAx`；类型／公理日志无 warning，聚合日志为空。静态导入审计覆盖聚合及两个审计入口的 512 个可达本工程模块，扫描覆盖全部 import 行形式；无 Obligations、Candidate、Scene2、Act2 或 `Iut.*` 导入。新增源码未含 sorry/admit/自定义 axiom/opaque。打印签名确认原 tilt 的 IsAlgClosed 只依赖同一 D／支持处 w（和原隐式 AG／TG），不接收额外根存在、近似、代数闭性、指定 F 或来源身份 certificate。

本轮共 11 次直接 Lean 任务（6 成功、5 失败），成功累计 608.233 秒、失败累计 320.791 秒、总计 929.024 秒；进程组峰值 RSS 9,402,200 KiB（8.967 GiB）。全部使用 CPU affinity `0–13`、`LEAN_NUM_THREADS=10`、Lean `-j1`，实际并发 worker 峰值 1；每 0.5 秒采样进程组 RSS，85 GiB 停止线未触发（用户上限 90 GiB）。无 heartbeat override。只用 `lake env lean -j1 -o` 访问现有依赖产物，未调用 Lake build 调度器、冷构建、重编 Mathlib 或变更冻结工具链/依赖。


### 实际 tilt 整数环、W(O_F) 上的 Fontaine θ 与 Teichmüller lifts

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-INITIAL-THETA-TILT-INTEGERS` | `InitialThetaTiltIntegers.{Integers,inclusion,inclusion_coe,inclusion_bijective,preTiltEquiv,preTiltEquiv_coe,preTiltEquiv_symm_coe,preTiltEquiv_isometry,preTiltEquiv_norm,sharp,sharp_norm,sharp_preTiltEquiv,sharp_surjective}`；`Act1Scene1/IutInitialThetaTiltIntegers.lean` | Joshi II §7 在 `pr:teichmuller-lift-A` 前使用 canonical `eta_K:W(O_F)→O_K`（932）；同一实际 tilt 的整数环身份来自前轮 PreTilt inclusion image=closed unit ball。`Integers` 是原 `InitialThetaTiltField.Carrier D w` 的同一 norm valuation integer ring，未另选整数环。将原 inclusion 限制到该实际 subring，实际等距性、单射性与闭单位球满射性构造 `preTiltEquiv`，给出正反向 coercion 身份及 isometry／norm 身份。原全域 sharp 的 norm identity 证明其在该整数环上落入同一 Ω 的真实整数环，构造 multiplicative integral sharp，并证明在原 PreTilt 上恰为原 untilt。全域 sharp 满射及 norm identity 证明该 integral sharp 满射；未构造跨特征加法映射。 | Scene1/Derived；proved |
| `JT-SCENE1-INITIAL-THETA-TILT-FONTAINE` | `InitialThetaTiltFontaine.{Ainf,preTiltWittEquiv,theta,theta_preTiltWittEquiv,theta_surjective,theta_teichmuller,theta_teichmuller_norm,integralLift,theta_integralLift,integralLift_norm,exists_teichmuller_lift,integralLift_norm_lt_one,theta_integralLift_pow,theta_fiber,theta_kernel_isPrime,quotientEquiv,quotientEquiv_mk,primitive,primitive_mem_kernel,primitive_ne_zero}`；`Act1Scene1/IutInitialThetaTiltFontaine.lean` | Joshi II canonical eta_K（932）、`pr:teichmuller-lift-A`（940–958）的 integral Teichmüller lift 及 kernel translate，以及（838）的 `[p-flat]-p` equation；Mathlib WittVector.map／teichmuller／constantCoeff 和 quotient-kernel theorem 是 API。`Ainf` 直接定义为 `WittVector p (Integers D w)`，p 为同一实际支持处的 residue characteristic。Witt functor 逐系数提升已证 ring equivalence，构造显式逆的 `preTiltWittEquiv`；theta 将此前 canonical Fontaine θ 沿该等价运输，`theta_preTiltWittEquiv` 证明与原 map 精确相同，满射来自原 θ 满射。Teichmüller 的自然性证明 theta([x])=integral sharp(x)，故 norm(theta([x]))=norm(x)。对原 OΩ 中任意 z，实际 compatible root tower 的 rootLift 经 preTiltEquiv 给 `integralLift z∈O_F`，证明 theta([lift z])=z、norm(lift z)=norm(z)，严格小于 1 时保持在 maximal-ideal norm ball；所有正整数幂（包括 j²）的求值由 θ 的 ring hom 法律给出。`theta_fiber` 给整个 fiber 恰为 ker(theta)+[lift z]，并未将 kernel 等同 Tate module。原 OΩ 为整域，故 θ 核为素理想；满射给 Ainf/ker(theta) 与该同一 OΩ 的 quotient ring equivalence。对 z=p 取得实际 integral lift，`primitive=[lift p]-p` 经 θ 求值为 0；其 constantCoeff 是非零 lift p（O_F 中 p=0，而 lift p 的 norm=norm(p)>0），故 primitive≠0。未证明该元素生成全部核，未声明 degree-one primitivity 或 Fargues–Fontaine 点身份。 | Scene1/Derived；proved |

声明均带前缀 `JoshiTeich.Act1Scene1`，33 个新增公开名称（含两个 carrier abbrev）逐名登记于 Checks／Axioms 家族及 Scene1 聚合。两个叶均为本工程原创证明／adapter，无 reference 工程源码复制或许可证增量。新增直接 Mathlib import `RingTheory.Ideal.Quotient.Operations` 的现有 olean 已确认存在；缓存与冻结依赖保持，不导入 refer/iut。

本单元将原 canonical Fontaine map 的定义域从 PreTilt 的 Witt vectors 精确接到同一实际 tilt 的 W(O_F)，并给出文献 Teichmüller lift 所需的原域元素、求值和 norm 身份。norm identity 只比较 x∈O_F 与其 actual untilt image，未给 W(O_F) 或 period ring B 伪造 Fréchet／ρ norm。未将所构造任意 integral 元素命名为论文 theta-value，未构造 FF curve／Tate module／BK、完整 period norm、primitive kernel generator、指定 F／Berkovich 基点／tempered marking／全局 holomorphoid。H¹ₑ、theta locus、paper volume／representative weights、最终 3.12 与 G1–G4 仍开放；checkbox 父项未关闭。所有数学只在 Scene1/Derived，Core 假设增量 0，Prologue-R5 不变；无边界变更或数学负面证据，不写入 log5。

编辑期：整数环叶首检通过，108.875 秒、进程组峰值 RSS 9,092,104 KiB，日志为空。Fontaine 叶首检退出 1，112.352 秒、9,102,728 KiB：ext tactic 递归穿过整数环 subtype，改用显式 WittVector.ext 停在 coefficient 层；PerfectoidData.theta 保存的是函数，组合 ring hom 时改用其定义上相同的 Perfectoid.thetaMap；CharP.cast_eq_zero 的裸改写先匹配到了特征零 untilt 内的 p，改为明确给出 tilt 整数环中 p=0 的等式后重写。均为 Lean API／类型选择问题，不改变数学对象或前提，无 heartbeat 或内存失败。

Fontaine 叶第二次退出 1，123.742 秒、进程组峰值 RSS 9,106,652 KiB：simpa 未展开封装后的 canonical untilt 函数字段，改用已证 actual theta_teichmuller_eq_sharp 和 PreTilt-equivalence 的逆向 coercion 身份，在实际 Ω 中经 Subtype.ext 比较；constantCoeff 的 Teichmüller 简化改为定义性 rfl，避免 p／系数环参数未定。无 heartbeat 或内存失败，数学目标与前提不变。

验收（2026-10-19）：整数环叶 `IutInitialThetaTiltIntegers` 首检退出 0，108.875 秒、进程组峰值 RSS 9,092,104 KiB；最终 Fontaine 叶 `IutInitialThetaTiltFontaine` 退出 0，113.474 秒、9,101,564 KiB。两叶最终日志均为空，无错误或 warning。`Checks.SceneBounds`、`Axioms.SceneBounds`、`Act1Scene1` 依次首次通过，耗时 130.304、120.169、127.238 秒，峰值 RSS 依次 9,404,896、9,388,644、9,264,532 KiB。33/33 个新增登记声明逐名通过公理核对；全部 2674 个打印声明仅含 `propext`、`Classical.choice`、`Quot.sound`，无 `sorryAx`；类型／公理日志无 warning，聚合日志为空。静态导入审计覆盖聚合及两个审计入口的 514 个可达本工程模块，扫描覆盖全部 import 行形式；无 Obligations、Candidate、Scene2、Act2 或 `Iut.*` 导入。新增源码未含 sorry/admit/自定义 axiom/opaque。打印签名确认实际 O_F、Ainf、θ、quotient equivalence 和非零 kernel element 只依赖同一 D／支持处 w（及作用的元素／幂次、原隐式 AG／TG），没有新的 integer-ring identity、equivalence、root、surjectivity 或 kernel certificate。

本轮共 7 次直接 Lean 任务（5 成功、2 失败），成功累计 600.060 秒、失败累计 236.094 秒、总计 836.154 秒；进程组峰值 RSS 9,404,896 KiB（8.969 GiB）。全部使用 CPU affinity `0–13`、`LEAN_NUM_THREADS=10`、Lean `-j1`，实际并发 worker 峰值 1；每 0.5 秒采样进程组 RSS，85 GiB 停止线未触发（用户上限 90 GiB）。无 heartbeat override。只用 `lake env lean -j1 -o` 访问现有依赖产物，未调用 Lake build 调度器、冷构建、重编 Mathlib 或变更冻结工具链/依赖。


### 同一实际 Fontaine θ 的精确 principal kernel 与显式商环

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-ADIC-KERNEL-DIVISION` | `AdicKernelDivision.{exists_factor,eq_span}`；`Act1Scene1/AdicKernelDivision.lean` | Joshi II `pa:Mochizuki-Ansatz`（838）的 kernel equation 所需 p-adic division；Mathlib `IsPrecomplete.prec`、`IsHausdorff.haus` 及 adic Cauchy successive criterion。对原 p-adically complete commutative ring R、理想 K 和 ξ，假设具体一步关系 `∀a∈K,∃c∈R,r∈K,a=ξc+pr`。选择该关系的 digit/residual 函数，迭代 residual 并取 `q_n=Σ_{i<n}p^i c_i`，归纳证明 `a=ξq_n+p^n r_n`。q_n 的相邻差落在 (p)^n，代数完备性给原 R 内极限 b，分离性由 `a-ξb∈(p)^n` 对所有 n 推出 a=ξb。若 ξ∈K，得到 K=(ξ)。未假设 (ξ) 已闭、Noetherianity、kernel 完备性或新商环分离性。这里的一步关系在下一 actual leaf 中完整证明，不作为最终 kernel theorem 的输入。 | Scene1/Derived；proved |
| `JT-SCENE1-INITIAL-THETA-FONTAINE-KERNEL` | `InitialThetaFontaineKernel.{integersPerfect,decomposition,constantCoeff_norm_le,constantCoeff_dvd,division_step,kernel_eq_span,mem_kernel_iff_dvd,primitive_prime,quotientPrimitiveEquiv,quotientPrimitiveEquiv_mk}`；`Act1Scene1/IutInitialThetaFontaineKernel.lean` | Joshi II `pa:Mochizuki-Ansatz`（838）明确给 `ker(eta_K:W(O_F)→O_K)=([p-flat]-p)`；此前实际 `InitialThetaTiltFontaine.primitive` 使用同一实际 Ω 中 p 的 compatible-root lift，未更改该选择。实际 O_F 的 perfectness 经原 PreTilt ring equivalence 传递，因此 Mathlib 的同一 Witt ring p-adic completeness 可用。`decomposition` 从零号系数判据得任意 a=[a_0]+pb。若 θ(a)=0，θ([a_0])=-pθ(b)，而 θ(b)∈真实 OΩ，既有 sharp/norm identity 给 norm(a_0)≤norm(p)。actual lift(p) 的 norm=norm(p)，真实 valuation integers 的整除判据给 a_0=p-flat·c。Teichmüller 乘法证明 `a=([p-flat]-p)[c]+p(b+[c])`，且实际 char-zero untilt 中 p≠0 让 b+[c] 仍在 θ 核中。通用 p-adic 除法因此证明同一实际 W(O_F) 上的精确 kernel_eq_span，继而给 θ(a)=0 iff primitive∣a、既有 primitive 的 prime-element 性质，以及按显式方程取商 `W(O_F)/([p-flat]-p)≃OΩ`，quotient map 精确等于原 θ。最终所有定理只接收同一 D／支持处 w（及作用元素），不接收 primitive generator、norm division、ideal closedness 或 kernel identity 证书。 | Scene1/Derived；proved |

12 个新增公开名称均带前缀 `JoshiTeich.Act1Scene1`，包括实际 O_F 的 PerfectRing 实例，逐名登记于 Checks／Axioms 家族及 Scene1 聚合。两个新叶均为本工程原创证明，没有复制 refer/iut 源码或许可证增量；不导入外部 Iut 模块。新增 direct Mathlib import `RingTheory.AdicCompletion.Basic` 的现有 olean 在构建前确认存在，实际 Witt 完备性 API 由既有 Fontaine 依赖提供，没有新编译 Mathlib。

本单元关闭上一轮明确保留的 actual principal-kernel equation，ξ 始终是前轮实际 `primitive D w`，不是通过存在性另选的生成元。得到的是实际 OΩ 的 integral quotient ring，未将它改称 Ω 或宣称该 integral ideal 已在 Ainf 中 maximal。未定义 FF curve／解析点／B 的 Fréchet ρ-norm、Tate module、BK/H¹ₑ、论文 theta-values locus、paper volume 或最终 3.12；指定 F／Berkovich 基点／tempered marking 和全局 holomorphoid 身份仍开放。所有数学只在 Scene1/Derived，Core 假设增量 0，Prologue-R5 不变；无边界变更或数学负面证据，不写入 log5，checkbox 父项保持开放。

编辑期：通用 adic 叶首检退出 1，47.586 秒、进程组峰值 RSS 3,706,412 KiB；局部变量 partial 是 Lean 保留字，改名 approx；mem_span_singleton 的 divisibility witness 使用 a=ξb 的原方向，span containment 改用 span_le。第二次退出 1，49.660 秒、3,767,488 KiB；Cauchy API 位于 AdicCompletion 命名空间，补全限定名称。均为语法／API 问题，无 heartbeat 或内存失败，数学对象和前提未改变。

通用 adic 叶第三次退出 1，52.204 秒、进程组峰值 RSS 3,732,144 KiB；理想取负闭合使用继承的 `(I^n).neg_mem`，而非不存在的 `Ideal.neg_mem`。其余 residual 归纳、Cauchy 极限和精确整除步骤未报错；无 heartbeat 或内存失败。

通用 adic 叶第四次通过，47.074 秒、进程组峰值 RSS 3,759,628 KiB，日志为空。实际 kernel 叶首检退出 1，112.424 秒、9,103,788 KiB：PerfectRing.bijective_frobenius 的输出按函数 `fun x=>x^p` 表示，ring equivalence transport 时将 hy 显式 change 为幂等式，移除回写 ring-hom Frobenius 的步骤。实际 mod-p 分解、norm bound、整数环整除、kernel division、principal identity 和显式 quotient 等步骤均未报错。无 heartbeat 或内存失败，数学对象与目标未改变。

验收（2026-10-19）：最终通用叶 `AdicKernelDivision` 退出 0，47.074 秒、进程组峰值 RSS 3,759,628 KiB；最终实际叶 `IutInitialThetaFontaineKernel` 退出 0，117.617 秒、9,098,200 KiB。两叶最终日志均为空，无错误或 warning。`Checks.SceneBounds`、`Axioms.SceneBounds`、`Act1Scene1` 依次首次通过，耗时 136.815、119.056、115.511 秒，峰值 RSS 依次 9,407,224、9,390,132、9,263,864 KiB。12/12 个新增登记声明逐名通过公理核对；全部 2686 个打印声明仅含 `propext`、`Classical.choice`、`Quot.sound`，无 `sorryAx`；类型／公理日志无 warning，聚合日志为空。静态导入审计覆盖聚合及两个审计入口的 516 个可达本工程模块，扫描覆盖全部 import 行形式；无 Obligations、Candidate、Scene2、Act2 或 `Iut.*` 导入。新增源码未含 sorry/admit/自定义 axiom/opaque。打印签名确认实际 principal-kernel equality、primitive 的 Prime 性质及按该显式方程的 quotient equivalence 只依赖同一 D／支持处 w（及作用元素，原隐式 AG／TG），不接收 generator、integral division、adic completeness、ideal closedness 或 kernel identity certificate。

本轮共 9 次直接 Lean 任务（5 成功、4 失败），成功累计 536.073 秒、失败累计 261.874 秒、总计 797.947 秒；进程组峰值 RSS 9,407,224 KiB（8.971 GiB）。全部使用 CPU affinity `0–13`、`LEAN_NUM_THREADS=10`、Lean `-j1`，实际并发 worker 峰值 1；每 0.5 秒采样进程组 RSS，85 GiB 停止线未触发（用户上限 90 GiB）。无 heartbeat override。只用 `lake env lean -j1 -o` 访问现有依赖产物，未调用 Lake build 调度器、冷构建、重编 Mathlib 或变更冻结工具链/依赖。


### 倒置 p 后的实际 Fontaine 求值、极大核及真实 untilt 域商

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-NORMED-INTEGER-LOCALIZATION` | `NormedIntegerLocalization.{exists_integral_multiple,field_isLocalization,fieldEquiv,fieldEquiv_algebraMap}`；`Act1Scene1/NormedIntegerLocalization.lean` | Joshi II 从 integral eta_K 到 untilt field evaluation 的来源连接；Mathlib powers localization。对原非阿基米德赋范域 Ω 及真实 norm valuation 整数环中的 s，若 norm(s)<1，对任意非零 x 选 n 使 norm(s)^n<1/norm(x)，直接证明 xs^n∈OΩ；x=0 单独处理。若 s≠0，则 Ω 中 s 为单位，整数环 embedding 单射，满足 IsLocalization.Away 的三个完整条件，证明原 Ω 就是 OΩ[1/s]，并构造 canonical AlgEquiv 及其在实际整数元素上的嵌入身份。未另取 fraction field 或外给 localization／surjectivity certificate，也未给抽象 localization 伪造范数。 | Scene1/Derived；proved |
| `JT-SCENE1-INITIAL-THETA-FONTAINE-LOCALIZATION` | `InitialThetaFontaineLocalization.{untiltIsLocalization,AinfInvertP,theta,theta_algebraMap,theta_surjective,localizedPrimitive,theta_localizedPrimitive,kernel_eq_span,mem_kernel_iff_dvd,kernel_isMaximal,prime_ne_zero,algebraMap_injective,localizedPrimitive_ne_zero,quotientEquiv,quotientPrimitiveEquiv,quotientPrimitiveEquiv_mk,sourceLocalizationEquiv,sourceLocalizationEquiv_algebraMap,untiltLocalizationEquiv,untiltLocalizationEquiv_algebraMap,theta_sourceLocalization}`；`Act1Scene1/IutInitialThetaFontaineLocalization.lean` | Joshi II `pa:Mochizuki-Ansatz`（838）的 primitive kernel、canonical eta_K（932）及 period ring 到 B_dR 的包含（1069–1076）；Mathlib `IsLocalization.map`／`ker_map`／`fontaineThetaInvertP`。同一 D／支持处 w 的实际 Ω 中 p≠0、norm(p)<1，通用定理证明同一原 Ω 是其整数环的 p-localization；未替换既有域。`AinfInvertP` 是原 actual W(O_F) 的 p-localization，θ 是此前实际 θ 的 localization，整数元素上的求值仍是原 θ 的 Ω 嵌入，满射性由同一原 θ 的满射给出。localization 保核，前轮已证 `kerθ=([p-flat]-p)` 直接给本轮精确 kernel_eq_span。其像 `localizedPrimitive` 经实际 p 非零和 localization embedding 单射证明仍非零；新 θ 的核因实际 codomain Ω 为域且 θ 满射而为极大理想。`quotientPrimitiveEquiv` 因而精确给 `W(O_F)[1/p]/([p-flat]-p)≃Ω`，quotient map 就是新 θ。对旧 PreTilt Witt source 使用前轮 preTiltWittEquiv 诱导 sourceLocalizationEquiv，原 integer-ring p-localization 到同一 Ω 给 untiltLocalizationEquiv；`theta_sourceLocalization` 证明两者与 Mathlib 原 `fontaineThetaInvertP` 的方形逐元素交换，未另造一个无来源的 θ 或 period evaluation。 | Scene1/Derived；proved |

25 个新增公开名称均带前缀 `JoshiTeich.Act1Scene1`，包含原 Ω 的 IsLocalization.Away 实例及 AinfInvertP carrier abbrev，逐名登记于 Checks／Axioms 家族和 Scene1 聚合。两个新叶均为原创证明／adapter，无 refer/iut 源码复制或许可证增量，不导入外部 Iut。新增 direct Mathlib imports `Localization.Away.Basic`、`Localization.Algebra` 和 `Perfectoid.BDeRham` 的既有 olean 已逐项确认存在；只读使用 Mathlib，没有重编 Mathlib 或变更冻结依赖。

本单元从上一轮 integral quotient OΩ 推进到同一真实 untilt 域 Ω 的 field quotient，核仍由上一轮同一个 primitive 的实际像生成，并精确接回 Mathlib 原 Fontaine localization producer。这里只构造 W(O_F)[1/p] 的代数求值及极大核，未将此 localization 命名为完整 Fargues–Fontaine Fréchet ring B、未宣称该代数极大理想已是某个 Berkovich／FF 解析点；尚未构造 B 的 ρ-norm、B_dR 的 completion／DVR 或 Tate module、BK/H¹ₑ、论文 theta locus／volume。指定 F、Berkovich 基点、tempered marking、全局 holomorphoid、paper accounting、最终 3.12 和 G1–G4 仍开放，checkbox 父项未关闭。所有数学只在 Scene1/Derived，Core 假设增量 0，Prologue-R5 不变；无边界变更或数学负面证据，不写入 log5。

编辑期：通用 integer-localization 叶首检退出 1，63.787 秒、进程组峰值 RSS 5,483,912 KiB；范数收缩的证明在子环元素 s 与其 Ω coercion 的 norm 表示间未自动转换，定理直接明确使用原域 norm(s:Ω)，随后原有范数乘法估计通过。第二次退出 0，75.038 秒、5,480,588 KiB，最终日志为空。无 heartbeat 或内存失败，数学对象与目标未改变。

实际 localization 叶首检退出 1，142.835 秒、进程组峰值 RSS 9,106,692 KiB。`quotientPrimitiveEquiv_mk` 在默认 200000 heartbeat 的 whnf 阶段超时，按用户顺序先将该声明扩大到 1000000 重试。另修复原域 algebraMap 与 subtype coercion 的显式 API 连接；source localization 的 map_powers 结果是 monoid hom，保 p 需显式使用同一 RingEquiv 的 toRingHom.map_natCast；交换图中把 .toRingHom 应用明确 change 为 equivalence 应用，再使用已有 algebraMap 身份。失败声明引发的生成 sorry／未使用 simp warning 不作为验收；最终需重新完整检查。数学对象、θ 和 kernel 目标保持，无内存失败。

实际叶第二次退出 1，184.722 秒、进程组峰值 RSS 9,128,792 KiB，同一商环求值声明在 1000000 heartbeat 再次 whnf 超时。按用户顺序进行一次优化：先显式展开 quotient equivalence 的两步组合并重写 quotient-mk transport，再把 θ 和满射证明显式传给 quotient-kernel 求值定理，避免未定 `_` 参数触发整套 localization 类型展开；同时将该声明上限翻倍到 2000000。sourceLocalizationEquiv 另明确给出原／目标 powers 子幺半群，解决 map_powers 改写中的未定底环元素；移除交换图中的 unnecessarySeqFocus 风格 warning。数学目标与实际来源不变，无内存失败。

验收（2026-10-19）：最终通用叶 `NormedIntegerLocalization` 退出 0，75.038 秒、进程组峰值 RSS 5,480,588 KiB；优化后的实际叶 `IutInitialThetaFontaineLocalization` 退出 0，115.000 秒、9,107,740 KiB。两叶最终日志均为空，无错误或 warning。`Checks.SceneBounds`、`Axioms.SceneBounds`、`Act1Scene1` 依次首次通过，耗时 137.030、133.867、121.153 秒，峰值 RSS 依次 9,408,844、9,391,748、9,265,700 KiB。25/25 个新增登记声明逐名通过公理核对；全部 2711 个打印声明仅含 `propext`、`Classical.choice`、`Quot.sound`，无 `sorryAx`；类型／公理日志无 warning，聚合日志为空。最终静态导入审计覆盖聚合及两个审计入口的 518 个可达本工程模块，扫描覆盖全部 import 行形式；无 Obligations、Candidate、Scene2、Act2 或 `Iut.*` 导入。新增源码未含 sorry/admit/自定义 axiom/opaque。打印签名确认原 Ω 的 localization 身份、倒置 p 后的精确核／域商及与原 fontaineThetaInvertP 的交换图只依赖同一 D／支持处 w（及作用元素，原隐式 AG／TG），无额外 field、localization、surjectivity、kernel 或 equivalence certificate。

本轮共 8 次直接 Lean 任务（5 成功、3 失败；其中 2 次 heartbeat 超时、1 次 norm coercion 失败），成功累计 582.088 秒、失败累计 391.344 秒、总计 973.432 秒；进程组峰值 RSS 9,408,844 KiB（8.973 GiB）。全部使用 CPU affinity `0–13`、`LEAN_NUM_THREADS=10`、Lean `-j1`，实际并发 worker 峰值 1；每 0.5 秒采样进程组 RSS，85 GiB 停止线未触发（用户上限 90 GiB）。heartbeat 顺序严格为默认 200000 失败 → 1000000 失败 → 优化并翻倍到 2000000 通过；最终 override 仅作用于实际叶的 quotientPrimitiveEquiv_mk，其他新声明和审计保持默认限额。只用 `lake env lean -j1 -o` 访问现有依赖产物，未调用 Lake build 调度器、冷构建、重编 Mathlib 或变更冻结工具链/依赖。


### Actual de Rham completion 的 θ、主极大理想与剩余域

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-ADIC-RESIDUE-EVALUATION` | `JoshiTeich.Act1Scene1.AdicResidueEvaluation.evaluation`, `JoshiTeich.Act1Scene1.AdicResidueEvaluation.evaluation_algebraMap`, `JoshiTeich.Act1Scene1.AdicResidueEvaluation.evaluation_surjective`, `JoshiTeich.Act1Scene1.AdicResidueEvaluation.kernel_eq_map`, `JoshiTeich.Act1Scene1.AdicResidueEvaluation.kernel_eq_span`, `JoshiTeich.Act1Scene1.AdicResidueEvaluation.complete`, `JoshiTeich.Act1Scene1.AdicResidueEvaluation.quotientEquiv`, `JoshiTeich.Act1Scene1.AdicResidueEvaluation.quotientEquiv_mk`, `JoshiTeich.Act1Scene1.AdicResidueEvaluation.kernel_isMaximal`, `JoshiTeich.Act1Scene1.AdicResidueEvaluation.localRing`, `JoshiTeich.Act1Scene1.AdicResidueEvaluation.maximalIdeal_eq_kernel`, `JoshiTeich.Act1Scene1.AdicResidueEvaluation.isUnit_iff`；`Act1Scene1/AdicResidueEvaluation.lean` | Mathlib `AdicCompletion.evalOneₐ`、`ker_evalOneₐ_eq_map`、`isAdicComplete_self` 与 complete-maximal-ideal locality；将既有剩余域等价延拓到实际 adic completion，证明满射、精确核、按核完备、局部性、单位判据及商等价。通用源环无需 Noetherian／local 假设；有限生成与域商是显式输入。 原创消费者证明，无参考工程代码复制。 | Scene1/Derived；proved / accepted |
| `JT-SCENE1-INITIAL-THETA-DE-RHAM-COMPLETION` | `JoshiTeich.Act1Scene1.InitialThetaDeRhamCompletion.Source`, `JoshiTeich.Act1Scene1.InitialThetaDeRhamCompletion.sourceTheta`, `JoshiTeich.Act1Scene1.InitialThetaDeRhamCompletion.sourceTheta_eq`, `JoshiTeich.Act1Scene1.InitialThetaDeRhamCompletion.sourceTheta_surjective`, `JoshiTeich.Act1Scene1.InitialThetaDeRhamCompletion.sourceKernel`, `JoshiTeich.Act1Scene1.InitialThetaDeRhamCompletion.sourceTheta_kernel`, `JoshiTeich.Act1Scene1.InitialThetaDeRhamCompletion.sourcePrimitive`, `JoshiTeich.Act1Scene1.InitialThetaDeRhamCompletion.sourceKernel_eq_span`, `JoshiTeich.Act1Scene1.InitialThetaDeRhamCompletion.sourceKernel_fg`, `JoshiTeich.Act1Scene1.InitialThetaDeRhamCompletion.sourceQuotientEquiv`, `JoshiTeich.Act1Scene1.InitialThetaDeRhamCompletion.sourceQuotientEquiv_mk`, `JoshiTeich.Act1Scene1.InitialThetaDeRhamCompletion.Ring`, `JoshiTeich.Act1Scene1.InitialThetaDeRhamCompletion.theta`, `JoshiTeich.Act1Scene1.InitialThetaDeRhamCompletion.theta_of`, `JoshiTeich.Act1Scene1.InitialThetaDeRhamCompletion.theta_of_actual`, `JoshiTeich.Act1Scene1.InitialThetaDeRhamCompletion.theta_surjective`, `JoshiTeich.Act1Scene1.InitialThetaDeRhamCompletion.primitive`, `JoshiTeich.Act1Scene1.InitialThetaDeRhamCompletion.theta_primitive`, `JoshiTeich.Act1Scene1.InitialThetaDeRhamCompletion.kernel_eq_span`, `JoshiTeich.Act1Scene1.InitialThetaDeRhamCompletion.kernel_isMaximal`, `JoshiTeich.Act1Scene1.InitialThetaDeRhamCompletion.complete`, `JoshiTeich.Act1Scene1.InitialThetaDeRhamCompletion.localRing`, `JoshiTeich.Act1Scene1.InitialThetaDeRhamCompletion.maximalIdeal_eq_kernel`, `JoshiTeich.Act1Scene1.InitialThetaDeRhamCompletion.maximalIdeal_eq_span`, `JoshiTeich.Act1Scene1.InitialThetaDeRhamCompletion.completeMaximalIdeal`, `JoshiTeich.Act1Scene1.InitialThetaDeRhamCompletion.isUnit_iff`, `JoshiTeich.Act1Scene1.InitialThetaDeRhamCompletion.quotientEquiv`, `JoshiTeich.Act1Scene1.InitialThetaDeRhamCompletion.residueEquiv`, `JoshiTeich.Act1Scene1.InitialThetaDeRhamCompletion.residueEquiv_residue`；`Act1Scene1/IutInitialThetaDeRhamCompletion.lean` | Joshi II primitive kernel（838）、canonical eta_K（932）及 B_cris⊂B_st⊂B_dR（1069–1076）；Joshi III §5 local Hodge rings 和 theta locus 到 B_dR 的连接；Mathlib `BDeRhamPlus` 定义。对同一 D／w 的原 PreTilt Witt localization，用前轮交换图把实际 theta 和既有主核运输到原 `fontaineThetaInvertP`，直接在原 Mathlib `BDeRhamPlus OΩ p` carrier 上延拓 theta 到同一 Ω，证明满射、精确 principal maximal kernel、按该核及按极大理想完备、local ring、单位判据和实际 residue field≃Ω，并证明原 source／实际 W(O_F)[1/p] 上的交换及 residue 求值身份。无自由 untilt、kernel／residue／locality 证书。 原创消费者证明，无参考工程代码复制。 | Scene1/Derived；proved / accepted |

这里只关闭同一实际 `B_dR⁺` 的代数求值与 complete local ring 性质；没有宣称生成元在完备化中仍非零、DVR／period field、Fréchet B／ρ-norm、Fargues–Fontaine 解析点、Tate module 或论文 theta locus／holomorphoid 身份。上述后续数学义务及完整 3.12 仍开放。保持 Prologue-R5／Core、旧声明与冻结依赖不变，无新增数学前提或许可证增量；无动态边界修订或数学负面证据，不追加 log5。

验收：最终通用叶、实际叶、`Checks.SceneBounds`、`Axioms.SceneBounds` 与 `Act1Scene1` 全部退出 0，耗时依次为 57.220、153.338、143.039、123.674、125.703 秒；进程组峰值 RSS 依次为 4,551,788、9,269,032、9,413,344、9,395,412、9,266,012 KiB。两叶及汇总最终日志均为空，两项审计无 warning／error；41 个新增公开声明逐名核对，2752 个公理条目全部只含 `propext`、`Classical.choice`、`Quot.sound`，无 `sorryAx`；静态导入审计覆盖 520 个可达工程模块，无 Obligations、Candidate、Scene2、Act2 或 `Iut.*` 导入。

编辑期记录：通用叶首检退出 1（80.218 秒，4,559,028 KiB），将不存在的 Ideal.span_singleton_fg 改为实际 Submodule.fg_span_singleton，并去除重叠的 CommRing／Field 实例；第二次退出 1（72.069 秒，4,556,460 KiB），localRing 的结论未提及剩余域等价，Lean 自动省略该 section 参数，显式 include e 后解决。第三次退出 0（63.451 秒，4,552,816 KiB），两条 letI 风格提示清理为 let，随后最终通用叶无警告通过。实际叶首检退出 1（128.767 秒，9,195,568 KiB），BDeRhamPlus wrapper 阻止通用 completion 的局部环实例自动匹配，补局部显式连接；residue-field wrapper 下的 quotient 复合改写改为明确 change 到 quotient-mk 表达式。实际叶第二次无警告通过。上述均为 Lean API／参数／实例／展开适配，数学目标和前提不变，无 heartbeat 或内存失败。

本轮共 9 次直接 Lean 任务（6 次退出 0，其中 1 次编辑期有风格 warning 不作最终验收；3 次失败），退出 0 累计 666.425 秒、失败累计 281.054 秒、总计 947.479 秒；进程组峰值 RSS 9,413,344 KiB（8.977 GiB）。全部使用 CPU affinity `0–13`、`LEAN_NUM_THREADS=10`、Lean `-j1`，实际并发 worker 峰值 1；每 0.5 秒采样进程组 RSS，85 GiB 停止线未触发（用户上限 90 GiB）。无 heartbeat override。只用 `lake env lean -j1 -o` 访问现有依赖产物，未调用 Lake build 调度器、冷构建、重编 Mathlib 或变更冻结工具链／依赖。


### Actual de Rham DVR 与同一 primitive uniformizer

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-SEPARATED-PRINCIPAL-LOCAL-DVR` | `JoshiTeich.Act1Scene1.SeparatedPrincipalLocalRing.completion_pow_ne_zero`, `JoshiTeich.Act1Scene1.SeparatedPrincipalLocalRing.exists_pow_not_dvd`, `JoshiTeich.Act1Scene1.SeparatedPrincipalLocalRing.factorization`, `JoshiTeich.Act1Scene1.SeparatedPrincipalLocalRing.domain`, `JoshiTeich.Act1Scene1.SeparatedPrincipalLocalRing.discreteValuationRing`；`Act1Scene1/SeparatedPrincipalLocalRing.lean` | Mathlib AdicCompletion finite-level evaluation／IsHausdorff 和 `IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization`。原整域内非零非单位 π 在 (π)-adic completion 中的 n 次幂若为零，取模 (π)^(n+1) 得 π^n∈(π^(n+1))，消去 π^n 会使 π 为单位，矛盾；因此所有幂不消失。在按极大理想分离的局部环中，由非零 x 不被所有 π^n 整除取最小失败指数，最高次除法后的因子必须为单位；非零幂与单位分解给出无零因子及 DVR。通用法律显式接收相应数学前提，不要求原环 Noetherian／local。 原创消费者证明，无参考工程代码复制。 | Scene1/Derived；proved / accepted |
| `JT-SCENE1-INITIAL-THETA-DE-RHAM-DVR` | `JoshiTeich.Act1Scene1.InitialThetaDeRhamDVR.sourcePrimitive_ne_zero`, `JoshiTeich.Act1Scene1.InitialThetaDeRhamDVR.sourcePrimitive_not_isUnit`, `JoshiTeich.Act1Scene1.InitialThetaDeRhamDVR.primitive_pow_ne_zero`, `JoshiTeich.Act1Scene1.InitialThetaDeRhamDVR.primitive_ne_zero`, `JoshiTeich.Act1Scene1.InitialThetaDeRhamDVR.factorization`, `JoshiTeich.Act1Scene1.InitialThetaDeRhamDVR.domain`, `JoshiTeich.Act1Scene1.InitialThetaDeRhamDVR.discreteValuationRing`, `JoshiTeich.Act1Scene1.InitialThetaDeRhamDVR.primitive_irreducible`, `JoshiTeich.Act1Scene1.InitialThetaDeRhamDVR.primitive_prime`；`Act1Scene1/IutInitialThetaDeRhamDVR.lean` | Joshi II primitive kernel（838）、canonical eta_K（932）及 B_cris⊂B_st⊂B_dR（1069–1076）；Joshi III local Hodge rings；Mathlib BDeRhamPlus／DVR 判据。对同一实际 D／w，通过原 PreTilt Witt localization 到实际 W(O_F)[1/p] 的既有等价取得 source domain，原 θ 将同一个 sourcePrimitive 映到零而其本身非零，故非单位；前述通用生产者证明同一 actual BDeRhamPlus 中 primitive 的所有幂非零、整域性、DVR、原 primitive 不可约且为素，以及每个非零 actual 元素的 unit-times-primitive-power 分解。完备性消费前轮实际主极大理想完备实例；actual 输入仍仅为同一 D／w，没有新增 domain／nonvanishing／DVR 证书。 原创消费者证明，无参考工程代码复制。 | Scene1/Derived；proved / accepted |

这里只闭合同一实际 `B_dR⁺` 的 complete DVR 身份与原 primitive uniformizer；完整 period field 的局部化身份、Fréchet B／ρ-norm、Fargues–Fontaine 解析点、Tate module 和论文 theta locus／holomorphoid 身份以及完整 3.12 仍开放。保持 Prologue-R5／Core、旧声明和冻结依赖不变，无新增数学前提或许可证增量；无动态边界修订或数学负面证据，不追加 log5。

验收：最终通用叶、实际叶、`Checks.SceneBounds`、`Axioms.SceneBounds` 与 `Act1Scene1` 全部退出 0，耗时依次为 60.362、128.319、144.626、127.157、122.593 秒；进程组峰值 RSS 依次为 4,275,016、9,102,140、9,415,000、9,397,900、9,224,860 KiB。两叶及汇总最终日志均为空，两项审计无 warning／error；14 个新增公开声明逐名核对，2766 个公理条目全部只含 `propext`、`Classical.choice`、`Quot.sound`，无 `sorryAx`。actual domain／DVR／uniformizer 定理签名只接收既有 D／w，没有新增证书参数；静态导入审计覆盖 522 个可达工程模块，无 Obligations、Candidate、Scene2、Act2 或 `Iut.*` 导入。

编辑期记录：通用叶首检退出 1（58.844 秒，4,270,424 KiB），补 source self algebraMap 的显式化简；用 include 保留证明体使用的 hspan section 参数；ideal smul-top 明确改写为 ideal multiplication；整域判据显式传底环 R；移除 IsLocalRing 已蕴含的重复 Nontrivial 参数。第二次退出 0（62.086 秒，4,286,636 KiB），仅一条 unnecessarySimpa 提示，将失败指数不为零的矛盾处理改为 simp at hh，未改公开声明／数学内容。实际叶首次即无警告通过（128.319 秒，9,102,140 KiB）；清理后的通用叶第三次无警告通过，再顺序运行上述三项审计。首轮失败均为 Lean 类型／API／section 参数适配，数学对象及前提不变，无 heartbeat 或内存失败。

本轮共 7 次直接 Lean 任务（6 次退出 0，其中 1 次编辑期有风格 warning 不作最终验收；1 次失败），退出 0 累计 645.143 秒、失败累计 58.844 秒、总计 703.987 秒；进程组峰值 RSS 9,415,000 KiB（8.979 GiB）。全部使用 CPU affinity `0–13`、`LEAN_NUM_THREADS=10`、Lean `-j1`，实际并发 worker 峰值 1；每 0.5 秒采样进程组 RSS，85 GiB 停止线未触发（用户上限 90 GiB）。无 heartbeat override。只用 `lake env lean -j1 -o` 访问现有依赖产物，未调用 Lake build 调度器、冷构建、重编 Mathlib 或变更冻结工具链／依赖。


### 原 B_dR 的 primitive localization 与实际分式域身份

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-UNIFORMIZER-LOCALIZATION` | `JoshiTeich.Act1Scene1.UniformizerLocalization.generators_localization`, `JoshiTeich.Act1Scene1.UniformizerLocalization.fractionRing`；`Act1Scene1/UniformizerLocalization.lean` | Mathlib `IsLocalization.of_le`、associated elements 和 fraction-ring API。若集合 s 包含 π 且每个元素都与 π 相伴，则在 π-localization 中 s 的每个元素都为单位，因而得到沿 closure(s) 的实际 localization 身份。若原整域每个非零元素都是 π 的幂乘单位，则在 π-localization 中所有非零元素都为单位，得到原环的 IsFractionRing 身份。通用参数显式，不外给目标域结构。 原创消费者证明，无参考工程代码复制。 | Scene1/Derived；proved / accepted |
| `JT-SCENE1-INITIAL-THETA-DE-RHAM-FIELD` | `JoshiTeich.Act1Scene1.InitialThetaDeRhamField.completedGenerators`, `JoshiTeich.Act1Scene1.InitialThetaDeRhamField.denominators`, `JoshiTeich.Act1Scene1.InitialThetaDeRhamField.Carrier`, `JoshiTeich.Act1Scene1.InitialThetaDeRhamField.commRing`, `JoshiTeich.Act1Scene1.InitialThetaDeRhamField.algebra`, `JoshiTeich.Act1Scene1.InitialThetaDeRhamField.localization`, `JoshiTeich.Act1Scene1.InitialThetaDeRhamField.sourceGenerator_associated`, `JoshiTeich.Act1Scene1.InitialThetaDeRhamField.primitive_mem_generators`, `JoshiTeich.Act1Scene1.InitialThetaDeRhamField.generator_associated`, `JoshiTeich.Act1Scene1.InitialThetaDeRhamField.localizationEquiv`, `JoshiTeich.Act1Scene1.InitialThetaDeRhamField.localizationEquiv_algebraMap`, `JoshiTeich.Act1Scene1.InitialThetaDeRhamField.away`, `JoshiTeich.Act1Scene1.InitialThetaDeRhamField.fractionRing`, `JoshiTeich.Act1Scene1.InitialThetaDeRhamField.field`, `JoshiTeich.Act1Scene1.InitialThetaDeRhamField.algebraMap_injective`, `JoshiTeich.Act1Scene1.InitialThetaDeRhamField.primitive_image_ne_zero`, `JoshiTeich.Act1Scene1.InitialThetaDeRhamField.primitive_image_isUnit`, `JoshiTeich.Act1Scene1.InitialThetaDeRhamField.exists_primitive_denominator`, `JoshiTeich.Act1Scene1.InitialThetaDeRhamField.fractionEquiv`, `JoshiTeich.Act1Scene1.InitialThetaDeRhamField.fractionEquiv_algebraMap`；`Act1Scene1/IutInitialThetaDeRhamField.lean` | Joshi II primitive kernel／eta_K（838、932）及 B_cris⊂B_st⊂B_dR（1069–1076）；Joshi III local Hodge rings；Mathlib 原 BDeRham 定义。对同一 D／w，原 sourceKernel 的任意生成元在同一 B_dR⁺ 中的像仍生成 actual θ 核，故与同一 primitive 相伴。精确保留 Mathlib BDeRham OΩ p 的原 carrier 和倒置全部 kernel generators 的原分母子幺半群，构造它与只倒置 primitive 的 AlgEquiv 及交换公式，证明原 B_dR 是同一 complete DVR 的 IsFractionRing 并赋予 Field，证明自然嵌入单射、primitive 像非零且为单位、任意元素的 primitive-power 分母表示，以及与标准 FractionRing 的规范代数等价和交换公式。actual 输入仍仅为既有 D／w，不另给 field／localization／generator identity 证书。 原创消费者证明，无参考工程代码复制。 | Scene1/Derived；proved / accepted |

这里只闭合同一实际 `B_dR` 的代数 period-field／fraction-ring 身份和自然嵌入；未由此宣称其拓扑／赋值完备性、Fréchet B／ρ-norm、Fargues–Fontaine 解析点、Tate module 或论文 theta locus／holomorphoid 身份，完整 3.12 仍开放。保持 Prologue-R5／Core、旧声明和冻结依赖不变，无新增数学前提或许可证增量；无动态边界修订或数学负面证据，不追加 log5。

验收：通用叶、最终实际叶、`Checks.SceneBounds`、`Axioms.SceneBounds` 与 `Act1Scene1` 全部退出 0，耗时依次为 50.174、121.495、132.800、125.101、120.087 秒；进程组峰值 RSS 依次为 3,618,056、9,226,804、9,417,580、9,400,132、9,265,708 KiB。两叶及汇总最终日志均为空，两项审计无 warning／error；22 个新增公开声明逐名核对，2788 个公理条目全部只含 `propext`、`Classical.choice`、`Quot.sound`，无 `sorryAx`。actual localization／fraction-ring／Field／自然嵌入定理签名只接收既有 D／w，无新增证书参数；静态导入审计覆盖 524 个可达工程模块，无 Obligations、Candidate、Scene2、Act2 或 `Iut.*` 导入。

编辑期记录：通用叶首次无警告通过（50.174 秒，3,618,056 KiB）。实际叶首检退出 1（130.349 秒，9,164,412 KiB）：span-singleton associated 判据需要显式指定 actual BDeRhamPlus 载体，generators localization 的局部实例需明确给 denominators 类型以跨越其 def wrapper；补齐后第二次退出 1（123.542 秒，9,162,148 KiB），仅剩 calc 在底层 AdicCompletion 与 BDeRhamPlus 定义相同的 ideal carrier 之间不能合成 Trans。改为显式声明 actual theta 核等式 hk，再以 hk.symm.trans 连接原 kernel_eq_span，第三次无警告通过。上述均为 Lean 类型／实例／封装适配，未改变数学对象、公开目标或前提，无 heartbeat 或内存失败。

本轮共 7 次直接 Lean 任务（5 成功、2 失败），成功累计 549.657 秒、失败累计 253.891 秒、总计 803.548 秒；进程组峰值 RSS 9,417,580 KiB（8.981 GiB）。全部使用 CPU affinity `0–13`、`LEAN_NUM_THREADS=10`、Lean `-j1`，实际并发 worker 峰值 1；每 0.5 秒采样进程组 RSS，85 GiB 停止线未触发（用户上限 90 GiB）。无 heartbeat override。只用 `lake env lean -j1 -o` 访问现有依赖产物，未调用 Lake build 调度器、冷构建、重编 Mathlib 或变更冻结工具链／依赖。


### Actual B_dR 的离散赋值、整数环与 θ 滤过

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-INITIAL-THETA-DE-RHAM-VALUATION` | `JoshiTeich.Act1Scene1.InitialThetaDeRhamValuation.valuation`, `JoshiTeich.Act1Scene1.InitialThetaDeRhamValuation.discrete`, `JoshiTeich.Act1Scene1.InitialThetaDeRhamValuation.valuation_surjective`, `JoshiTeich.Act1Scene1.InitialThetaDeRhamValuation.integers`, `JoshiTeich.Act1Scene1.InitialThetaDeRhamValuation.valuation_le_one_iff`, `JoshiTeich.Act1Scene1.InitialThetaDeRhamValuation.valuation_primitive`, `JoshiTeich.Act1Scene1.InitialThetaDeRhamValuation.valuation_lt_one_iff_theta_eq_zero`, `JoshiTeich.Act1Scene1.InitialThetaDeRhamValuation.valuation_eq_one_iff_theta_ne_zero`, `JoshiTeich.Act1Scene1.InitialThetaDeRhamValuation.mem_kernel_pow_iff`, `JoshiTeich.Act1Scene1.InitialThetaDeRhamValuation.integerEquiv`, `JoshiTeich.Act1Scene1.InitialThetaDeRhamValuation.integerEquiv_coe`, `JoshiTeich.Act1Scene1.InitialThetaDeRhamValuation.integerTheta`, `JoshiTeich.Act1Scene1.InitialThetaDeRhamValuation.integerTheta_integerEquiv`, `JoshiTeich.Act1Scene1.InitialThetaDeRhamValuation.integerTheta_surjective`, `JoshiTeich.Act1Scene1.InitialThetaDeRhamValuation.integerTheta_eq_zero_iff`, `JoshiTeich.Act1Scene1.InitialThetaDeRhamValuation.integerQuotientEquiv`, `JoshiTeich.Act1Scene1.InitialThetaDeRhamValuation.integerQuotientEquiv_mk`, `JoshiTeich.Act1Scene1.InitialThetaDeRhamValuation.nonzero_zpow_factorization`；`Act1Scene1/IutInitialThetaDeRhamValuation.lean` | Joshi II primitive kernel／eta_K（838、932）及 B_cris⊂B_st⊂B_dR（1069–1076）；Joshi III local Hodge rings；Mathlib `IsDiscreteValuationRing.maximalIdeal`、其离散 adic valuation 与 `exists_lift_of_le_one`。对同一 D／w 的原 BDeRham，使用原 complete DVR BDeRhamPlus 的实际极大理想构造 ℤᵐ⁰ 值的满射离散赋值，证明 primitive 像的赋值精确为 exp(-1)、赋值≤1 当且仅当属于原 plus ring 的嵌入像，并构造原 plus ring 到赋值整数环的 ring equivalence 及原嵌入交换公式。证明赋值<1 当且仅当 θ=0、赋值=1 当且仅当 θ≠0，以及 ker(θ)^n 的完整赋值球判据。原 θ 经该等价运输到赋值整数环，证明求值一致、满射、核为赋值<1 的元素和整数环商≃原 Ω 及商求值身份；非零 field 元素为 plus-unit 乘同一 primitive 像的整数次幂。actual 输入仍仅为 D／w，无自由 valuation、integer identity 或 residue 证书。原创消费者证明，无参考工程代码复制。 | Scene1/Derived；proved / accepted |

这里的赋值是 primitive-adic 离散赋值。本单元未证明 period-field 的赋值拓扑完备性，也未将该离散赋值等同 Fréchet B／ρ-norm、原 untilt 的非离散范数或 theta locus 的 period norm。Fargues–Fontaine 解析点、Tate module、论文 theta locus／holomorphoid 身份及完整 3.12 仍开放。Prologue-R5／Core、旧声明、冻结依赖和原 actual carrier 均保持，无新增数学前提或许可证增量；无动态边界修订或数学负面证据，不追加 log5。

验收：最终实际叶、`Checks.SceneBounds`、`Axioms.SceneBounds` 与 `Act1Scene1` 全部退出 0，耗时依次为 116.528、123.541、119.498、121.091 秒；进程组峰值 RSS 依次为 9,099,408、9,419,444、9,400,876、9,267,160 KiB。实际叶及汇总最终日志均为空，两项审计无 warning／error；18 个新增公开声明逐名核对，2806 个公理条目全部只含 `propext`、`Classical.choice`、`Quot.sound`，无 `sorryAx`。actual valuation／integer identity／theta filtration 关键签名只接收既有 D／w，无新增证书参数；静态导入审计覆盖 525 个可达工程模块，无 Obligations、Candidate、Scene2、Act2 或 `Iut.*` 导入。

编辑期记录：首检退出 1（126.827 秒，9,100,732 KiB），未开启 WithZero scope 导致 ℤᵐ⁰ 记号无法解析，后续为级联错误；补 scope，并给整数环等价的 ring-hom 结构显式类型。第二次退出 1（111.322 秒，9,099,816 KiB），exists_of_le_one 的隐式 r 量词需 eta expansion，同时该 ring-hom 字面量缺右花括号。第三次退出 1（117.487 秒，9,095,612 KiB），两个量词适配均已解决，但右花括号在第二次修改中漏补；明确补齐结构字面量并保持自然嵌入上的定义性求值，第四次无警告通过。赋值归一化、θ 的严格不等式／单位判据和 kernel-power 滤过在 scope 修正后未再报错。三次均为 Lean 语法／notation／隐式参数适配，不变更数学对象或前提，无 heartbeat 或内存失败；失败声明的自动生成缺口及其 warning 从未作为验收。

本轮共 7 次直接 Lean 任务（4 成功、3 失败），成功累计 480.658 秒、失败累计 355.636 秒、总计 836.294 秒；进程组峰值 RSS 9,419,444 KiB（8.983 GiB）。全部使用 CPU affinity `0–13`、`LEAN_NUM_THREADS=10`、Lean `-j1`，实际并发 worker 峰值 1；每 0.5 秒采样进程组 RSS，85 GiB 停止线未触发（用户上限 90 GiB）。无 heartbeat override。只用 `lake env lean -j1 -o` 访问现有依赖产物，未调用 Lake build 调度器、冷构建、重编 Mathlib 或变更冻结工具链／依赖。


### 同一 actual B_dR 的 primitive-adic 范数拓扑与完备性

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-ADIC-NORMED-INTEGERS-COMPLETENESS` | `JoshiTeich.Act1Scene1.AdicNormedIntegers.isAdic`, `JoshiTeich.Act1Scene1.AdicNormedIntegers.sourceComplete`, `JoshiTeich.Act1Scene1.AdicNormedIntegers.fieldComplete`；`Act1Scene1/AdicNormedIntegers.lean` | Mathlib `IsAdic.isPrecomplete_iff`、ultrametric closed-ball openness、isometric complete ranges 及 `NormedField.completeSpace_iff_isComplete_closedBall`。在显式 normed ring／field 和等距 ring hom 上，若理想幂精确为收缩非零元素幂半径球的逆像，证明原拓扑为该理想的 adic topology，进而将代数 adic 完备性转为原 source 的 CompleteSpace；若 source 完备且像为 field 闭单位球，则原 field 完备。全部通用前提显式，不将任意完备化载体替代原 field。 原创消费者证明，无参考工程代码复制。 | Scene1/Derived；proved / accepted |
| `JT-SCENE1-INITIAL-THETA-DE-RHAM-TOPOLOGY` | `JoshiTeich.Act1Scene1.InitialThetaDeRhamTopology.valueEmbedding`, `JoshiTeich.Act1Scene1.InitialThetaDeRhamTopology.valueEmbedding_strictMono`, `JoshiTeich.Act1Scene1.InitialThetaDeRhamTopology.normValuation`, `JoshiTeich.Act1Scene1.InitialThetaDeRhamTopology.absoluteValue`, `JoshiTeich.Act1Scene1.InitialThetaDeRhamTopology.fieldNormed`, `JoshiTeich.Act1Scene1.InitialThetaDeRhamTopology.norm_eq_value`, `JoshiTeich.Act1Scene1.InitialThetaDeRhamTopology.norm_le_iff`, `JoshiTeich.Act1Scene1.InitialThetaDeRhamTopology.norm_le_one_iff`, `JoshiTeich.Act1Scene1.InitialThetaDeRhamTopology.fieldUltrametric`, `JoshiTeich.Act1Scene1.InitialThetaDeRhamTopology.plusNormed`, `JoshiTeich.Act1Scene1.InitialThetaDeRhamTopology.inclusion_norm`, `JoshiTeich.Act1Scene1.InitialThetaDeRhamTopology.inclusion_isometry`, `JoshiTeich.Act1Scene1.InitialThetaDeRhamTopology.primitive_norm`, `JoshiTeich.Act1Scene1.InitialThetaDeRhamTopology.kernel_power_eq_ball`, `JoshiTeich.Act1Scene1.InitialThetaDeRhamTopology.plus_isAdic`, `JoshiTeich.Act1Scene1.InitialThetaDeRhamTopology.plusComplete`, `JoshiTeich.Act1Scene1.InitialThetaDeRhamTopology.inclusion_range_eq_closedBall`, `JoshiTeich.Act1Scene1.InitialThetaDeRhamTopology.fieldComplete`, `JoshiTeich.Act1Scene1.InitialThetaDeRhamTopology.inclusion_range_isClosed`, `JoshiTeich.Act1Scene1.InitialThetaDeRhamTopology.cauchySeq_converges`, `JoshiTeich.Act1Scene1.InitialThetaDeRhamTopology.fieldValued`, `JoshiTeich.Act1Scene1.InitialThetaDeRhamTopology.valued_eq_normValuation`；`Act1Scene1/IutInitialThetaDeRhamTopology.lean` | Joshi II primitive kernel／eta_K（838、932）及 B_dR 连接（1069–1076）；Joshi III local Hodge rings；Mathlib `WithZeroMulInt.toNNReal`、absolute-value normed fields 和 adic completeness/topology。对同一 D／w 的原实际 BDeRham carrier，将前轮 ℤᵐ⁰ 值离散赋值经严格单调的 exp(n)↦2^n 映射取为范数，证明范数比较与原赋值比较精确等价、primitive 像范数=1/2、ultrametric 和 norm-induced Valued 实例与所用实值赋值一致。plus ring 在原自然单射上取 induced norm；证明自然嵌入等距及 ker(θ)^n 精确等于 primitive-norm^n 闭球的逆像，从而证明其 norm topology 确为 kernel-adic。由既有 IsAdicComplete 得原 plus ring 的 CompleteSpace；其实际像精确为 field 闭单位球，因此同一原 B_dR field 在该范数下 CompleteSpace。另证明 plus 像闭、原 field 中任意 Cauchy sequence 收敛。actual 输入仍仅 D／w，没有外给范数、拓扑或完备性证书，也没有另取完备化。 原创消费者证明，无参考工程代码复制。 | Scene1/Derived；proved / accepted |

这里的范数明确为 primitive-adic（primitive 半径 1/2），且拓扑与前轮离散赋值比较相容；没有将它识别为原 untilt 非离散范数、Fréchet B／ρ-norm 或论文 theta locus 的 period norm。Fargues–Fontaine 解析点、Tate module、论文 theta locus／holomorphoid 身份及完整 3.12 仍开放。Prologue-R5／Core、旧声明、冻结依赖和原实际 carrier 均保持，无新增数学前提或许可证增量；无动态边界修订或数学负面证据，不追加 log5。

验收：最终通用叶、实际叶、`Checks.SceneBounds`、`Axioms.SceneBounds` 与 `Act1Scene1` 全部退出 0，耗时依次为 54.194、123.200、142.994、132.825、121.022 秒；进程组峰值 RSS 依次为 3,998,180、9,097,280、9,421,808、9,404,324、9,267,400 KiB。两叶及汇总最终日志均为空，两项审计无 warning／error；25 个新增公开声明逐名核对，2831 个公理条目全部只含 `propext`、`Classical.choice`、`Quot.sound`，无 `sorryAx`。actual plus-isAdic／plus-CompleteSpace／field-CompleteSpace 关键签名只接收既有 D／w，无新增证书参数；静态导入审计覆盖 527 个可达工程模块，无 Obligations、Candidate、Scene2、Act2 或 `Iut.*` 导入。

编辑期记录：通用叶首检退出 1（54.289 秒，3,970,960 KiB），理想幂直接标注 Set 时 Lean 选择集合幂，明确先标注 Ideal R 再转集合；同时 omit fieldComplete 不使用的 ultrametric section 实例。第二次退出 1（56.280 秒，3,999,780 KiB），嵌套 by 的目标缺失，拆成明确 norm inequality 的 have 后，第三次无警告通过（54.194 秒，3,998,180 KiB）。实际叶首检退出 1（125.233 秒，9,100,060 KiB），未开启 NNReal 记号作用域，ℝ≥0 被解析为比较表达式，后续均为级联错误；补作用域后第二次退出 1（124.185 秒，9,096,860 KiB），仅剩 Valued 逐点身份中 ext 已深入到实数等式而证明多包一层 Subtype.ext，直接给 norm_eq_value 后第三次无警告通过（123.200 秒，9,097,280 KiB）。范数球、kernel-adic topology 和两个 actual 完备实例在作用域修正后未再报错。上述均为 Lean 类型／notation／局部证明适配，数学对象及前提不变，无 heartbeat 或内存失败；失败声明的自动生成缺口及其 warning 从未作为验收。

本轮共 9 次直接 Lean 任务（5 成功、4 失败），成功累计 574.235 秒、失败累计 359.987 秒、总计 934.222 秒；进程组峰值 RSS 9,421,808 KiB（8.985 GiB）。全部使用 CPU affinity `0–13`、`LEAN_NUM_THREADS=10`、Lean `-j1`，实际并发 worker 峰值 1；每 0.5 秒采样进程组 RSS，85 GiB 停止线未触发（用户上限 90 GiB）。无 heartbeat override。只用 `lake env lean -j1 -o` 访问现有依赖产物，未调用 Lake build 调度器、冷构建、重编 Mathlib 或变更冻结工具链／依赖。


### 实际 Tate 参数的 Teichmüller／de Rham 局部 pilot

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-INITIAL-THETA-DE-RHAM-TEICHMULLER` | `JoshiTeich.Act1Scene1.InitialThetaDeRhamTeichmuller.localizationToPlus`, `JoshiTeich.Act1Scene1.InitialThetaDeRhamTeichmuller.theta_localizationToPlus`, `JoshiTeich.Act1Scene1.InitialThetaDeRhamTeichmuller.ainfToPlus`, `JoshiTeich.Act1Scene1.InitialThetaDeRhamTeichmuller.theta_ainfToPlus`, `JoshiTeich.Act1Scene1.InitialThetaDeRhamTeichmuller.lift`, `JoshiTeich.Act1Scene1.InitialThetaDeRhamTeichmuller.theta_lift`, `JoshiTeich.Act1Scene1.InitialThetaDeRhamTeichmuller.theta_lift_pow`, `JoshiTeich.Act1Scene1.InitialThetaDeRhamTeichmuller.evaluation_norm`, `JoshiTeich.Act1Scene1.InitialThetaDeRhamTeichmuller.lift_isUnit`, `JoshiTeich.Act1Scene1.InitialThetaDeRhamTeichmuller.fiber`, `JoshiTeich.Act1Scene1.InitialThetaDeRhamTeichmuller.kernel_translate_pow`；`Act1Scene1/IutInitialThetaDeRhamTeichmuller.lean` | Joshi II `pr:teichmuller-lift-A`（940–958）及到 B_dR 的连接（1069–1076）；Mathlib WittVector／AdicCompletion 和既有 actual theta kernel。对同一 D／w，将原实际 W(O_F) 经原 p-localization 和原 PreTilt source equivalence 映入同一 BDeRhamPlus，证明与同一 actual θ 交换。把既有 compatible-root Teichmüller lift 实际送入 plus ring，证明求值、任意幂、untilt-evaluation norm、非零值的 lift 为单位，以及完整 fiber 恰为 primitive·b+lift 和这些 translate 的幂求值。只使用已证实际生产者；没有假设 W→completion 单射或 Tate module 身份。 原创消费者证明，无参考工程代码复制。 | Scene1/Derived；proved / accepted |
| `JT-SCENE1-INITIAL-THETA-TATE-DE-RHAM-PILOT` | `JoshiTeich.Act1Scene1.InitialThetaTateDeRhamPilot.tateValue`, `JoshiTeich.Act1Scene1.InitialThetaTateDeRhamPilot.tateValue_ne_zero`, `JoshiTeich.Act1Scene1.InitialThetaTateDeRhamPilot.tateValue_norm`, `JoshiTeich.Act1Scene1.InitialThetaTateDeRhamPilot.tateValue_norm_lt_one`, `JoshiTeich.Act1Scene1.InitialThetaTateDeRhamPilot.root_exists`, `JoshiTeich.Act1Scene1.InitialThetaTateDeRhamPilot.root`, `JoshiTeich.Act1Scene1.InitialThetaTateDeRhamPilot.root_pow`, `JoshiTeich.Act1Scene1.InitialThetaTateDeRhamPilot.root_ne_zero`, `JoshiTeich.Act1Scene1.InitialThetaTateDeRhamPilot.root_norm_pow`, `JoshiTeich.Act1Scene1.InitialThetaTateDeRhamPilot.root_norm_lt_one`, `JoshiTeich.Act1Scene1.InitialThetaTateDeRhamPilot.integralRoot`, `JoshiTeich.Act1Scene1.InitialThetaTateDeRhamPilot.tiltRoot`, `JoshiTeich.Act1Scene1.InitialThetaTateDeRhamPilot.tiltRoot_norm`, `JoshiTeich.Act1Scene1.InitialThetaTateDeRhamPilot.tiltRoot_norm_lt_one`, `JoshiTeich.Act1Scene1.InitialThetaTateDeRhamPilot.pilot`, `JoshiTeich.Act1Scene1.InitialThetaTateDeRhamPilot.pilot_isUnit`, `JoshiTeich.Act1Scene1.InitialThetaTateDeRhamPilot.theta_pilot`, `JoshiTeich.Act1Scene1.InitialThetaTateDeRhamPilot.theta_pilot_ne_zero`, `JoshiTeich.Act1Scene1.InitialThetaTateDeRhamPilot.theta_pilot_root_equation`, `JoshiTeich.Act1Scene1.InitialThetaTateDeRhamPilot.evaluation_norm`, `JoshiTeich.Act1Scene1.InitialThetaTateDeRhamPilot.evaluation_log`, `JoshiTeich.Act1Scene1.InitialThetaTateDeRhamPilot.evaluation_product`, `JoshiTeich.Act1Scene1.InitialThetaTateDeRhamPilot.evaluation_log_sum`, `JoshiTeich.Act1Scene1.InitialThetaTateDeRhamPilot.fiber`, `JoshiTeich.Act1Scene1.InitialThetaTateDeRhamPilot.root_log`, `JoshiTeich.Act1Scene1.InitialThetaTateDeRhamPilot.evaluation_log_eq_tate`；`Act1Scene1/IutInitialThetaTateDeRhamPilot.lean` | Joshi II `pr:teichmuller-lift-A/B`、`thm:theta-pilot-object-appears`（940–1013）以及 B_dR 连接（1069–1076）。从同一 D 的 actual supported base place w 读取原 TateParameterData.parameter，以原 completionEmbedding 送入原 Ω，证明非零且 norm 等于同一 TateParameterData.norm。直接利用 Ω 的既有代数闭性构造 2ℓ 次根，证明 root equation、非零、norm<1、norm^(2ℓ)=原 Tate norm 和 log(root norm)=log(原 Tate norm)/(2ℓ)；将根作为实际 Ω 整数再由同一 compatible-root lift 送入实际 O_F，保范数且<1。原 BDeRhamPlus 中的 pilot(j)=lift^(j²)，证明其单位性、非零求值、求值的 2ℓ 次幂为原 Tate value^(j²)、范数／对数／任意有限 index 集的乘积与和，以及 exact principal-kernel fiber；求值对数精确为 j²/(2ℓ)·log(原 Tate norm)。actual 输入仍仅 D／w，没有额外 root／norm／evaluation 证书。 原创消费者证明，无参考工程代码复制。 | Scene1/Derived；proved / accepted |

本单元处理一个实际 base-place untilt 中的 Tate-root 幂和其在原 B_dR⁺ 中的 lift。根由该 Ω 内的真实根生产者选取，未声称它已等同前轮 torsion-field completion 上的特定 q-root，也未识别跨 holomorphoid／Ansatz 的不同 untilts。所有范数和 log 公式明确是 θ 求值后的 untilt 范数；没有把 primitive-adic 范数认作论文 B 的 Fréchet／ρ-norm。实际 paper theta-values／theta locus、Tate module、FF 点／holomorphoid 身份、adelic collation 及完整 3.12 仍开放。Prologue-R5／Core、旧声明和冻结依赖保持，无新增数学前提或许可证增量；无动态边界修订或数学负面证据，不追加 log5。

验收：Witt/de Rham 连接叶、最终实际 Tate pilot 叶、`Checks.SceneBounds`、`Axioms.SceneBounds` 与 `Act1Scene1` 全部退出 0，耗时依次为 128.781、132.471、137.418、134.281、126.172 秒；进程组峰值 RSS 依次为 9,170,844、9,101,856、9,425,188、9,407,652、9,271,920 KiB。两叶及汇总最终日志均为空，两项审计无 warning／error；37 个新增公开声明逐名核对，2868 个公理条目全部只含 `propext`、`Classical.choice`、`Quot.sound`，无 `sorryAx`。actual root equation／theta pilot／evaluation-log／fiber 关键签名只接收既有 D／w、指数和被测元素，无新增 root／norm／evaluation 证书参数；静态导入审计覆盖 529 个可达工程模块，无 Obligations、Candidate、Scene2、Act2 或 `Iut.*` 导入。

编辑期记录：Witt/de Rham 连接叶首次无警告通过（128.781 秒，9,170,844 KiB）。实际 Tate pilot 叶首检退出 1（126.740 秒，9,099,020 KiB），root_norm_lt_one 中直接嵌套 Nat.mul_ne_zero 的首因子尚为 metavariable，by decide 缺少确定类型；拆出显式 `hp : 2*ℓ≠0` 后解决。同批补上 root_log 和 evaluation_log_eq_tate，将局部 untilt 范数公式接回同一实际 TateParameterData.norm 的 j²/(2ℓ) 定量值，第二次无警告通过（132.471 秒，9,101,856 KiB）。首次失败为 Lean 类型推断适配，既有数学对象／前提不变，无 heartbeat 或内存失败。

本轮共 6 次直接 Lean 任务（5 成功、1 失败），成功累计 659.123 秒、失败累计 126.740 秒、总计 785.863 秒；进程组峰值 RSS 9,425,188 KiB（8.989 GiB）。全部使用 CPU affinity `0–13`、`LEAN_NUM_THREADS=10`、Lean `-j1`，实际并发 worker 峰值 1；每 0.5 秒采样进程组 RSS，85 GiB 停止线未触发（用户上限 90 GiB）。无 heartbeat override。只用 `lake env lean -j1 -o` 访问现有依赖产物，未调用 Lake build 调度器、冷构建、重编 Mathlib 或变更冻结工具链／依赖。


### 原 torsion q-root 到同一 untilt／de Rham pilot 的实际来源连接

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-FINITE-COMPLETION-ALGEBRAIC-EMBEDDING` | `JoshiTeich.Act1Scene1.FiniteCompletionEmbedding.embedding`, `JoshiTeich.Act1Scene1.FiniteCompletionEmbedding.embedding_base`, `JoshiTeich.Act1Scene1.FiniteCompletionEmbedding.embedding_injective`；`Act1Scene1/FiniteCompletionEmbedding.lean` | Joshi I local untilt embeddings、Joshi II local Teichmüller lifts；Mathlib `IsAlgClosed.lift` 和既有 `LocalCompletion.finite_relativeAlgebra`。对实际 number-field places v|w 的 completion，显式安装原 iutEmbedCompletion 给出的有限相对代数，将给定的 base completion→代数闭 Ω 嵌入延拓为原 extension completion→Ω ring hom，证明原 base completion 上交换及单射。该生产者构造的是实际代数嵌入，不假设 raw completion 范数等距。 原创消费者证明，无参考工程代码复制。 | Scene1/Derived；proved / accepted |
| `JT-SCENE1-INITIAL-THETA-TORSION-DE-RHAM-PILOT` | `JoshiTeich.Act1Scene1.InitialThetaTorsionDeRhamPilot.embedding`, `JoshiTeich.Act1Scene1.InitialThetaTorsionDeRhamPilot.embedding_base`, `JoshiTeich.Act1Scene1.InitialThetaTorsionDeRhamPilot.embedding_injective`, `JoshiTeich.Act1Scene1.InitialThetaTorsionDeRhamPilot.supported_bad`, `JoshiTeich.Act1Scene1.InitialThetaTorsionDeRhamPilot.parameter_eq_tate`, `JoshiTeich.Act1Scene1.InitialThetaTorsionDeRhamPilot.qroot_power`, `JoshiTeich.Act1Scene1.InitialThetaTorsionDeRhamPilot.rootImage`, `JoshiTeich.Act1Scene1.InitialThetaTorsionDeRhamPilot.rootImage_pow`, `JoshiTeich.Act1Scene1.InitialThetaTorsionDeRhamPilot.rootImage_ne_zero`, `JoshiTeich.Act1Scene1.InitialThetaTorsionDeRhamPilot.rootImage_norm_pow`, `JoshiTeich.Act1Scene1.InitialThetaTorsionDeRhamPilot.rootImage_norm`, `JoshiTeich.Act1Scene1.InitialThetaTorsionDeRhamPilot.rootImage_norm_lt_one`, `JoshiTeich.Act1Scene1.InitialThetaTorsionDeRhamPilot.qroot_norm_eq_image_pow`, `JoshiTeich.Act1Scene1.InitialThetaTorsionDeRhamPilot.qroot_log_eq_degree_mul`, `JoshiTeich.Act1Scene1.InitialThetaTorsionDeRhamPilot.phase`, `JoshiTeich.Act1Scene1.InitialThetaTorsionDeRhamPilot.phase_pow`, `JoshiTeich.Act1Scene1.InitialThetaTorsionDeRhamPilot.phase_norm`, `JoshiTeich.Act1Scene1.InitialThetaTorsionDeRhamPilot.integralImage`, `JoshiTeich.Act1Scene1.InitialThetaTorsionDeRhamPilot.pilot`, `JoshiTeich.Act1Scene1.InitialThetaTorsionDeRhamPilot.theta_pilot`, `JoshiTeich.Act1Scene1.InitialThetaTorsionDeRhamPilot.theta_pilot_eq_phase_mul`, `JoshiTeich.Act1Scene1.InitialThetaTorsionDeRhamPilot.evaluation_norm`, `JoshiTeich.Act1Scene1.InitialThetaTorsionDeRhamPilot.evaluation_log_eq_tate`；`Act1Scene1/IutInitialThetaTorsionDeRhamPilot.lean` | Joshi II `pr:teichmuller-lift-A/B` 及 local pilot（940–1013）；Joshi III relative-degree weights；原 actual `qrootAt_pow_eq_of_liesOver`。对同一 D、实际 supported base place w 和任意 torsion place v|w，以前述嵌入生产者把原 v-completion 映入前轮同一个 Ω，严格延拓原 base completionEmbedding。actual qrootAt 的真实像满足 2ℓ 次幂=同一 tateValue，非零；其范数等于前轮所选 Ω 根的范数，且<1。保留 iutRelativeRamificationIndex·relInertDeg 的完整次数 d，证明原 torsion q-root norm=image norm^d 与 log(norm raw)=d·log(norm image)。像与前轮根的商 phase 满足 phase^(2ℓ)=1 和 norm=1。对原 q-root 的像取 actual Teichmüller lift 于原 B_dR⁺，证明 j² 求值与前轮 pilot 相差 phase^(j²)、求值范数完全相同，并继承 j²/(2ℓ)·log(原 Tate norm) 公式。actual 输入仅既有 D／w／v 和 place lies-over 关系，无外给 extension embedding／root／norm 身份证书。 原创消费者证明，无参考工程代码复制。 | Scene1/Derived；proved / accepted |

这里关闭了前轮特定 torsion completion q-root 到同一 Ω 的代数嵌入与实际 pilot 比较；延拓嵌入的选择不称为规范或等距，完整 raw norm 次数保留。未声称不同 holomorphoid／Ansatz 的 untilts 身份、论文 theta-values／theta locus、Tate module、B 的 Fréchet／ρ-norm、adelic collation 或完整 3.12。Prologue-R5／Core、旧声明和冻结依赖不变，无新增数学前提或许可证增量；无动态边界修订或数学负面证据，不追加 log5。

验收：最终通用嵌入叶、实际 torsion pilot 叶、`Checks.SceneBounds`、`Axioms.SceneBounds` 与 `Act1Scene1` 全部退出 0，耗时依次为 77.086、139.238、147.800、139.150、125.789 秒；进程组峰值 RSS 依次为 5,459,588、9,243,996、9,428,396、9,410,616、9,268,260 KiB。两叶及汇总最终日志均为空，两项审计无 warning／error；26 个新增公开声明逐名核对，2894 个公理条目全部只含 `propext`、`Classical.choice`、`Quot.sound`，无 `sorryAx`。actual embedding-extension／root equation／relative-degree norm／phase comparison 关键签名只接收既有 D／w／v、原 places-over 关系及被测元素或指数，没有外给嵌入／norm 证书；静态导入审计覆盖 531 个可达工程模块，无 Obligations、Candidate、Scene2、Act2 或 `Iut.*` 导入。

编辑期记录：通用叶首检退出 1（70.909 秒，5,448,832 KiB），section 层的 local instance 依赖显式 hvw／ι，不能由实例目标推断；改为在定义／证明内部显式安装 relative algebra、target algebra 和 finite-module 生产者。第二次退出 0（72.489 秒，5,461,172 KiB），两条 letI 风格提示改为 let；第三次无警告通过（77.086 秒，5,459,588 KiB）。实际叶首检退出 1（127.259 秒，9,244,808 KiB）：旧 iutInitialThetaQParameter 是 private 声明，改由公开 TateParameterData 的定义等式证明同一参数身份；root-image 幂公式明确传 hvw，避免 rw 生成未解处关系。第二次退出 1（128.179 秒，9,244,172 KiB），条件分支中 Tate q 为单位，需明确强制到 completion 域使 else 0 类型成立；第三次退出 0（135.056 秒，9,244,468 KiB），日志有一条 dif_pos 弃用提示，非空日志 gate 阻止审计启动；替换为 dite_eq_left 后第四次无警告通过（139.238 秒，9,243,996 KiB），再执行三项收尾审计。均为 Lean 实例／API／强制转换适配，数学对象及前提不变；未发生 heartbeat 或内存失败。

本轮共 10 次直接 Lean 任务（7 次退出 0，其中 2 次编辑期有提示不作最终验收；3 次失败），退出 0 累计 836.608 秒、失败累计 326.347 秒、总计 1162.955 秒；进程组峰值 RSS 9,428,396 KiB（8.992 GiB）。全部使用 CPU affinity `0–13`、`LEAN_NUM_THREADS=10`、Lean `-j1`，实际并发 worker 峰值 1；每 0.5 秒采样进程组 RSS，85 GiB 停止线未触发（用户上限 90 GiB）。无 heartbeat override。只用 `lake env lean -j1 -o` 访问现有依赖产物，未调用 Lake build 调度器、冷构建、重编 Mathlib 或变更冻结工具链／依赖。


### 原 torsion-completion 嵌入的拓扑与全域次数范数公式

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-CLOSED-FIELD-EMBEDDING-NORM` | `JoshiTeich.Act1Scene1.ClosedFieldEmbeddingNorm.pullback`, `JoshiTeich.Act1Scene1.ClosedFieldEmbeddingNorm.norm_lt_one_iff`, `JoshiTeich.Act1Scene1.ClosedFieldEmbeddingNorm.norm_eq_pow`；`Act1Scene1/ClosedFieldEmbeddingNorm.lean` | Mathlib absolute-value equivalence 与幂趋零判据。对 normed fields 之间的 topological embedding f，幂趋零在 f 下等价，故 norm(fx)<1↔norm(x)<1；两实绝对值因此等价，得到正实指数 c。若一个显式非零收缩校准值已满足 norm(a)=norm(fa)^d，则实幂单射确定 c=d，从而所有 x 均满足 norm(x)=norm(fx)^d。通用假设显式，不要求校准值额外生成整个 field。 原创消费者证明，无参考工程代码复制。 | Scene1/Derived；proved / accepted |
| `JT-SCENE1-FINITE-COMPLETION-EMBEDDING-TOPOLOGY` | `JoshiTeich.Act1Scene1.FiniteCompletionEmbeddingTopology.isClosedEmbedding`, `JoshiTeich.Act1Scene1.FiniteCompletionEmbeddingTopology.continuous`；`Act1Scene1/FiniteCompletionEmbeddingTopology.lean` | Mathlib injective finite-dimensional linear map 的 closed-embedding 判据；既有 actual finite p-adic completion algebra、continuous_padicEmb 和 embedCompletion_padicEmb。对原 finite-completion embedding，若给定 base completion→Ω map 连续，则将原 source 和 Ω 装配为同一 ℚ_p 上的拓扑向量空间；原 embedding 与 base map 的交换给出线性，实际 source 的有限维性及单射性推出 closed topological embedding 和连续性。并未假定 raw completion 范数等距或预置拓扑嵌入证书。 原创消费者证明，无参考工程代码复制。 | Scene1/Derived；proved / accepted |
| `JT-SCENE1-INITIAL-THETA-TORSION-UNTILT-TOPOLOGY` | `JoshiTeich.Act1Scene1.InitialThetaTorsionUntiltTopology.embedding_isClosedEmbedding`, `JoshiTeich.Act1Scene1.InitialThetaTorsionUntiltTopology.embedding_continuous`, `JoshiTeich.Act1Scene1.InitialThetaTorsionUntiltTopology.embedding_range_isClosed`, `JoshiTeich.Act1Scene1.InitialThetaTorsionUntiltTopology.embedding_norm_lt_one_iff`, `JoshiTeich.Act1Scene1.InitialThetaTorsionUntiltTopology.embedding_norm_pow`, `JoshiTeich.Act1Scene1.InitialThetaTorsionUntiltTopology.embedding_dist_pow`, `JoshiTeich.Act1Scene1.InitialThetaTorsionUntiltTopology.embedding_log_norm`；`Act1Scene1/IutInitialThetaTorsionUntiltTopology.lean` | Joshi local untilt embeddings、III relative-degree normalization；前轮同一 D／w／v|w 的原 torsion-completion→Ω embedding、原 completion 范数幂公式。对同一实际嵌入，base completionEmbedding 的既有等距性提供连续性生产者，推出实际 embedding 为 closed topological embedding、连续且像闭。以原 TateParameterData.parameter 经 iutEmbedCompletion 的像为非零收缩校准值，前轮交换图与 actual norm_eq_pow 给精确指数 d=iutRelativeRamificationIndex·relInertDeg；于是任意原 torsion completion 元素 x 均满足 raw norm(x)=norm(embedding x)^d，任意两点的距离满足相同幂关系，对数亦带 d，且 contraction threshold 精确保留。actual 输入仅既有 D／w／v 与原 places-over 关系，无新增连续性／范数／isometry 证书。 原创消费者证明，无参考工程代码复制。 | Scene1/Derived；proved / accepted |

这里保留原 torsion completion 的 raw norm 和同一 Ω 范数，得到全域精确幂关系而未将两者直接视为等距。该比较服务于 actual q-root／Teichmüller source adapter；不同 holomorphoid／Ansatz 的来源身份、论文 theta-values／theta locus、Tate module、B 的 Fréchet／ρ-norm、adelic collation 和完整 3.12 仍开放。Prologue-R5／Core、旧声明及冻结依赖不变，无新增数学前提或许可证增量；无动态边界修订或数学负面证据，不追加 log5。

验收：最终绝对值比较叶、有限 completion 闭嵌入叶、actual 拓扑叶、`Checks.SceneBounds`、`Axioms.SceneBounds` 与 `Act1Scene1` 全部退出 0，耗时依次为 56.383、71.481、117.071、136.915、128.311、122.719 秒；进程组峰值 RSS 依次为 4,349,860、5,460,460、9,234,484、9,428,412、9,411,648、9,238,796 KiB。三叶及汇总最终日志均为空，两项审计无 warning／error；12 个新增公开声明逐名核对，2906 个公理条目全部只含 `propext`、`Classical.choice`、`Quot.sound`，无 `sorryAx`。actual closed-embedding／all-element norm-power／distance-power 关键签名只接收既有 D／w／v、原 places-over 关系及被测元素，没有外给连续性或范数证书；静态导入审计覆盖 534 个可达工程模块，无 Obligations、Candidate、Scene2、Act2 或 `Iut.*` 导入。

编辑期记录：绝对值比较叶首检退出 1（59.383 秒，4,356,844 KiB），所引 NormedField.toAbsoluteValue 未在窄导入中暴露，改用已定义 pullback 在 RingHom.id 上表示原 norm，并将校准式的自然数幂改写方向改为实幂；第二次首次无警告通过（56.383 秒，4,349,860 KiB）。有限 completion 拓扑叶首检退出 1（71.475 秒，5,466,288 KiB），closed-embedding 结论未显式提及 hι，Lean 自动省略该 section 参数；include hι 保留实际使用的连续性前提，并将三条 letI 风格提示清理为 let；第二次无警告通过（71.481 秒，5,460,460 KiB）。actual 拓扑叶首次即无警告通过（117.071 秒，9,234,484 KiB）。失败均为 Lean API／section 参数及改写适配，数学对象和前提不变，无 heartbeat 或内存失败。

本轮共 8 次直接 Lean 任务（6 成功、2 失败），成功累计 632.880 秒、失败累计 130.858 秒、总计 763.738 秒；进程组峰值 RSS 9,428,412 KiB（8.992 GiB）。全部使用 CPU affinity `0–13`、`LEAN_NUM_THREADS=10`、Lean `-j1`，实际并发 worker 峰值 1；每 0.5 秒采样进程组 RSS，85 GiB 停止线未触发（用户上限 90 GiB）。无 heartbeat override。只用 `lake env lean -j1 -o` 访问现有依赖产物，未调用 Lake build 调度器、冷构建、重编 Mathlib 或变更冻结工具链／依赖。


### de Rham pilot 求值到原 torsion completion 与实际 tensor witness

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-EMBEDDED-RESIDUE-PULLBACK` | `JoshiTeich.Act1Scene1.EmbeddedResiduePullback.source`, `JoshiTeich.Act1Scene1.EmbeddedResiduePullback.rangeEquiv`, `JoshiTeich.Act1Scene1.EmbeddedResiduePullback.evaluation`, `JoshiTeich.Act1Scene1.EmbeddedResiduePullback.embedding_evaluation`, `JoshiTeich.Act1Scene1.EmbeddedResiduePullback.evaluation_eq_iff`, `JoshiTeich.Act1Scene1.EmbeddedResiduePullback.surjective`, `JoshiTeich.Act1Scene1.EmbeddedResiduePullback.kernel`, `JoshiTeich.Act1Scene1.EmbeddedResiduePullback.fiber`, `JoshiTeich.Act1Scene1.EmbeddedResiduePullback.quotientEquiv`, `JoshiTeich.Act1Scene1.EmbeddedResiduePullback.quotientEquiv_mk`；`Act1Scene1/EmbeddedResiduePullback.lean` | Joshi II eta_K／local Teichmüller evaluation（932–958）；Mathlib subring comap、ring-hom range 和 quotient-kernel。对 θ:A→Ω 和 field embedding ι:E→Ω，构造 source=θ⁻¹(range ι) 的实际子环及其到 E 的 evaluation，证明 ι∘evaluation=θ、求值判据；θ 满射时 evaluation 满射，核精确为原 kerθ 在 source 中的 comap，fiber 当且仅当原环中的差属于 kerθ，给 source/ker(evaluation)≃E 及商求值。没有为求值映射另加来源、满射或核证书。 原创消费者证明，无参考工程代码复制。 | Scene1/Derived；proved / accepted |
| `JT-SCENE1-INITIAL-THETA-TORSION-DE-RHAM-EVALUATION` | `JoshiTeich.Act1Scene1.InitialThetaTorsionDeRhamEvaluation.source`, `JoshiTeich.Act1Scene1.InitialThetaTorsionDeRhamEvaluation.evaluation`, `JoshiTeich.Act1Scene1.InitialThetaTorsionDeRhamEvaluation.embedding_evaluation`, `JoshiTeich.Act1Scene1.InitialThetaTorsionDeRhamEvaluation.evaluation_surjective`, `JoshiTeich.Act1Scene1.InitialThetaTorsionDeRhamEvaluation.kernel_eq_comap`, `JoshiTeich.Act1Scene1.InitialThetaTorsionDeRhamEvaluation.quotientEquiv`, `JoshiTeich.Act1Scene1.InitialThetaTorsionDeRhamEvaluation.pilot`, `JoshiTeich.Act1Scene1.InitialThetaTorsionDeRhamEvaluation.evaluation_pilot`, `JoshiTeich.Act1Scene1.InitialThetaTorsionDeRhamEvaluation.evaluation_pilot_vbad`, `JoshiTeich.Act1Scene1.InitialThetaTorsionDeRhamEvaluation.pilot_fiber`, `JoshiTeich.Act1Scene1.InitialThetaTorsionDeRhamEvaluation.evaluation_pilot_norm`, `JoshiTeich.Act1Scene1.InitialThetaTorsionDeRhamEvaluation.tensorPilot`, `JoshiTeich.Act1Scene1.InitialThetaTorsionDeRhamEvaluation.tensorPilot_eq_scaleElt`, `JoshiTeich.Act1Scene1.InitialThetaTorsionDeRhamEvaluation.tensorPilot_mem_region`；`Act1Scene1/IutInitialThetaTorsionDeRhamEvaluation.lean` | Joshi II eta_K／Teichmüller lift／local pilot（932–1013）；reference `ThetaRegion.scaleElt`／`thetaFinite`；Joshi III local source 与 hull。对同一 D／w／v|w，把原 BDeRhamPlus 的 θ 限制到残值位于原 torsion completion 嵌入像的实际子环，构造到该原 completion 的满射 ring hom、原 Ω 中交换公式、精确 kernel-comap 和商环等价。既有 actual torsion pilot 的残值就是原 qrootAt^(j²) 的像，故在该 source 中构造原 pilot 元素并证明 evaluation(pilot)=原 qrootAt^(j²)=vbadQrootAt^(j²)，其 norm 精确为原 raw qroot norm^(j²)，fiber 恰为原 primitive·b+pilot。对任意实际 Packet、指定 d 及该因子的实际 places-over 关系，将该真实求值送入 singleAlgHom，证明 tensorPilot 精确等于已有 finite factor region 的 scaleElt，并因此位于原实际 region；不重新定义或改动旧区域。actual 输入仍仅 D／w／v|w、实际 Packet 与指定因子的 places-over 关系，无外给 θ求值／区域包含证书。 原创消费者证明，无参考工程代码复制。 | Scene1/Derived；proved / accepted |

这里关闭一个实际 period lift 到旧 completion container 的精确单点来源连接，没有把整套 θ-fiber 或整个 B_dR⁺ 当成论文 locus，也没有声称容器包含全部论文 Ind1–Ind3。full paper theta locus、Tate module／B^{φ=p}、Fréchet B／ρ-norm、跨 holomorphoid collation、paper volume 身份和最终 3.12 仍开放。Prologue-R5／Core、旧声明及冻结依赖不变，无新增数学前提或许可证增量；无动态边界修订或数学负面证据，不追加 log5。

验收：最终通用 pullback 叶、实际求值叶、`Checks.SceneBounds`、`Axioms.SceneBounds` 与 `Act1Scene1` 全部退出 0，耗时依次为 59.379、130.859、153.749、129.793、126.262 秒；进程组峰值 RSS 依次为 3,648,284、9,247,016、9,432,600、9,414,216、9,268,552 KiB。两叶及汇总最终日志均为空，两项审计无 warning／error；24 个新增公开声明逐名核对，2930 个公理条目全部只含 `propext`、`Classical.choice`、`Quot.sound`，无 `sorryAx`。actual evaluation-pilot／fiber／tensor-scaleElt／region-membership 签名只接收既有 D／w／v、places-over、原 Packet／指定因子及指数，没有外给求值或包含关系证书；静态导入审计覆盖 536 个可达工程模块，无 Obligations、Candidate、Scene2、Act2 或 `Iut.*` 导入。

编辑期记录：通用叶首检退出 1（51.264 秒，3,653,104 KiB），ring-hom 结构的 map_mul／map_add 需要把 source 子类型参数显式强制到原 A；同时清理 rangeEquiv 的两个变量名提示，第二次无警告通过（59.379 秒，3,648,284 KiB）。实际叶首检退出 1（118.009 秒，9,245,388 KiB），fiber 改写未穿过 actual evaluation wrapper，改为原嵌入单射和已证 θ 交换／主核等式；singleAlgHom 需要 scoped Classical，处身份依赖运输改为显式处理。第二次退出 1（129.250 秒，9,246,404 KiB），仅剩等式运输的 Eq.ndrec 挡住 tensor 求值改写；新 tensor 接口直接消费指定因子 P.place d 的 places-over，去除冗余 v／处等式运输。第三次退出 0（141.114 秒，9,248,356 KiB），一条未用 Fintype section 提示用 omit 清理，空日志 gate 阻止带提示版本进入收尾审计；第四次无警告通过（130.859 秒，9,247,016 KiB）。失败均为 Lean 强制转换／封装／依赖类型适配，数学对象和前提不变，无 heartbeat 或内存失败。

本轮共 9 次直接 Lean 任务（6 次退出 0，其中 1 次编辑期有提示不作最终验收；3 次失败），退出 0 累计 741.156 秒、失败累计 298.523 秒、总计 1039.679 秒；进程组峰值 RSS 9,432,600 KiB（8.996 GiB）。全部使用 CPU affinity `0–13`、`LEAN_NUM_THREADS=10`、Lean `-j1`，实际并发 worker 峰值 1；每 0.5 秒采样进程组 RSS，85 GiB 停止线未触发（用户上限 90 GiB）。无 heartbeat override。只用 `lake env lean -j1 -o` 访问现有依赖产物，未调用 Lake build 调度器、冷构建、重编 Mathlib 或变更冻结工具链／依赖。

### Actual de Rham theta-fiber image and normalization hull

| source-id | 声明／文件 | 来源与忠实度 | 状态 |
| --- | --- | --- | --- |
| `JT-SCENE1-INITIAL-THETA-DE-RHAM-FIBER-HULL` | `JoshiTeich.Act1Scene1.InitialThetaDeRhamFiberHull.fiber`, `JoshiTeich.Act1Scene1.InitialThetaDeRhamFiberHull.mem_fiber_iff`, `JoshiTeich.Act1Scene1.InitialThetaDeRhamFiberHull.pilot_mem_fiber`, `JoshiTeich.Act1Scene1.InitialThetaDeRhamFiberHull.fiber_nonempty`, `JoshiTeich.Act1Scene1.InitialThetaDeRhamFiberHull.fiber_eq_kernel_translate`, `JoshiTeich.Act1Scene1.InitialThetaDeRhamFiberHull.evaluation_image_fiber`, `JoshiTeich.Act1Scene1.InitialThetaDeRhamFiberHull.tensorEvaluation`, `JoshiTeich.Act1Scene1.InitialThetaDeRhamFiberHull.tensorImage`, `JoshiTeich.Act1Scene1.InitialThetaDeRhamFiberHull.tensorImage_eq_singleton`, `JoshiTeich.Act1Scene1.InitialThetaDeRhamFiberHull.orbit`, `JoshiTeich.Act1Scene1.InitialThetaDeRhamFiberHull.orbit_eq_existing`, `JoshiTeich.Act1Scene1.InitialThetaDeRhamFiberHull.orbit_finite`, `JoshiTeich.Act1Scene1.InitialThetaDeRhamFiberHull.orbit_haar_eq_zero`, `JoshiTeich.Act1Scene1.InitialThetaDeRhamFiberHull.orbit_subset_region`, `JoshiTeich.Act1Scene1.InitialThetaDeRhamFiberHull.hull`, `JoshiTeich.Act1Scene1.InitialThetaDeRhamFiberHull.hull_eq_existing`, `JoshiTeich.Act1Scene1.InitialThetaDeRhamFiberHull.hull_isCompact`, `JoshiTeich.Act1Scene1.InitialThetaDeRhamFiberHull.hull_haar_pos_lt_top`, `JoshiTeich.Act1Scene1.InitialThetaDeRhamFiberHull.region_subset_hull`, `JoshiTeich.Act1Scene1.InitialThetaDeRhamFiberHull.hull_le_principalRegion_iff`；`Act1Scene1/IutInitialThetaDeRhamFiberHull.lean` | Joshi II `pr:teichmuller-lift-A`（940–958）的 kernel-translate 求值思想及 local pilot（至 1013）；Joshi III principal hull／`pr:convexes-and-hulls`／standard-point witness（3568–3631）；reference `Concrete/ThetaRegion.lean` 的 `scaleElt`／`thetaFinite` 和 image→orbit→hull 次序。对同一实际 D／w／torsion place v∣w，用原 B_dR⁺ 的 θ 和前轮残值子环定义完整 fiber，证明非空、原 primitive·b+pilot 表示、求值像为原 qrootAt^(j²) 单点。指定 tensor 因子下像精确为旧 scaleElt 单点；factor 轨道等于旧点轨道，有限且 Haar 为零，并包含于旧 region。该轨道的 normalization hull 等于原 leastHull，紧且 Haar 正有限，包含原 thickened region，落入任意 principalRegion 当且仅当轨道已落入。原创组合证明，无参考源码复制。 | Scene1/Derived；proved |

忠实度限制：完整 B_dR⁺ 主核 fiber 未识别为论文 B^{φ=p} 的 Tate-module translate；有限 completion-factor 自同构族未识别为全部 Ind1–Ind3。上述 hull 身份连接真实 period 求值来源与旧局部 container，不证明整个论文 theta locus、跨 holomorphoid collation、H¹ₑ/BK、Fréchet／ρ-norm、paper volume 或最终 3.12。所有输入仍为原 D、处关系及实际 Packet；无外给 fiber／轨道／包含／体积证书，无新增 Core 前提，Prologue-R5 与原公开声明不变，无许可证增量。

验收资源与尝试（2026-10-19）：叶首检 attempt1 退出 1，124.209 秒，进程组峰值 9,268,196 KiB；`singleAlgHom` 的因子族类型推断失败，非 heartbeat／内存失败。修正为显式 `(R := ℚ_[p])` 与 `(A := fun i => P.Factor i)` 后 attempt2 退出 0，121.864 秒，9,268,544 KiB，但有未使用 `Fintype` section 提示，未进入最终验收。加入 `omit [Fintype ι]` 后 attempt3 退出 0，119.498 秒，9,268,328 KiB，日志为空。收尾 `Checks.SceneBounds` 退出 0，135.888 秒，9,434,856 KiB；`Axioms.SceneBounds` 退出 0，124.654 秒，9,416,580 KiB；`Act1Scene1` 聚合退出 0，119.569 秒，9,269,460 KiB。所有任务使用 CPU affinity 0–13、`LEAN_NUM_THREADS=10`、Lean `-j1`，每 0.5 秒采样进程组 RSS，85 GiB 停止线未触发；无 heartbeat override、无冷构建、未重编译 Mathlib。直接 Lean 任务共 6 次，成功 5 次、失败 1 次；成功累计 621.473 秒，失败累计 124.209 秒，总计 745.682 秒；本轮最大进程组峰值 9,434,856 KiB。最终叶和聚合日志为空；20 个新增声明逐名核对，公理审计共 2950 条，仅含 `propext`、`Classical.choice`、`Quot.sound`，无 `sorryAx`；静态导入审计覆盖 537 个可达模块，无禁用导入。

### Marked Krull Galois transport on original continuous H¹

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-CONTINUOUS-H1-MARKED-TRANSPORT` | `JoshiTeich.Act1Scene1.ContinuousH1Transport.Marking`, `JoshiTeich.Act1Scene1.ContinuousH1Transport.Marking.symm`, `JoshiTeich.Act1Scene1.ContinuousH1Transport.Marking.coefficientHom`, `JoshiTeich.Act1Scene1.ContinuousH1Transport.Marking.cochain`, `JoshiTeich.Act1Scene1.ContinuousH1Transport.Marking.cochain_law`, `JoshiTeich.Act1Scene1.ContinuousH1Transport.Marking.map`, `JoshiTeich.Act1Scene1.ContinuousH1Transport.Marking.map_classOf`, `JoshiTeich.Act1Scene1.ContinuousH1Transport.Marking.symm_map_map`, `JoshiTeich.Act1Scene1.ContinuousH1Transport.Marking.map_symm_map`, `JoshiTeich.Act1Scene1.ContinuousH1Transport.Marking.h1Equiv`, `JoshiTeich.Act1Scene1.ContinuousH1Transport.Marking.h1Equiv_classOf`, `JoshiTeich.Act1Scene1.ContinuousH1Transport.Marking.groupIso`, `JoshiTeich.Act1Scene1.ContinuousH1Transport.Marking.coefficientIso`, `JoshiTeich.Act1Scene1.ContinuousH1Transport.Marking.equivariant`；`Act1Scene1/ContinuousH1Transport.lean` | Joshi I `pr:galois-cohomology-and-teich`（1609–1632）与 `cor:collation-classes`（1636–1643）；II½ `pr:arith-isom-gal-cohom`（1585–1602）；冻结 Mathlib `ContCohomology.Functoriality`。给定拓扑群同构 H≃G 和等变连续线性系数同构 X≃Y，使用原 homogeneous cochain complex 的实际 functoriality map，证明 crossed cocycle 的精确 precompose／postcompose 公式和双向逆，产生原标准连续 H¹ 的连续线性同构。两侧拓扑、系数模和 H¹ 都是原对象，没有经坐标重定义。 原创消费者证明，无参考工程源码复制。 | Scene1/Derived；proved，group/twist marking 显式 |
| `JT-SCENE1-LOCAL-KUMMER-MARKED-TRANSPORT` | `JoshiTeich.Act1Scene1.LocalKummer.MarkedTransport.Marking`, `JoshiTeich.Act1Scene1.LocalKummer.MarkedTransport.Marking.coefficientIso`, `JoshiTeich.Act1Scene1.LocalKummer.MarkedTransport.Marking.coefficientIso_coordinate`, `JoshiTeich.Act1Scene1.LocalKummer.MarkedTransport.Marking.coefficientIso_equivariant`, `JoshiTeich.Act1Scene1.LocalKummer.MarkedTransport.Marking.integralMarking`, `JoshiTeich.Act1Scene1.LocalKummer.MarkedTransport.Marking.rationalMarking`, `JoshiTeich.Act1Scene1.LocalKummer.MarkedTransport.Marking.integralH1`, `JoshiTeich.Act1Scene1.LocalKummer.MarkedTransport.Marking.rationalH1`, `JoshiTeich.Act1Scene1.LocalKummer.MarkedTransport.Marking.coefficient_change`, `JoshiTeich.Act1Scene1.LocalKummer.MarkedTransport.Marking.rationalH1_standardMap`, `JoshiTeich.Act1Scene1.LocalKummer.MarkedTransport.Marking.cocycle`, `JoshiTeich.Act1Scene1.LocalKummer.MarkedTransport.Marking.integralH1_classOfCocycle`, `JoshiTeich.Act1Scene1.LocalKummer.MarkedTransport.Marking.rationalH1_classOfCocycle`, `JoshiTeich.Act1Scene1.LocalKummer.MarkedTransport.rationalCollation`, `JoshiTeich.Act1Scene1.LocalKummer.MarkedTransport.mem_rationalCollation_iff`, `JoshiTeich.Act1Scene1.LocalKummer.MarkedTransport.integralCollation`, `JoshiTeich.Act1Scene1.LocalKummer.MarkedTransport.rationalization_collation`, `JoshiTeich.Act1Scene1.LocalKummer.MarkedTransport.Marking.groupIso`, `JoshiTeich.Act1Scene1.LocalKummer.MarkedTransport.Marking.character_eq`；`Act1Scene1/LocalKummerMarkedTransport.lean` | Joshi I 同上；II½ `pr:arith-isom-gal-cohom`／`pr:collation-principle`（1585–1625）。两套原域和代数闭 integral 扩张给实际 Krull Galois 群、原 Tate 逆极限、原 cyclotomic characters。显式 group marking 要求拓扑群同构保持该 character；由原 Tate bases 生产 integral coefficient equivalence，rational 系数沿原 lifted ℚₚ(1) 表示运输。证明 integral/rational 标准连续 H¹ 的连续线性同构、standardMap 交换图、原 transported Tate cocycle 及其两种 class 公式。对全部这些基所确定的标注取像并集，给 integral/rational collation，并证明 coefficient-change 与 collation 交换。 原创消费者证明，无参考工程源码复制。 | Scene1/Derived；proved，group/twist marking 显式 |

来源边界：这是原 ambient continuous H¹ 的跨群、跨实际 Tate 系数运输，未用任意 H¹ 等价冒充来源映射；Marking 并未从 holomorphoid／anabelomorphism／arithmeticoid 自动产生。actual 系数比较使用原固定 Tate bases，只覆盖这些标注产生的映射；完整论文 collation 的标注生产者、全部 coefficient 选择、H¹ₑ／H¹_f／H¹_g amphoricity、BK／log 兼容、论文 theta locus 和最终 3.12 仍开放。运输 cocycle 的定理不声称它等于另一域指定元素的 Kummer cocycle。未新增 Core 前提或修改 Prologue-R5／既有声明，无许可证增量；无动态边界变更或数学负面证据，不追加 log5。

验收与编辑期全部尝试：

| 任务 | 退出码 | 耗时（秒） | 进程组峰值 RSS（KiB） |
| --- | ---: | ---: | ---: |
| `scene1-marked-cohomology-generic-attempt1.jsonl` | 1 | 56.284 | 4,392,280 |
| `scene1-marked-cohomology-generic-attempt2.jsonl` | 1 | 60.122 | 4,395,328 |
| `scene1-marked-cohomology-generic-attempt3.jsonl` | 0 | 60.171 | 4,398,800 |
| `scene1-marked-cohomology-actual-attempt1.jsonl` | 1 | 66.736 | 5,155,960 |
| `scene1-marked-cohomology-actual-attempt2.jsonl` | 1 | 67.311 | 5,155,768 |
| `scene1-marked-cohomology-actual-attempt3.jsonl` | 0 | 68.765 | 5,155,644 |
| `scene1-marked-cohomology-aggregate-metrics.jsonl` | 0 | 148.722 | 9,271,368 |
| `scene1-marked-cohomology-axioms-metrics.jsonl` | 0 | 124.385 | 9,420,932 |
| `scene1-marked-cohomology-checks-metrics.jsonl` | 0 | 130.025 | 9,439,696 |

通用叶 attempt1 因冻结版 ContinuousMulEquiv 不提供投影式 toContinuousMonoidHom 名称而失败，改用 ContinuousMonoidHom.toContinuousMonoidHom；清除 cochain_law 不使用的拓扑群 section 参数。attempt2 两个 inverse 证明中的 congr 已关掉目标，删除其后多余 exact，attempt3 无警告通过。实际 Tate 叶 attempt1 的 coefficient_change 在 TopRep wrapper 下改写失败，改为对原系数等式作 congrArg；存在量词括号语法同轮报错，attempt2 仍有未补类型的 binder 语法，最终改为明确的 `∃ m, ∃ x ∈ S, ...` 后 attempt3 无警告通过。四次失败均为 Lean API／类型封装／语法／冗余 tactic 适配；数学目标及前提不变，无 heartbeat 或内存失败，失败诊断生成的 sorry 从未作为验收。

本轮共 9 次直接 Lean 任务（5 成功、4 失败），成功累计 532.068 秒，失败累计 250.453 秒，总计 782.521 秒；进程组峰值 RSS 9,439,696 KiB。最终两叶及聚合日志为空，两审计入口无 warning／error；33 个新增公开名称（含显式结构字段）逐名审计，整个 SceneBounds 公理日志共 2983 条，仅含 propext、Classical.choice、Quot.sound，无 sorryAx。静态导入边界覆盖 539 个可达工程模块，无 Obligations、Candidate、Scene2、Act2 或 Iut.*。所有任务固定 CPU affinity 0–13、LEAN_NUM_THREADS=10、Lean -j1，实际并发 worker 峰值 1，每 0.5 秒采样进程组 RSS，85 GiB 停止线未触发（用户上限 90 GiB）。无 heartbeat override；只使用既有预编译依赖，未运行 Lake build 调度器、冷构建、清缓存或重编 Mathlib。Lean v4.35.0-rc3 与 Mathlib 389347a7c1cfa76f6bd5be2ca35d4cb621610ad3 已核对。

### Preferred algebraic-closure Galois and Kummer transport

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-GALOIS-CLOSURE-TRANSPORT` | `JoshiTeich.Act1Scene1.GaloisClosureTransport.autCongr_continuous`, `JoshiTeich.Act1Scene1.GaloisClosureTransport.groupIso`, `JoshiTeich.Act1Scene1.GaloisClosureTransport.groupIso_apply`, `JoshiTeich.Act1Scene1.GaloisClosureTransport.intertwine`；`Act1Scene1/GaloisClosureTransport.lean` | Joshi I `ss:distinct-kummer-theories` 与 `pr:galois-cohomology-and-teich`（1588–1632）；Mathlib `KrullTopology` finite-intermediate-field neighborhoods and `AlgEquiv.autCongr`. 对同一底域 K 的两个代数闭扩张 Ω、Ξ，按 fixing subgroup 邻域证明 Galois 共轭的连续性，构造 preferred-closure Galois group 的连续群同构，并证明共轭对元素的交换。原创消费者证明，无参考源码复制。 | Scene1/Derived；proved。只覆盖固定底域的 closure transport，不产生跨 anabelomorphism／holomorphoid 的来源标注。 |
| `JT-SCENE1-LOCAL-KUMMER-CLOSURE-TRANSPORT` | `JoshiTeich.Act1Scene1.LocalKummer.ClosureTransport.tateMap`, `JoshiTeich.Act1Scene1.LocalKummer.ClosureTransport.tateMap_apply`, `JoshiTeich.Act1Scene1.LocalKummer.ClosureTransport.tateMap_symm`, `JoshiTeich.Act1Scene1.LocalKummer.ClosureTransport.tateMap_padicPower`, `JoshiTeich.Act1Scene1.LocalKummer.ClosureTransport.tateMap_continuous`, `JoshiTeich.Act1Scene1.LocalKummer.ClosureTransport.tateEquiv`, `JoshiTeich.Act1Scene1.LocalKummer.ClosureTransport.tateEquiv_equivariant`, `JoshiTeich.Act1Scene1.LocalKummer.ClosureTransport.marking`, `JoshiTeich.Act1Scene1.LocalKummer.ClosureTransport.h1Equiv`, `JoshiTeich.Act1Scene1.LocalKummer.ClosureTransport.mapRootTower`, `JoshiTeich.Act1Scene1.LocalKummer.ClosureTransport.mapRootTower_cocycle`, `JoshiTeich.Act1Scene1.LocalKummer.ClosureTransport.h1Equiv_rootTower`, `JoshiTeich.Act1Scene1.LocalKummer.ClosureTransport.h1Equiv_kummerClass`；`Act1Scene1/LocalKummerClosureTransport.lean` | Joshi I 同上；Joshi III compatible-root Kummer construction（3190–3208）；原 `LocalKummer` Tate basis、continuous H¹ 和 root-tower choice-independence。逐坐标运输 roots-of-unity inverse limit，证明连续、ℤₚ 线性、Galois 等变；任意 root tower 沿 K-代数同构运输，Kummer cocycle 与目标独立选取的 root tower 给出同一原 integral H¹ class。原创消费者证明，无参考源码复制。 | Scene1/Derived；proved。未声称 H¹ₑ/BK、log comparison、跨 holomorphoid collation 或 paper theta locus 身份。 |

来源边界：这两个叶把上一单元的显式 marking 推进到同一底域的 preferred algebraic closures，并消除 root-tower 选择依赖；它们没有构造 Joshi 论文所需的 admissible holomorphoid／arithmeticoid 标注生产者，也没有把 ambient H¹ 自动识别为 H¹ₑ/BK。Prologue-R5、Core 和许可证不变，无动态边界修订或数学负面证据，不追加 log5。

验收资源与尝试（2026-10-19）：Galois closure 叶 attempt1 失败 70.774 秒、4,233,672 KiB（`finiteDimensional_map` 类型适配）；attempt2 失败 55.611 秒、4,188,896 KiB（fixing-subgroup 改写未命中）；attempt3 失败 52.038 秒、4,211,068 KiB（同一成员命题的 `change` 仍被 coercion 阻挡）；改为显式 `.mpr` 后 attempt4 通过，56.110 秒、4,224,576 KiB，日志为空。Kummer closure 叶 attempt1 退出 1，58.140 秒、4,922,580 KiB（未保留 integral section 实例及三条 unused-instance 提示）；attempt2 退出 0，59.137 秒、4,920,236 KiB，但仍有一个 unused section 参数提示；加入 `omit` 后 attempt3 退出 0，60.120 秒、4,920,660 KiB，日志为空。`Checks.SceneBounds` 通过，122.701 秒、9,440,944 KiB；`Axioms.SceneBounds` 通过，115.152 秒、9,423,304 KiB；`Act1Scene1` 聚合通过，114.700 秒、9,272,140 KiB。共 10 次直接 Lean 任务，6 次成功、4 次失败；成功累计 527.920 秒，失败累计 236.563 秒，总计 764.483 秒；峰值 RSS 9,440,944 KiB。全部 CPU affinity 0–13、`LEAN_NUM_THREADS=10`、Lean `-j1`，实际 worker 峰值 1，每 0.5 秒采样，未触及 85 GiB 停止线；无 heartbeat timeout 或 override，未冷构建、未重编译 Mathlib。最终两叶及聚合日志为空，审计无 warning/error；17 个新增公开名称逐名核对，公理日志共 3000 条，仅含 `propext`、`Classical.choice`、`Quot.sound`，无 `sorryAx`；静态导入审计覆盖 541 个可达工程模块，无禁用导入。

### Rational preferred-closure Kummer transport with the actual Tate basis unit

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-LOCAL-KUMMER-RATIONAL-CLOSURE-TRANSPORT` | `JoshiTeich.Act1Scene1.LocalKummer.RationalClosureTransport.coordinateEquiv`, `JoshiTeich.Act1Scene1.LocalKummer.RationalClosureTransport.basisScalar`, `JoshiTeich.Act1Scene1.LocalKummer.RationalClosureTransport.coordinateEquiv_apply`, `JoshiTeich.Act1Scene1.LocalKummer.RationalClosureTransport.coordinate_tateEquiv`, `JoshiTeich.Act1Scene1.LocalKummer.RationalClosureTransport.basisScalar_mul_inverse`, `JoshiTeich.Act1Scene1.LocalKummer.RationalClosureTransport.basisUnit`, `JoshiTeich.Act1Scene1.LocalKummer.RationalClosureTransport.basisUnit_val`, `JoshiTeich.Act1Scene1.LocalKummer.RationalClosureTransport.character_eq`, `JoshiTeich.Act1Scene1.LocalKummer.RationalClosureTransport.coefficientEquiv`, `JoshiTeich.Act1Scene1.LocalKummer.RationalClosureTransport.coefficientEquiv_down`, `JoshiTeich.Act1Scene1.LocalKummer.RationalClosureTransport.coefficientEquiv_equivariant`, `JoshiTeich.Act1Scene1.LocalKummer.RationalClosureTransport.marking`, `JoshiTeich.Act1Scene1.LocalKummer.RationalClosureTransport.h1Equiv`, `JoshiTeich.Act1Scene1.LocalKummer.RationalClosureTransport.coefficient_change`, `JoshiTeich.Act1Scene1.LocalKummer.RationalClosureTransport.h1Equiv_standardMap`, `JoshiTeich.Act1Scene1.LocalKummer.RationalClosureTransport.h1Equiv_rootTower`, `JoshiTeich.Act1Scene1.LocalKummer.RationalClosureTransport.h1Equiv_kummerClass`；`Act1Scene1/LocalKummerRationalClosureTransport.lean` | Joshi I `ss:distinct-kummer-theories`／`pr:galois-cohomology-and-teich`（1588–1632），III integral/rational compatible-root Kummer classes（3190–3236）；原 preferred-closure Tate transport、原 Tate bases 和 standardMap。将原自然 Tate 同构写到两侧独立选取的 ℤₚ 基坐标中，证明得到的线性自同构是乘 basisScalar，反向坐标给出实际逆元，因此 basisScalar 是单位。自然 Tate 同构的等变性及该单位可消去性给原 cyclotomic characters 的精确共轭等式。rational 系数以同一单位乘原 ULift ℚₚ carrier，证明等变，构造原 rational H¹ 的连续线性同构；standardMap 与原 integral H¹ transport 的交换图、任意实际 root tower class 和目标独立选取根塔 class 的同一底域元素身份均有完整 proof term。原创消费者证明，无参考代码复制。 | Scene1/Derived；proved，K-代数 closure 同构显式 |

此单位由实际自然 Tate transport 决定，不假设等于 1。结果没有用前轮基坐标恒等的 marking 代替自然系数映射；也没有假设 cyclotomic character identity、系数比较或 H¹ equivalence 证书。仍限于一个固定底域 K 的两个代数闭 integral 扩张和显式 K-代数同构；不同 holomorphoid／anabelomorphism 的生产者、H¹ₑ/BK／log 比较、论文 collation／theta locus 和最终 3.12 仍开放。Prologue-R5／Core 和旧公开声明未变，无许可证增量；无动态边界变更或数学负面证据，不追加 log5。

验收与全部 Lean 尝试（2026-10-19）：

| 任务 | 退出码 | 耗时（秒） | 进程组峰值 RSS（KiB） |
| --- | ---: | ---: | ---: |
| `scene1-rational-closure-attempt1.jsonl` | 1 | 60.077 | 5,153,656 |
| `scene1-rational-closure-attempt2.jsonl` | 0 | 60.595 | 5,147,012 |
| `scene1-rational-closure-checks-metrics.jsonl` | 0 | 121.195 | 9,442,524 |
| `scene1-rational-closure-axioms-metrics.jsonl` | 0 | 114.320 | 9,425,332 |
| `scene1-rational-closure-aggregate-metrics.jsonl` | 0 | 114.647 | 9,272,600 |

首检退出 1：coordinateEquiv_apply 的 simp 需显式展开 basisScalar；Units.map 需要传 RingHom 的 toMonoidHom，后续错误均为该定义失败的级联。两处修正后叶第二次无警告通过，之后生产源码未修改；三个收尾入口均通过。失败为 Lean API／展开适配，无 heartbeat 超时，无数学目标或前提变动。

本轮共 5 次直接 Lean 任务（4 成功、1 失败），成功累计 410.757 秒，失败累计 60.077 秒，总计 470.834 秒；进程组峰值 RSS 9,442,524 KiB。最终新叶和聚合日志为空，两审计入口无 warning/error；17 个新增声明逐名核对，公理日志 3017 条仅含 `propext`、`Classical.choice`、`Quot.sound`，无 `sorryAx`；静态导入审计覆盖 542 个可达工程模块，无 Obligations、Candidate、Scene2、Act2 或 Iut.* 导入。固定 CPU 0–13、LEAN_NUM_THREADS=10、Lean -j1，实际并发 worker 峰值 1；每 0.5 秒采样组 RSS，85 GiB 停止线未触发（用户上限 90 GiB）。没有 heartbeat override、冷构建、清缓存、Mathlib 重编译或依赖变更；Lean v4.35.0-rc3 与 Mathlib 389347a7c1cfa76f6bd5be2ca35d4cb621610ad3 已核对。

本轮同时更正清单已证局部 normalization 子项的文字：paper factor 的负对数等于 qOrder·log(residueChar)/(2ℓ)，q-pilot normalizedLogTerm 再乘 qPilotWeight。原定理和来源台账公式不变；这不构成数学负面证据或边界修订。

### Preferred-closure principal Kummer image, saturation and ordinary logarithm

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-LOCAL-KUMMER-LOG-CLOSURE-TRANSPORT` | `JoshiTeich.Act1Scene1.LocalPadicLog.ClosureTransport.kummerHom`, `JoshiTeich.Act1Scene1.LocalPadicLog.ClosureTransport.principalKummerHom`, `JoshiTeich.Act1Scene1.LocalPadicLog.ClosureTransport.mem_principalImage_iff`, `JoshiTeich.Act1Scene1.LocalPadicLog.ClosureTransport.principalImageEquiv`, `JoshiTeich.Act1Scene1.LocalPadicLog.ClosureTransport.principalImageLog_eq`, `JoshiTeich.Act1Scene1.LocalPadicLog.ClosureTransport.mem_saturatedImage_iff`, `JoshiTeich.Act1Scene1.LocalPadicLog.ClosureTransport.saturatedEquiv`, `JoshiTeich.Act1Scene1.LocalPadicLog.ClosureTransport.saturatedEquiv_classOfImage`, `JoshiTeich.Act1Scene1.LocalPadicLog.ClosureTransport.saturatedImageLog_eq`, `JoshiTeich.Act1Scene1.LocalPadicLog.ClosureTransport.saturatedExp_eq`, `JoshiTeich.Act1Scene1.LocalPadicLog.ClosureTransport.integralLift_iff`, `JoshiTeich.Act1Scene1.LocalPadicLog.ClosureTransport.saturatedContinuousEquiv`, `JoshiTeich.Act1Scene1.LocalPadicLog.ClosureTransport.saturatedPadicLog_eq`；`Act1Scene1/LocalKummerLogClosureTransport.lean` | Joshi I `ss:distinct-kummer-theories`／`pr:galois-cohomology-and-teich`（1588–1632）；III principal-unit Kummer classes、ordinary-log／exp 的构造规格（3190–3236）；原 rational closure transport、principal image、p-saturation、integral standardMap 与 subspace topology。对同一完备离散赋值特征零底域 k 的两个代数闭 integral 扩张及显式 k-代数同构 e，限制原 rational continuous H¹ 同构，证明同一底域单位的 Kummer 类运输、principal image 成员充要条件及加法同构。利用清除 p 次幂分母证明原 p-saturation 的成员充要条件、divided-class 公式和加法同构；对素数 p 及显式 ‖(p:k)‖<1 证明 ordinary log／inverse exp 交换；由原 integral/rational standardMap 交换图证明任意 ambient rational 类的 integral-lift 存在性保持。原 H¹ 子空间拓扑上的 ℚₚ 连续线性限制及 saturatedPadicLog 兼容也有完整 proof term。原创证明，无参考源码复制。 | Scene1/Derived；proved，固定底域 closure 同构显式 |
| `JT-SCENE1-INITIAL-THETA-CLOSURE-LOG` | `JoshiTeich.Act1Scene1.PrincipalUnitKummer.ClosureLog.preferredEquiv`, `JoshiTeich.Act1Scene1.PrincipalUnitKummer.ClosureLog.imageClass`, `JoshiTeich.Act1Scene1.PrincipalUnitKummer.ClosureLog.imageClass_eq_kummer`, `JoshiTeich.Act1Scene1.PrincipalUnitKummer.ClosureLog.imageClass_log`, `JoshiTeich.Act1Scene1.PrincipalUnitKummer.ClosureLog.imageClass_normalizedLog`, `JoshiTeich.Act1Scene1.PrincipalUnitKummer.ClosureLog.dividedClass`, `JoshiTeich.Act1Scene1.PrincipalUnitKummer.ClosureLog.dividedClass_log`, `JoshiTeich.Act1Scene1.PrincipalUnitKummer.ClosureLog.dividedClass_ne_zero`；`Act1Scene1/IutInitialThetaClosureLog.lean` | Joshi I preferred algebraic closures 与 Kummer theories（1588–1632）；III 同一 principal unit `1+p*·qroot` 的根塔类及 normalized logarithmic witness（3190–3236）；原 actual rationalImageClass／normalizedSaturatedClass。对同一 D 的实际支持处 completion 和任意代数闭 integral 扩张 Ξ，用 IsAlgClosure.equiv 构造 preferred closure 比较；目标特征零由原域嵌入显式推出。原 principal-unit 类实际运输为目标闭包中同一单位的 Kummer 类，ordinary log 精确为 p*·PaperLogWitnessHull.value，除以 p* 恢复原 witness；原 divided saturated 类运输后的 ordinary log 精确为原 witness，因而非零。未外给 closure equivalence、group marking 或 log compatibility。原创证明，无参考源码复制。 | Scene1/Derived；proved，actual D／place 消费者 |

来源边界：这两个叶补齐固定底域 preferred-closure Kummer 运输的 principal-unit、saturation、ordinary-log 与 integral-lift 兼容，并消费同一实际 Initial Θ-data 的类。inverse exp 是已构造 saturated ordinary-log 的逆，不在本单元把它认作 Bloch–Kato 指数；同一 completion 的闭包比较不产生不同 holomorphoid／anabelomorphism 的标注，也不证明 H¹ₑ／BK／crystalline、跨非同构底域的 log 比较、完整论文 collation／theta locus／volume 或最终 3.12。完整来源父义务仍开放。无新增 Core 前提，Prologue-R5、旧公开声明与许可证不变；没有动态边界变更或数学负面证据，不追加 log5。

验收与全部直接 Lean 尝试（2026-10-19）：

| 任务 | 退出码 | 耗时（秒） | 进程组峰值 RSS（KiB） |
| --- | ---: | ---: | ---: |
| `scene1-log-closure-generic-attempt1.jsonl` | 1 | 61.159 | 5,234,724 |
| `scene1-log-closure-generic-attempt2.jsonl` | 0 | 62.633 | 5,235,964 |
| `scene1-log-closure-generic-attempt3.jsonl` | 0 | 65.191 | 5,237,588 |
| `scene1-log-closure-generic-attempt4.jsonl` | 0 | 65.735 | 5,236,520 |
| `scene1-log-closure-actual-attempt1.jsonl` | 1 | 129.373 | 9,218,660 |
| `scene1-log-closure-actual-attempt2.jsonl` | 0 | 126.336 | 9,263,620 |
| `scene1-log-closure-actual-attempt3.jsonl` | 1 | 116.169 | 9,220,544 |
| `scene1-log-closure-actual-attempt4.jsonl` | 0 | 125.746 | 9,263,064 |
| `scene1-log-closure-checks-metrics.jsonl` | 0 | 123.808 | 9,447,512 |
| `scene1-log-closure-axioms-metrics.jsonl` | 0 | 117.128 | 9,426,244 |
| `scene1-log-closure-aggregate-attempt1.jsonl` | 1 | 119.799 | 9,272,572 |
| `scene1-log-closure-aggregate-metrics.jsonl` | 0 | 117.803 | 9,248,488 |

通用叶 attempt1 因局部 notation 的投影写法、principal-image 底域参数推断及 saturated_as_divided_image 的参数适配失败；attempt2 证明通过但有两条 unused-section-variable warning；按依赖链清理后 attempt3 暴露下游 mem_principalImage_iff 的同类冗余参数，attempt4 日志为空。实际数据叶 attempt1 因目标 CharZero 实例的底域参数无法按目标类型推断而失败；改为各声明内显式导出特征零后 attempt2 通过，但有 class-valued def、defProp 和 letI 格式警告；attempt3 将辅助 def 改 theorem 时遗漏仅在证明体中的底域参数，导致类型错误；改为显式底域参数的私有辅助定理后 attempt4 无警告通过。聚合首检因两个新 import 位于末尾模块文档注释之后失败，将其移回 import 区后复验通过；叶与两审计源码未再改动，因此不重复其已通过检查。上述四次非零退出均为 Lean 类型／实例／语法适配，无 heartbeat 或数学前提变动，失败诊断中的占位证明从未作为验收。

共 12 次直接 Lean 任务（8 次退出 0、4 次失败；退出 0 中包含编辑期警告清理复验），成功累计 804.380 秒，失败累计 426.500 秒，总计 1230.880 秒；进程组峰值 RSS 9,447,512 KiB。最终两叶及聚合日志为空，Checks／Axioms 无 warning/error；21 个新增公开名称逐名核对，公理日志 3038 条只含 `propext`、`Classical.choice`、`Quot.sound`，无 `sorryAx`。静态导入边界覆盖 544 个可达工程模块，无 Obligations、Candidate、Scene2、Act2 或 Iut.*。全部任务固定 CPU affinity 0–13、`LEAN_NUM_THREADS=10`、Lean `-j1`，每个直接任务一个目标，实际并发 Lean worker 峰值 1；每 0.5 秒采样进程组 RSS，85 GiB 停止线未触发（用户上限 90 GiB）。无 heartbeat timeout／override、冷构建、清缓存、Mathlib 重编译或依赖变更；Lean `v4.35.0-rc3` 与 Mathlib `389347a7c1cfa76f6bd5be2ca35d4cb621610ad3` 已核对。
### Concrete untilt algebraic-closure Kummer source

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-EMBEDDED-ALGEBRAIC-CLOSURE` | `JoshiTeich.Act1Scene1.EmbeddedAlgebraicClosure.Carrier`, `JoshiTeich.Act1Scene1.EmbeddedAlgebraicClosure.inclusion`, `JoshiTeich.Act1Scene1.EmbeddedAlgebraicClosure.inclusion_injective`, `JoshiTeich.Act1Scene1.EmbeddedAlgebraicClosure.inclusion_algebraMap`, `JoshiTeich.Act1Scene1.EmbeddedAlgebraicClosure.mem_inclusion_range_iff`, `JoshiTeich.Act1Scene1.EmbeddedAlgebraicClosure.equiv`, `JoshiTeich.Act1Scene1.EmbeddedAlgebraicClosure.embedding`, `JoshiTeich.Act1Scene1.EmbeddedAlgebraicClosure.embedding_algebraMap`, `JoshiTeich.Act1Scene1.EmbeddedAlgebraicClosure.embedding_range`, `JoshiTeich.Act1Scene1.EmbeddedAlgebraicClosure.mem_embedding_range_iff`, `JoshiTeich.Act1Scene1.EmbeddedAlgebraicClosure.groupIso`, `JoshiTeich.Act1Scene1.EmbeddedAlgebraicClosure.intertwine`; `Act1Scene1/EmbeddedAlgebraicClosure.lean` | Joshi I `def:untilt-galois` (1470--1498), preferred-closure Kummer theory (1588--1632); Mathlib relative `algebraicClosure` and `IsAlgClosure.equiv`. For a specified base embedding into an algebraically closed field, constructs the relative algebraic-closure carrier, proves its image is exactly the elements algebraic over the base, and transports the Krull Galois group with its intertwining law. Original proof, no reference code copied. | Scene1/Derived; proved. Does not construct a whole untilt action, tempered marking, or cross-holomorphoid source. |
| `JT-SCENE1-INITIAL-THETA-UNTILT-KUMMER` | `JoshiTeich.Act1Scene1.InitialThetaUntiltKummer.localEmbedding`, `JoshiTeich.Act1Scene1.InitialThetaUntiltKummer.Closure`, `JoshiTeich.Act1Scene1.InitialThetaUntiltKummer.inclusion`, `JoshiTeich.Act1Scene1.InitialThetaUntiltKummer.closureEquiv`, `JoshiTeich.Act1Scene1.InitialThetaUntiltKummer.mem_inclusion_range_iff`, `JoshiTeich.Act1Scene1.InitialThetaUntiltKummer.groupIso`, `JoshiTeich.Act1Scene1.InitialThetaUntiltKummer.rootTower`, `JoshiTeich.Act1Scene1.InitialThetaUntiltKummer.rootTower_power`, `JoshiTeich.Act1Scene1.InitialThetaUntiltKummer.principalUnit_eq_rootImage`, `JoshiTeich.Act1Scene1.InitialThetaUntiltKummer.principalUnit_norm_sub_one_lt_one`, `JoshiTeich.Act1Scene1.InitialThetaUntiltKummer.principalUnit_eq_theta_pilot`, `JoshiTeich.Act1Scene1.InitialThetaUntiltKummer.imageClass`, `JoshiTeich.Act1Scene1.InitialThetaUntiltKummer.imageClass_eq_kummer`, `JoshiTeich.Act1Scene1.InitialThetaUntiltKummer.imageClass_eq_rootTower`, `JoshiTeich.Act1Scene1.InitialThetaUntiltKummer.imageClass_log`, `JoshiTeich.Act1Scene1.InitialThetaUntiltKummer.dividedClass`, `JoshiTeich.Act1Scene1.InitialThetaUntiltKummer.dividedClass_log`, `JoshiTeich.Act1Scene1.InitialThetaUntiltKummer.dividedClass_ne_zero`; `Act1Scene1/IutInitialThetaUntiltKummer.lean` | Joshi I `def:untilt-galois` and Kummer theory (1470--1498, 1588--1632), Joshi II eta/Teichmuller local pilot (932--1013), III principal units and normalized log witness (3190--3236). For the same actual `D`, torsion completion, supported place and existing de Rham coefficient field, embeds the original completion, forms its relative algebraic closure inside that field, transports the original root tower and Kummer class, and proves the principal unit is the same de Rham root-image expression. The original `p*` ordinary-log and divided-class witness formulas remain unchanged. Original proof, no reference code copied. | Scene1/Derived; proved. No claim of full paper theta locus, H1_e/BK, whole-untilt Galois action, or cross-holomorphoid collation. |

Source boundary: This unit upgrades fixed-base preferred-closure transport to the concrete relative algebraic closure inside the actual Fontaine/de Rham coefficient field. It closes the source identity for the actual principal unit and root tower, while retaining the explicit original ordinary-log witness. It does not identify the resulting class with H1_e/Bloch--Kato, produce an admissible holomorphoid marking, or prove a cross-untilt log comparison. No Core assumptions, Prologue revision, or license changes.

Acceptance and all direct Lean attempts (2026-10-20):

| task | exit | seconds | peak process-group RSS (KiB) |
| --- | ---: | ---: | ---: |
| `scene1-untilt-kummer-generic-attempt1.jsonl` | 1 | 53.544 | 4,235,456 |
| `scene1-untilt-kummer-generic-attempt2.jsonl` | 0 | 53.018 | 4,229,600 |
| `scene1-untilt-kummer-actual-attempt1.jsonl` | 1 | 121.849 | 9,259,928 |
| `scene1-untilt-kummer-actual-attempt2.jsonl` | 1 | 115.176 | 9,264,532 |
| `scene1-untilt-kummer-actual-attempt3.jsonl` | 1 | 125.747 | 9,266,744 |
| `scene1-untilt-kummer-actual-attempt4.jsonl` | 1 | 125.315 | 9,271,720 |
| `scene1-untilt-kummer-actual-attempt5.jsonl` | 1 | 141.733 | 9,271,724 |
| `scene1-untilt-kummer-actual-attempt6.jsonl` | 1 | 119.056 | 9,273,564 |
| `scene1-untilt-kummer-actual-attempt7.jsonl` | 0 | 120.387 | 9,273,124 |
| `scene1-untilt-kummer-checks-metrics.jsonl` | 1 | 125.194 | 9,451,384 |
| `scene1-untilt-kummer-checks-attempt2.jsonl` | 0 | 173.057 | 9,450,516 |
| `scene1-untilt-kummer-axioms-metrics.jsonl` | 0 | 132.531 | 9,431,368 |
| `scene1-untilt-kummer-aggregate-metrics.jsonl` | 0 | 117.848 | 9,274,596 |

There were 13 direct Lean tasks: 5 successful and 8 ordinary elaboration/typeclass/import failures. Successful tasks took 596.841 seconds; failed diagnostics took 927.614 seconds; total time was 1524.455 seconds. Maximum process-group RSS was 9,451,384 KiB. No heartbeat timeout or heartbeat override occurred; no memory stop occurred. Final leaf, Checks, Axioms and Scene1 logs were empty of warnings/errors; 30 declarations were checked individually, 3068 axiom entries were audited against `propext`, `Classical.choice`, `Quot.sound`, with no `sorryAx`; static import audit covered 546 reachable project modules and no forbidden imports. All tasks used CPU affinity 0--13, `LEAN_NUM_THREADS=10`, Lean `-j1`, existing precompiled dependencies, and no cold build or Mathlib recompilation.
### Actual Initial-Theta admissible-prime source package

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-INITIAL-THETA-ADMISSIBLE-PRIME-SOURCE-AUDIT` | `JoshiTeich.Act1Scene1.InitialThetaAdmissiblePrimeSourceAudit.source`, `source_ell`, `source_torsion_field`, `source_representation`, `source_fixed_field_eq_rep_adapter`, `source_sl2_image`, `source_residue_coprime`, `source_q_order_coprime`; `Act1Scene1/IutInitialThetaAdmissiblePrimeSourceAudit.lean` | Joshi III `ss:theta-data-fixing2` (1023--1055), IUT I Definition 3.1(b--c), and `refer/iut/Iut/Cor312/ThetaData/AdmissiblePrime.lean`. Packages the fields already chosen by one actual `InitialThetaData`: the same `ell`, genuine elliptic-torsion Galois representation, `SL2` image, open kernel, fixed-field torsion carrier, `F/F_mod` degree coprimality, residue-characteristic coprimality, and Tate q-order coprimality. The adapter is a projection/source audit and does not manufacture a new prime or hide the representation condition. Original proofs, no reference code copied. | Scene1/Derived; proved. Existence of a new admissible prime, a new mod-ell representation, and the later holomorphoid/theta source remain separate obligations. |

Source boundary: This closes the source packaging for the admissible-prime fields of the existing `InitialThetaData`; it does not close the parent obligation requiring a jointly constructed Initial Theta input or a new `L'`/holomorphoid model. No Core assumptions, Prologue revision, or license changes.

Acceptance and leaf attempts (2026-10-20):

| task | exit | seconds | peak process-group RSS (KiB) |
| --- | ---: | ---: | ---: |
| `scene1-admissible-prime-attempt1.jsonl` | 1 | 114.809 | 9,119,128 |
| `scene1-admissible-prime-attempt2.jsonl` | 1 | 127.028 | 9,121,280 |
| `scene1-admissible-prime-attempt3.jsonl` | 0 | 118.787 | 9,113,468 |
| Checks | 0 | 127.855 | 9,451,220 |
| Axioms | 0 | 119.824 | 9,431,560 |
| Scene1 aggregate | 0 | 122.398 | 9,235,828 |

The first leaf attempt had an index mismatch between the package prime and the representation coefficient field; the second showed the structure had captured the ambient `D` as an implicit parameter rather than a field; the third fixed the source index to `D.prime.ℓ` and passed. These were ordinary Lean elaboration errors, with no mathematical premise change. There were 6 direct Lean tasks, 4 successful and 2 failed; successful tasks took 488.864 seconds, failed diagnostics 241.837 seconds, and total time was 730.701 seconds. Maximum process-group RSS was 9,451,220 KiB. No heartbeat timeout/override or memory stop occurred. The leaf and aggregate logs were empty; 8 declarations were checked individually and all 3076 axiom entries were within `propext`, `Classical.choice`, `Quot.sound`, with no `sorryAx`; static import audit covered 547 reachable modules and no forbidden imports. CPU affinity 0--13, `LEAN_NUM_THREADS=10`, Lean `-j1`, existing precompiled dependencies, no cold build and no Mathlib recompilation.
### Actual Kummer/Bloch--Kato normalization audit

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-INITIAL-THETA-BK-NORMALIZATION-AUDIT` | `JoshiTeich.Act1Scene1.PrincipalUnitKummer.BlochKatoNormalizationAudit.actualIntegralClass_ordinaryLog`, `actualIntegralClass_normalizedComparison`, `ordinaryComparison_unique_of_smallBallCalibration`, `normalizedComparison_not_smallBallCalibrated`; `Act1Scene1/IutInitialThetaBlochKatoNormalizationAudit.lean` | Joshi III `ss:bloch-kato-exp`, `ss:bloch-kato-logarithm`, and `eq:bloch-kato-log-class` (3210--3236), together with the actual small-ball Kummer/log calibration. For each actual support place, proves that any Qp-linear comparison satisfying the ordinary small-ball calibration is the original unscaled ordinary logarithm. The actual integral Kummer class therefore has log `p* * witness`; the normalized `log/p*` comparison has the paper witness but provably fails that same calibration. Original proof, no reference code copied. | Scene1/Derived; proved as a normalization audit. It does not identify the carrier with H1_e, construct BK exponential/log, or claim the paper's H1_e source identity. |

Source boundary: This records the forced normalization choice and the actual class formulas. It strengthens the open H1_e/BK obligation by ruling out an incompatible simultaneous normalization; it does not close that obligation. No Core assumptions, Prologue revision, or license changes.

Acceptance and attempts (2026-10-20): leaf attempt1 exited 1 after 227.206 seconds and 9,216,140 KiB at the default heartbeat; attempt2 exited 1 after 346.469 seconds and 9,816,244 KiB at 1,000,000 heartbeats; after removing redundant wrappers and making the closure parameters explicit, attempt3 exited 1 after 149.225 seconds and 9,340,212 KiB; attempt4 exited 0 after 151.696 seconds and 9,340,984 KiB at 2,000,000 heartbeats. The first failure was the expected heartbeat timeout; the second also timed out under the user escalation policy; the latter two were ordinary elaboration/typeclass adaptation. Checks exited 0 in 121.294 seconds with 9,451,280 KiB; Axioms exited 0 in 111.637 seconds with 9,433,608 KiB; Scene1 aggregate exited 0 in 110.215 seconds with 9,253,368 KiB. Seven direct tasks, four successful and three failed; successful time 494.842 seconds, failed time 722.900 seconds, total 1217.742 seconds; peak RSS 9,451,280 KiB. Final leaf and aggregate logs were empty; four declarations were checked individually and 3080 axiom entries were audited against `propext`, `Classical.choice`, `Quot.sound`, with no `sorryAx`; static import audit covered 548 reachable modules and no forbidden imports. No memory stop or cold build; Mathlib was not recompiled.

### Actual torsion-q-root theta-pilot scaling law

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-INITIAL-THETA-TORSION-THETA-PILOT-SCALING` | `JoshiTeich.Act1Scene1.InitialThetaTorsionThetaPilotScaling.PilotIndex`, `indexOne`, `pilotData`, `pilotData_value_eq`, `pilotData_norm_eq`, `pilotData_laws`, `pilotData_log_shell`; `Act1Scene1/IutInitialThetaTorsionThetaPilotScaling.lean` | Joshi II `pr:teichmuller-lift-A/B` and `thm:theta-pilot-object-appears` (940--1013), consumed through the project's actual torsion q-root embedding and its evaluation in the same original `B_dR+`. On the finite index `ULift (Fin (ell+1))`, uses the actual `j^2` de Rham evaluation as pilot value and norm, with scaling index `j`; base `j=1`. Proves nonzero values, positive norms, exact norm scaling by `j^2`, and sets period/liftedLog to the real logarithm of the actual evaluated norm. Original proof; no reference code copied. | Scene1/Derived; proved as a local finite-index scaling producer. It does not construct the global theta link, an infinite index of all positive j, a holomorphoid geometric base point/marking, cross-untilt collation, H1_e/BK comparison, or the paper theta-values locus. |

Source boundary: This producer discharges the local `ThetaPilotScalingLaws` contract for the actual torsion q-root evaluations inside one selected untilt. The real logarithm of the norm is a local real-valued pilot field, not the paper's p-adic Bloch--Kato logarithm. The finite index and local untilt do not close the parent theta locus, joint Initial Theta model, or H1_e/BK obligations. No Core assumptions, Prologue revision, or license changes.

Acceptance and attempts (2026-10-20): the leaf used the hot-check script for the single target with CPU affinity 0--13, `LEAN_NUM_THREADS=10`, Lean `-j1`, one worker and 0.5-second process-group RSS sampling. Attempts 1--3 exited 1 after 110.297, 112.282 and 108.698 seconds (peak RSS 9,238,372, 9,236,736 and 9,239,532 KiB), from universe/implicit-parameter and structure-literal unfolding adaptations. Attempt4 exited 1 after 108.187 seconds and 9,230,892 KiB on the real-power square normalization; attempt5 exited 1 after 106.548 seconds and 9,241,224 KiB on an unavailable ULift simp lemma. Attempt6 exited 0 after 138.838 seconds and 9,231,036 KiB, with empty log and no `sorryAx`. These were ordinary elaboration errors; no heartbeat timeout or memory stop occurred. Final Checks/Axioms/aggregate and static import audit are recorded after the unit closeout.

Closeout acceptance: the first Checks attempt exited 1 after 116.693 seconds and 9,452,100 KiB because the audit import list did not yet include the new leaf; after adding the exact import, Checks exited 0 in 121.828 seconds with 9,453,276 KiB, Axioms exited 0 in 108.606 seconds with 9,431,692 KiB, and the Scene1 aggregate exited 0 in 107.637 seconds with 9,275,268 KiB. Across 10 direct tasks, 4 succeeded and 6 were ordinary source/elaboration/import failures; successful time was 476.909 seconds, failed time 662.705 seconds, total 1139.614 seconds; peak RSS was 9,453,276 KiB. No heartbeat timeout, heartbeat override, memory stop, cold build or Mathlib recompilation occurred. Final logs were empty; the six axiom-audited declarations used only the standard whitelist `propext`, `Classical.choice`, `Quot.sound`, with no `sorryAx`. Static import closure covered 549 reachable project modules, with no Obligations, Candidate, Scene2, Act2 or `Iut.*` imports.

### Actual torsion-q-root pilot ordinary-log shell carrier

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-INITIAL-THETA-TORSION-PILOT-LOG-SHELL` | `JoshiTeich.Act1Scene1.InitialThetaTorsionPilotLogShell.qrootAt_pilot_normalizedLog_mem_logShell`, `qrootAt_pilot_normalizedLog_norm`, `qrootAt_pilot_norm_eq_deRham_evaluation_norm`; `Act1Scene1/IutInitialThetaTorsionPilotLogShell.lean` | Joshi III `eq:bloch-kato-log-class` (3226) and the local paper-normalized ordinary-log/log-shell calculation, consumed with the actual q-root family and Joshi II de Rham pilot evaluation (940--1013). On the original torsion completion, proves `paperNormalizedLog(qrootAt^(j^2))` lies in the ordinary log-shell and has norm `‖qrootAt‖^(j^2)`; the existing evaluation theorem identifies this norm with the same de Rham pilot evaluation. Original proof; no reference code copied. | Scene1/Derived; proved as a local carrier/evaluation bridge. It does not identify the ordinary logarithm with Bloch--Kato, does not construct H1_e classes, and does not close theta locus or cross-holomorphoid collation. |

Source boundary: The log-shell theorem is deliberately applied on the original torsion completion, which carries the actual valued/rank-one structure. The de Rham coefficient field is used only through the already proved evaluation norm comparison; no new valued instance is imposed on that untilt carrier. No Core assumptions, Prologue revision, or license changes.

Acceptance and attempts (2026-10-20): the first three leaf attempts exited 1 after 106.164, 109.594 and 110.635 seconds (peak RSS 9,231,360, 9,233,752 and 9,236,212 KiB) from carrier/universe and power-norm elaboration adaptations. Attempt4 exited 0 after 104.031 seconds and 9,236,212 KiB with an empty log and no `sorryAx`; no heartbeat timeout or memory stop occurred. Final Checks/Axioms/aggregate and static import audit are recorded after unit closeout.

### Canonical actual hull coefficient-weighted volume

`JT-SCENE1-CANONICAL-ACTUAL-HULL-DATA`: `CanonicalActualHull.data_thetaVolume_eq_exp_neg_coefficientWeightedPaperSum` transports the existing `hullVolume_eq_exp_neg_coefficientWeightedPaperSum` to the canonical data field. Source: Joshi III `ss:weighted-vol` and `cor:cor312`, through the actual VBad representative-coefficient accounting. The formula is `data.thetaVolume = exp(-length(D) * coefficientWeightedPaperSum(D))`. This is an internal carrier identity; the explicit `AnalyticInput` and the identification with the paper theta-volume remain open. Original proof; Scene1/Derived; no Core assumption or boundary revision.

Acceptance (2026-10-21): monitored direct hot tasks for the leaf, Checks.SceneBounds, Axioms.SceneBounds, and Act1Scene1 exited 0 in 139.427, 148.105, 148.127, and 144.119 seconds; respective process-group RSS peaks were 9,235,172, 9,454,760, 9,435,380, and 9,228,856 KiB. All 3098 axiom entries, including the new theorem, used only `propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx`. CPU 0--13, LEAN_NUM_THREADS=10, Lean -j1, one worker, RSS sampled every 0.5 seconds with an 85 GiB stop. No memory stop, cold build, or Mathlib compilation. Evidence: `/tmp/scene1-canonical-final-20261021.metrics.log`.

### Actual cyclotomic Tate inverse limit to tilt and Fontaine kernel

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-CYCLOTOMIC-TATE-TILT` | `CyclotomicTateTilt.coordinate`, `toPreTilt`, `untilt_shift_toPreTilt`, `toPreTilt_injective`, `sharpOneEquiv`; `Act1Scene1/CyclotomicTateTilt.lean` | Joshi II `eq:tate-module-of-lubin-tate` (935--938), which permits the multiplicative formal group, and `pr:teichmuller-lift-A` (940--958); Mathlib PreTilt/Teichmuller limit characterization. Reduces the original compatible roots of unity, proves integrality, recovers the nth root by inverse Frobenius and untilting, and proves an exact multiplicative equivalence with the existing integral sharp-one fiber. Both inverses use the original carriers. | Scene1/Derived; proved local algebraic source bridge. |
| `JT-SCENE1-INITIAL-THETA-CYCLOTOMIC-TATE-TILT` | `InitialThetaCyclotomicTateTilt.epsilon`, `epsilon_injective`, `sharp_epsilon`, `teichmuller`, `kernelCoordinate`, `kernelCoordinate_eq_zero_iff`, `kernelCoordinate_mul`, `theta_kernelCoordinate_add`, `canonicalKernelCoordinate_ne_zero`, `canonicalKernelCoordinate_mem_ker`; `Act1Scene1/IutInitialThetaCyclotomicTateTilt.lean` | Consumes that root-tower construction for the same D/w, the proved equivalence with actual tilt valuation integers, and the original Fontaine theta. The element mu(x)=[epsilon(x)]-1 is in the original Fontaine kernel, is injective as a function of the tower, and obeys mu(xy)=mu(x)+mu(y)+mu(x)mu(y). The existing primitive compatible tower gives a concrete nonzero mu, with no free compatible-generator or kernel certificate. | Scene1/Derived; proved actual input adapter and multiplicative-formal-group kernel coordinate. |

These are original proofs; no reference code was copied. A normed, complete, ultrametric untilt with prime norm strictly between zero and one suffices for the generic equivalence; the actual adapter uses the existing canonical completed algebraic closure. The element [epsilon]-1 is not asserted to be the additive Tate period. A period logarithm, its nonvanishing and Frobenius-p identity, the ring B and its Frechet/rho topology, H1_e/BK comparison, and cross-holomorphoid collation remain open. No new Core assumptions, Prologue revision, or license changes.

Acceptance (2026-10-21):

| task | exit | seconds | peak process-group RSS (KiB) |
| --- | ---: | ---: | ---: |
| Generic leaf attempt 1 | 1 | 81.318 | 5,746,720 |
| Generic leaf attempt 2 | 0 | 87.973 | 5,746,380 |
| Actual D/w leaf | 0 | 139.043 | 9,100,236 |
| Checks.SceneBounds | 0 | 150.662 | 9,458,128 |
| Axioms.SceneBounds | 0 | 141.986 | 9,438,752 |
| Act1Scene1 aggregate | 0 | 144.681 | 9,276,228 |

The first generic attempt failed on explicit subtype coercion, modular-reflexivity elaboration, and set-membership unfolding; no mathematical assumption changed. The corrected generic leaf and the actual leaf passed with empty logs. There were six direct Lean tasks: five successful and one ordinary elaboration failure. Successful time was 664.345 seconds, failed time 81.318 seconds, total 745.663 seconds; peak process-group RSS was 9,458,128 KiB. No heartbeat timeout or override occurred. All 34 new public declarations were checked and axiom-audited: all 3132 dependent axiom entries used only `propext`, `Classical.choice`, `Quot.sound`, with one further axiom-free entry and no `sorryAx`. Static import audit covered 552 reachable project modules, with no forbidden imports or new proof holes. All tasks used CPU 0--13, LEAN_NUM_THREADS=10, Lean -j1, one worker, and 0.5-second process-group RSS sampling with an 85 GiB stop. No memory stop, cache deletion, cold build, or Mathlib recompilation. Evidence: `/tmp/scene1-tate-tilt-attempt1.metrics.log`, `/tmp/scene1-tate-tilt-attempt2.metrics.log`, `/tmp/scene1-tate-tilt-final-audit.metrics.log`, `/tmp/scene1-tate-tilt-axioms.json`, `/tmp/scene1-tate-tilt-static.json`.

### Convergent logarithm on the original de Rham plus ring

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-ADIC-LOGARITHM` | `AdicLogarithm.quotient`, `log_eq_X_mul_quotient`, `oneAdd`, `hasSum_oneAdd`, `oneAdd_eq_mul_unit`, `oneAdd_eq_zero_iff`, `oneAdd_mem_ideal`; `Act1Scene1/AdicLogarithm.lean` | Joshi II multiplicative-formal-group period, `eq:tate-module-of-lubin-tate` and `pr:teichmuller-lift-A` (935--958); Mathlib formal logarithm and evaluation of power series in a complete, separated, linearly topologized Q-algebra. Evaluates the genuine convergent formal logarithm and proves log(1+a)=a*u for a unit u by evaluating log(1+X)/X, whose constant coefficient is one. Thus logarithm preserves nonvanishing and every ideal containing a. | Scene1/Derived; proved generic adic logarithm construction. |
| `JT-SCENE1-INITIAL-THETA-DE-RHAM-LOGARITHM` | `InitialThetaDeRhamLogarithm.intCast_isUnit`, `rationalMap`, `rationalAlgebra`, `linearTopology`, `hasEval_kernel`, `logOneAdd`, `hasSum_logOneAdd`, `theta_logOneAdd`, `norm_logOneAdd`, `tateCoordinate`, `tateLog`, `hasSum_tateLog`, `theta_tateLog`, `norm_tateLog`, `tateLog_eq_zero_iff`; `Act1Scene1/IutInitialThetaDeRhamLogarithm.lean` | Joshi II period source (935--958) and B_dR inclusion (1069--1076), through the project's original Ainf-to-B_dR+ map. Derives rational scalars from actual theta-nonvanishing of nonzero integers and derives linear topology/topological nilpotence from the proved original kernel-adic topology. Evaluates log(1+a) in the same B_dR+ carrier, proves it lies in the original theta kernel and has exactly the original primitive-adic norm of a. Applies the construction to the original Tate tower's [epsilon]-1, rather than an unrelated uniformizer. | Scene1/Derived; proved actual completion and Tate-source consumer. |

These are original proofs; no reference code was copied. No free rational-scalar, topological-nilpotence, logarithm-convergence, norm-comparison or kernel-membership certificate is added to D. Nonvanishing is preserved for the element in B_dR+, with the precise statement `tateLog(x)=0 iff tateCoordinate(x)=0`. The original [epsilon]-1 is already nonzero in Ainf for a nontrivial tower; preservation of that nonzero value under Ainf-to-B_dR+ remains a separate source obligation. Additivity in the Tate variable, the Frobenius-p identity, identification with the paper's T_y in B^{phi=p}, Frechet/rho structure, H1_e/BK and cross-holomorphoid collation remain open. The norm here is the existing primitive-adic norm, not the untilt norm or the paper's rho norm. No new Core assumptions, Prologue revision, or license changes.

Acceptance (2026-10-21):

| task | exit | seconds | peak process-group RSS (KiB) |
| --- | ---: | ---: | ---: |
| Generic attempt 1 | 1 | 61.235 | 4,140,148 |
| Generic attempt 2 | 1 | 68.264 | 4,161,392 |
| Generic attempt 3 | 0 | 62.666 | 4,174,996 |
| Actual D/w leaf | 0 | 136.498 | 9,099,780 |
| Checks.SceneBounds | 0 | 144.979 | 9,460,964 |
| Axioms.SceneBounds | 0 | 134.868 | 9,442,408 |
| Act1Scene1 aggregate | 0 | 141.528 | 9,276,300 |

The first two generic attempts failed on explicit evaluation-hom coercion and ideal-membership argument elaboration. The corrected generic leaf and the actual leaf passed with empty logs and unchanged mathematical assumptions. Seven direct Lean tasks: five successful, two ordinary elaboration failures. Successful time 620.539 seconds, failed time 129.499 seconds, total 750.038 seconds; peak process-group RSS 9,460,964 KiB. No heartbeat timeout or override occurred. All 28 new public declarations and instances were checked individually and axiom-audited; 3160 dependent entries used only `propext`, `Classical.choice`, `Quot.sound`, one further entry was axiom-free, and there was no `sorryAx`. Static import audit covered 554 reachable project modules, with no forbidden imports or new proof holes. All tasks used CPU 0--13, LEAN_NUM_THREADS=10, Lean -j1, one worker and 0.5-second process-group RSS monitoring at an 85 GiB stop. No memory stop, cold build, cache deletion or Mathlib compilation. Both new Mathlib imports (PowerSeries.Evaluation and PowerSeries.Log) had precompiled artifacts before the first diagnostic. Evidence: `/tmp/scene1-adic-log-attempt{1,2,3}.metrics.log`, `/tmp/scene1-adic-log-final-audit.metrics.log`, `/tmp/scene1-adic-log-axioms.json`, `/tmp/scene1-adic-log-static.json`.

### Actual Ainf-to-de Rham embedding and nonzero Tate logarithm

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-PRIME-ADIC-SEPARATION` | `PrimeAdicSeparation.of_mod_p`, `away_injective`, `pow_dvd_of_localized_dvd`, `away`; `Act1Scene1/PrimeAdicSeparation.lean` | Joshi II primitive Fontaine equation and B_dR inclusion (838, 932, 1069--1076); Mathlib p-adic separation and cancellation of powers of a prime. In a domain, p-adic separation plus the explicit criterion that infinite xi-divisibility implies p-divisibility gives xi-adic separation, provided xi is prime and does not divide p. Dividing by p preserves infinite xi-divisibility. Clearing p-denominators and prime-power saturation then preserves separation in R[1/p]. | Scene1/Derived; proved generic separation and localization lemmas, with their mod-p criterion explicit. |
| `JT-SCENE1-INITIAL-THETA-DE-RHAM-EMBEDDING` | `InitialThetaDeRhamEmbedding.constantCoeff_eq_zero_of_all_primitive_pow_dvd`, `primitiveSeparated`, `localizedKernelSeparated`, `sourceKernelSeparated`, `sourceToPlus_injective`, `localizationToPlus_injective`, `ainfToPlus_injective`, `tateCoordinate_injective`, `tateLog_eq_zero_iff`, `canonicalTateLog_ne_zero`, `theta_canonicalTateLog`; `Act1Scene1/IutInitialThetaDeRhamEmbedding.lean` | For the same actual D/w, the zeroth Witt digit of xi=[p-flat]-p is the original p-flat, with norm strictly below one. Infinite xi-divisibility bounds the zeroth digit by every power of that norm and forces it to vanish. The actual Witt p-adic separation and original Fontaine prime-kernel theorem supply all hypotheses of the generic lemmas. Transports the resulting localized separation through the existing source ring equivalence and applies Mathlib's adic-completion injection theorem. The original Ainf and Ainf[1/p] therefore inject into the original B_dR+, and the original nontrivial compatible Tate tower has a nonzero convergent logarithm in its original theta kernel. | Scene1/Derived; proved actual source embedding and nonzero period producer. |

These are original proofs; no reference code was copied. No Noetherian, separatedness, completion-injectivity or nonzero-period certificate is added to the actual inputs. This closes the Ainf-to-B_dR+ nonvanishing obligation left by the preceding logarithm unit: `tateLog(x)=0 iff x=1`, and the existing primitive compatible generator gives a concrete nonzero canonicalTateLog with theta=0. The proof uses the original [epsilon]-1 and the original Ainf-to-plus map. Additivity in the Tate variable, the Frobenius-p identity, identification with T_y in B^{phi=p}, Frechet/rho topology, H1_e/BK and cross-holomorphoid collation remain open. No new Core assumptions, Prologue revision, or license changes.

Acceptance (2026-10-21):

| task | exit | seconds | peak process-group RSS (KiB) |
| --- | ---: | ---: | ---: |
| Generic attempt 1 | 1 | 56.139 | 3,787,656 |
| Generic attempt 2 | 0 | 55.072 | 3,791,164 |
| Actual leaf attempt 1 | 1 | 140.532 | 9,110,336 |
| Actual leaf attempt 2 | 0 | 138.580 | 9,110,004 |
| Checks.SceneBounds | 0 | 155.256 | 9,463,884 |
| Axioms.SceneBounds | 0 | 139.485 | 9,444,920 |
| Act1Scene1 aggregate | 0 | 139.005 | 9,277,216 |

The first generic attempt needed explicit p^0 reduction. The first actual attempt needed the correct direction of the limit-bound lemma, explicit ideal-map coercions, and the original AdicCompletion.of interface instead of inferring an Algebra instance through the BDeRhamPlus wrapper. These were ordinary elaboration/API failures; no mathematical premise changed. The corrected leaves passed with empty logs. Seven direct Lean tasks: five successful and two failed; successful time 627.398 seconds, failed time 196.671 seconds, total 824.069 seconds; peak process-group RSS 9,463,884 KiB. No heartbeat timeout or override occurred. All 20 new public declarations and instances were checked and axiom-audited; all 3180 dependent entries used only `propext`, `Classical.choice`, `Quot.sound`, with one further axiom-free entry and no `sorryAx`. Static import audit covered 556 reachable project modules and no forbidden imports or new proof holes. All tasks used CPU 0--13, LEAN_NUM_THREADS=10, Lean -j1, one worker and 0.5-second process-group RSS monitoring with an 85 GiB stop. No memory stop, cold build, cache deletion or Mathlib compilation. Evidence: `/tmp/scene1-derham-embedding-attempt{1,2,3}.metrics.log`, `/tmp/scene1-derham-embedding-final-audit.metrics.log`, `/tmp/scene1-derham-embedding-axioms.json`, `/tmp/scene1-derham-embedding-static.json`.

### Actual additive Tate period in the original de Rham theta kernel

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-ADIC-EXPONENTIAL` | `AdicExponential.evaluate`, `evaluate_log`, `evaluate_subst`, `exp`, `exp_log`, `log_exp`, `formal_exp_add`, `exp_add`; `Act1Scene1/AdicExponential.lean` | Joshi II multiplicative-formal-group Tate module (935--958); Mathlib rational formal exponential/logarithm, substitution and evaluation. Uses a discrete uniformity only on the rational coefficient ring. Convergent evaluation retains the target's existing complete, separated linear topology. Uniqueness of HasSum identifies evaluation of log over Q with the previously constructed AdicLogarithm.oneAdd on the target ring. Evaluates formal inverse identities and a coefficient-proved bivariate exponential identity to prove exp/log inverses and exp(a+b)=exp(a)exp(b). | Scene1/Derived; proved formal and convergent algebraic identities. |
| `JT-SCENE1-INITIAL-THETA-ADDITIVE-TATE-PERIOD` | `InitialThetaAdditiveTatePeriod.logOneAdd_mul`, `tateCoordinate_mul`, `tateLog_mul`, `tateLogHom`, `tateLogHom_injective`, `tateLogKernelHom`, `tateLogKernelHom_injective`; `Act1Scene1/IutInitialThetaAdditiveTatePeriod.lean` | Consumes the same actual D/w, original B_dR+ theta kernel, original Tate root tower and original convergent tateLog. Derives log(1+a+b+ab)=log(1+a)+log(1+b) in the original kernel, and then tateLog(xy)=tateLog(x)+tateLog(y) from the actual [epsilon]-1 formal-group law. Packages these exact existing values as additive homomorphisms on Additive of the original Tate group, including an injective map into the original additive theta kernel. Injectivity uses the previously proved tateLog(x)=0 iff x=1. | Scene1/Derived; proved actual additive Tate-period producer. |

These are original proofs; no reference code was copied. No additivity, replacement period, change of Tate carrier, or target topology certificate is added to D. This closes the Tate-variable additivity obligation left by the preceding embedding unit. Continuity for the paper's period topology, Z_p-linearity, Frobenius-p, identification with T_y in the paper's B^{phi=p}, Frechet/rho topology, H1_e/BK and cross-holomorphoid collation remain open. The target is the existing B_dR+ with its existing primitive-adic topology; the discrete rational coefficient ring does not replace that topology. No new Core assumptions, Prologue revision, or license changes.

Acceptance (2026-10-21):

| task | exit | seconds | peak process-group RSS (KiB) |
| --- | ---: | ---: | ---: |
| Generic attempt 1 | 1 | 61.678 | 4,174,648 |
| Generic attempt 2 | 1 | 60.621 | 4,183,164 |
| Generic attempt 3 | 0 | 67.796 | 4,176,252 |
| Actual leaf attempt 1 | 1 | 134.970 | 9,173,712 |
| Actual leaf attempt 2 | 0 | 138.557 | 9,157,948 |
| Checks.SceneBounds | 0 | 149.667 | 9,466,852 |
| Axioms.SceneBounds | 0 | 144.534 | 9,445,524 |
| Act1Scene1 aggregate | 0 | 146.255 | 9,277,864 |

The generic diagnostics corrected an explicit unit coercion, rational coefficient-ring inference, and proof-dependent rewriting after bivariate evaluation. The first actual attempt needed explicit existing convergence proofs in exp_add and the actual residue-prime instance for Witt operations. These were ordinary Lean API/elaboration errors with unchanged mathematical inputs. Final generic and actual leaf logs were empty. Eight direct Lean tasks: five successful and three failed; successful time 646.809 seconds, failed time 257.269 seconds, total 904.078 seconds; peak process-group RSS 9,466,852 KiB. No heartbeat timeout or override occurred. All 19 new public declarations were checked individually and axiom-audited; all 3199 dependent entries used only `propext`, `Classical.choice`, `Quot.sound`, with one further axiom-free entry and no `sorryAx`. Static import audit covered 558 reachable project modules with no forbidden imports or new proof holes. CPU 0--13, LEAN_NUM_THREADS=10, Lean -j1, one worker; process-group RSS sampled every 0.5 seconds with an 85 GiB stop. No memory stop, cold build, cache deletion or Mathlib compilation. New imports had precompiled artifacts before the first diagnostic. Evidence: `/tmp/scene1-tate-additive-attempt{1,2,3,4}.metrics.log`, `/tmp/scene1-tate-additive-final-audit.metrics.log`, `/tmp/scene1-tate-additive-axioms.json`, `/tmp/scene1-tate-additive-static.json`.

### Actual Witt Frobenius on Tate periods and the de Rham topology boundary

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-INITIAL-THETA-TATE-FROBENIUS` | `InitialThetaTateFrobenius.phi`, `phi_teichmuller`, `phi_kernelCoordinate`, `iterate_phi_kernelCoordinate`, `frobeniusCoordinate`, `frobeniusLog`, `frobeniusLog_scaling`; `Act1Scene1/IutInitialThetaTateFrobenius.lean` | Joshi II `eq:tate-module-of-lubin-tate` / `pr:teichmuller-lift-A` (935--958) and the principal Fontaine equation (838, 932); Mathlib's original WittVector.frobenius. Proves that actual phi sends the original Teichmuller Tate coordinate for x to that for x^p, and its n-fold iterate sends [epsilon(x)]-1 to the original coordinate for x^(p^n). After the existing Ainf-to-B_dR+ map, the existing convergent logarithm is exactly p^n times the original tateLog(x). | Scene1/Derived; proved actual Frobenius source/logarithm compatibility. |
| `JT-SCENE1-INITIAL-THETA-TATE-FROBENIUS` | `theta_phi_primitive`, `theta_phi_primitive_ne_zero`, `phi_not_preserve_kernel`, `phi_primitive_image_isUnit`, `phi_primitive_image_not_hasEval`, `no_continuous_frobenius_extension` in the same namespace/file | Computes theta(phi(xi))=p^p-p != 0 for the original xi=[p-flat]-p. Thus actual phi does not preserve the original Fontaine kernel. The original image of xi is topologically nilpotent in the existing primitive-adic B_dR+, whereas the image of phi(xi) is a unit with every power having norm one. A continuous ring endomorphism of this B_dR+ commuting with phi on all original Ainf elements would preserve topological nilpotence, giving a contradiction. | Scene1/Derived; proved precise negative evidence against continuous extension in the existing primitive-adic topology. |

These are original proofs; no reference code was copied. The Frobenius is the actual Witt operator, applied before the existing completion/logarithm. This proves a source-level phi/p scaling law, not a Frobenius endomorphism on B_dR+ or a completed construction of the paper's B^{phi=p}. The negative result is limited to a continuous endomorphism of the existing B_dR+ with its primitive-adic topology and its original Ainf map. The paper's Frechet B/rho topology and Frobenius action, the comparison of its Tate submodule with these actual periods, Z_p-linearity, H1_e/BK and cross-holomorphoid collation remain open. No new Core assumptions or Prologue revision; see S1-BND-488 for the route boundary.

Acceptance (2026-10-21):

| task | exit | seconds | peak process-group RSS (KiB) |
| --- | ---: | ---: | ---: |
| Leaf attempt 1 | 1 | 145.506 | 9,269,520 |
| Leaf attempt 2 | 1 | 132.877 | 9,103,332 |
| Leaf attempt 3 | 1 | 133.962 | 9,106,452 |
| Leaf attempt 4 | 0 | 127.291 | 9,102,532 |
| Checks.SceneBounds | 0 | 146.535 | 9,469,020 |
| Axioms.SceneBounds | 0 | 136.345 | 9,449,264 |
| Act1Scene1 aggregate | 0 | 135.344 | 9,278,136 |

The three failed leaf diagnostics corrected explicit power-map selection, natural-multiple argument order and type-tag simplification, and the norm-limit function composition. These were ordinary Lean API/elaboration errors with unchanged mathematical inputs. Final leaf and aggregate logs were empty. Seven direct Lean tasks: four successful and three failed; successful time 545.515 seconds, failed time 412.345 seconds, total 957.860 seconds; peak process-group RSS 9,469,020 KiB. No heartbeat timeout or override occurred. All 19 new public declarations were checked individually and axiom-audited; all 3218 dependent entries used only `propext`, `Classical.choice`, `Quot.sound`, with one further axiom-free entry and no `sorryAx`. Static import audit covered 559 reachable project modules with no forbidden imports or new proof holes. CPU 0--13, LEAN_NUM_THREADS=10, Lean -j1, one worker; process-group RSS sampled every 0.5 seconds with an 85 GiB stop. No memory stop, cold build, cache deletion or Mathlib compilation; the Witt Frobenius import had precompiled artifacts before the first diagnostic. Evidence: `/tmp/scene1-tate-frobenius-attempt{1,2,3,4}.metrics.log`, `/tmp/scene1-tate-frobenius-final-audit.metrics.log`, `/tmp/scene1-tate-frobenius-axioms.json`, `/tmp/scene1-tate-frobenius-static.json`.

### Actual two-element Witt localization with Frobenius automorphism

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-INITIAL-THETA-BOUNDED-WITT-LOCALIZATION` | `InitialThetaBoundedWittLocalization.varpi`, `varpi_norm_pos_lt_one`, `Ring`, `inclusion_injective`, `prime_isUnit`, `teichVarpi_isUnit`, `frobeniusEquiv`, `toDeRhamPlus_injective`, `evaluation_inclusion`, `frobenius_tateCoordinate`, `toDeRhamPlus_tateCoordinate`; `Act1Scene1/IutInitialThetaBoundedWittLocalization.lean` | Joshi II `se:ff-rings` (511--512), `pr:primitive-elements1` and the inclusion W(O_F) into B (719--727), together with Frobenius-stable B+ and its period-ring inclusion (1051--1076). Constructs the explicit algebraic starting ring W(O_F)[1/p,1/[varpi]] as the original Ainf localized at p*[varpi], using the same actual varpi already constructed with sharp(varpi)=p and 0<norm(varpi)<1. Both p and [varpi] are proved units. The original Witt Frobenius and its original inverse extend to this localization and are proved inverse on the entire ring by localization uniqueness. The inverse extension uses phi^{-1}([varpi])^p=[varpi], rather than a free root or operator certificate. The original Ainf-to-B_dR+ map extends to an injective map of this ring, retaining the original theta evaluation. The original Tate coordinates inject into this ring, transform by x -> x^p under its actual Frobenius automorphism, and map to exactly the previous de Rham Tate coordinates. | Scene1/Derived; proved algebraic Witt localization and source consumers. |

This is the two-element algebraic localization only. Its rho norms, bounded Witt-expansion characterization, independence of the contracting element, Frechet completion and identification with the paper's completed B have not been asserted or proved here. The source citations specify the W(O_F)-to-B/Frobenius/period-ring direction; they do not supply the missing norm construction. The map into B_dR+ is a ring embedding; it does not intertwine a Frobenius on all of B_dR+ (S1-BND-488 excludes a continuous extension for its existing primitive-adic topology). Convergence of the Tate logarithm in a rho completion and the full paper T_y subset B^{phi=p} identity remain open. These are original proofs, with no reference code copied. No new Core assumptions, Prologue revision, target topology, or license changes.

Acceptance (2026-10-21):

| task | exit | seconds | peak process-group RSS (KiB) |
| --- | ---: | ---: | ---: |
| Leaf attempt 1 | 1 | 145.614 | 9,129,292 |
| Leaf attempt 2 | 1 | 150.287 | 9,128,832 |
| Leaf attempt 3 | 0 | 136.988 | 9,112,356 |
| Checks.SceneBounds | 0 | 161.818 | 9,472,452 |
| Axioms.SceneBounds | 0 | 159.843 | 9,452,736 |
| Act1Scene1 aggregate | 0 | 141.561 | 9,278,528 |

The two failed diagnostics corrected the integral/field norm coercion, rewriting a denominator occurring in the localization carrier, the injective-map criterion name, and the explicit inclusion/algebraMap interface in denominator clearing. These were ordinary Lean elaboration/API errors, with unchanged mathematical inputs. Tate-coordinate consumers were added during the first diagnostic and were covered by the subsequent final leaf and all 32 name checks. Final leaf and aggregate logs were empty. Six direct Lean tasks: four successful and two failed; successful time 600.210 seconds, failed time 295.901 seconds, total 896.111 seconds; peak process-group RSS 9,472,452 KiB. No heartbeat timeout or override occurred. All 32 new public declarations and instances were checked individually and axiom-audited; all 3250 dependent entries used only `propext`, `Classical.choice`, `Quot.sound`, with one further axiom-free entry and no `sorryAx`. Static import audit covered 560 reachable project modules with no forbidden imports or new proof holes. CPU 0--13, LEAN_NUM_THREADS=10, Lean -j1, one worker; process-group RSS sampled every 0.5 seconds with an 85 GiB stop. No memory stop, cold build, cache deletion or Mathlib compilation. Evidence: `/tmp/scene1-bounded-witt-attempt{1,2,3}.metrics.log`, `/tmp/scene1-bounded-witt-final-audit.metrics.log`, `/tmp/scene1-bounded-witt-axioms.json`, `/tmp/scene1-bounded-witt-static.json`.

### Independence of the contracting element in the actual Witt localization

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-INITIAL-THETA-WITT-LOCALIZATION-CHOICE` | `InitialThetaWittLocalizationChoice.dvd_contraction_pow`, `teichmuller_isUnit_of_contraction`, `teichmuller_isUnit`, `ChoiceRing`, `choiceEquiv`, `choiceToDeRhamPlus_inclusion`, `choiceToDeRhamPlus_injective`, `choiceFrobenius`, `choiceFrobenius_inclusion`, `lift`, `lift_inclusion`, `lift_unique`; `Act1Scene1/IutInitialThetaWittLocalizationChoice.lean` | Joshi II `se:ff-rings` and W(O_F) into B (511--512, 719--727), through the actual norm valuation integers and the algebraic Witt localization. A nonzero integral a divides a power of any contracting s by the actual norm inequality. Teichmuller multiplicativity then proves that any homomorphism inverting [s] also inverts every nonzero integral [a]. The previously constructed ring therefore already inverts all these elements. For every nonzero contracting s, builds both maps between the original ring and W(O_F)[1/p,1/[s]], proves they are inverse and fix original Ainf as an algebra equivalence. The existing de Rham embedding is retained; conjugating the proved original Frobenius along the algebra equivalence gives the original Witt Frobenius on the alternative carrier. Existence and uniqueness of factorization for maps inverting p and all nonzero integral Teichmuller elements give the explicit universal property. | Scene1/Derived; proved algebraic choice independence and universal mapping property. |

These are original proofs; no reference code was copied. The valuation divisibility, powers tending to zero, localization universal property and the existing Frobenius/de Rham maps supply all proofs. No equivalence, unit condition for all Teichmuller elements, or arbitrary choice-comparison certificate is added to D. This closes dependence on the chosen contracting element at the algebraic localization stage. It does not identify bounded Witt expansions, construct rho norms, prove compatibility of such norms under the equivalence, construct Frechet B, or prove the paper Tate-period/BK comparison. The source citation motivates the choice-independent W(O_F)-to-B carrier; it does not substitute for those analytic obligations. No Core assumption, Prologue revision or target topology changes.

Acceptance (2026-10-21):

| task | exit | seconds | peak process-group RSS (KiB) |
| --- | ---: | ---: | ---: |
| Initial leaf (choice equivalence and universal property) | 0 | 148.726 | 9,136,200 |
| Final leaf (including Frobenius consumer) | 0 | 153.474 | 9,137,512 |
| Checks.SceneBounds | 0 | 168.092 | 9,474,744 |
| Axioms.SceneBounds | 0 | 163.585 | 9,454,904 |
| Act1Scene1 aggregate | 0 | 153.349 | 9,277,904 |

All five direct Lean tasks passed, taking 787.226 seconds in total; peak process-group RSS 9,474,744 KiB. The first leaf validated choice independence and the universal property; after adding the Frobenius consumer, the final leaf validated all public declarations with an empty log. No failed task, heartbeat timeout or override occurred. All 20 new public declarations were checked individually and axiom-audited; all 3270 dependent entries used only `propext`, `Classical.choice`, `Quot.sound`, with one further axiom-free entry and no `sorryAx`. Static import audit covered 561 reachable project modules with no forbidden imports or new proof holes. CPU 0--13, LEAN_NUM_THREADS=10, Lean -j1, one worker; process-group RSS sampled every 0.5 seconds with an 85 GiB stop. No memory stop, cold build, cache deletion or Mathlib compilation. Evidence: `/tmp/scene1-witt-choice-attempt{1,2}.metrics.log`, `/tmp/scene1-witt-choice-final-audit.metrics.log`, `/tmp/scene1-witt-choice-axioms.json`, `/tmp/scene1-witt-choice-static.json`.

### Actual bounded Teichmuller expansion of the Witt localization

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-WITT-TEICHMULLER-EXPANSION` | `WittTeichmullerExpansion.partialSum`, `partialSum_coeff`, `Expands`, `expands_iff_coeff`, `digits`, `expansion_unique`, `digits_unique`, `expands_map`, `expands_teichmuller_mul`; `Act1Scene1/WittTeichmullerExpansion.lean` | Joshi II `se:ff-rings` / W(O_F) into B and Mathlib TeichmullerSeries. Encodes the actual p-adic expansion by divisibility of all finite remainders. Proves this is equivalent to x.coeff(n)=c(n)^(p^n), giving uniqueness of the Witt vector and, over a perfect ring, of its digits. Proves naturality and exact multiplication by an arbitrary Teichmuller representative on the same expansion, using finite sums. | Scene1/Derived; proved finite-remainder expansion and uniqueness laws. |
| `JT-SCENE1-INITIAL-THETA-BOUNDED-WITT-EXPANSION` | `InitialThetaBoundedWittExpansion.wittInclusion`, `toAmbient`, `toAmbient_injective`, `HasBoundedExpansion`, `hasBoundedExpansion`, `integral_scaled_expansion`, `mem_range_of_hasBoundedExpansion`, `range_eq_boundedExpansions`; `Act1Scene1/IutInitialThetaBoundedWittExpansion.lean` | Joshi II W(O_F)-to-B algebraic source (511--512, 719--727), through the original actual tilt F and its norm valuation integers. Embeds the existing localization in Frac(W(F)). Proves its image consists exactly of z for which some p^m*z is an actual Witt vector y with Teichmuller digits uniformly bounded in the original F norm. The forward direction clears the original p*[varpi] denominator and explicitly scales the integral numerator digits by varpi^{-m}. The reverse direction multiplies bounded digits by a sufficiently high power of the original contracting varpi to construct a Witt vector in the original Ainf coefficient by coefficient; the unique expansion proves the required equality and the original localization units clear the denominators. | Scene1/Derived; proved actual image characterization by bounded Witt expansions. |

These are original proofs; no reference code was copied. The ambient fraction field is only used to compare actual algebraic elements; it is not identified with the paper's B or supplied with a replacement norm. Expansion and boundedness for actual localization elements are proved, not additional fields of D. The range characterization gives both directions; the p-power denominator is explicit, and uniqueness refers to the Teichmuller digits of each fixed scaled Witt vector. Independence under changing that p-power denominator, rho-norm estimates, multiplicativity of the rho norm, Frechet completion, and Tate-log convergence there remain to be established. No new Core assumptions, Prologue revision or target topology changes.

Acceptance (2026-10-21):

| task | exit | seconds | peak process-group RSS (KiB) |
| --- | ---: | ---: | ---: |
| Generic leaf attempt 1 | 1 | 71.351 | 4,232,384 |
| Generic leaf attempt 2 | 0 | 70.810 | 4,231,480 |
| Actual leaf attempt 1 | 1 | 169.112 | 9,110,712 |
| Generic leaf final (lint cleanup) | 0 | 68.316 | 4,224,556 |
| Actual leaf attempt 2 | 1 | 151.876 | 9,127,188 |
| Actual leaf attempt 3 | 0 | 159.519 | 9,113,252 |
| Checks.SceneBounds | 0 | 172.189 | 9,478,016 |
| Axioms.SceneBounds | 0 | 168.713 | 9,458,052 |
| Act1Scene1 aggregate | 0 | 154.873 | 9,264,048 |

Nine direct Lean tasks: six successful and three failed; successful time 794.420 seconds, failed time 392.339 seconds, total 1186.759 seconds; peak process-group RSS 9,478,016 KiB. The first generic diagnostic corrected inequality reversal and Frobenius-iteration normalization; the later successful generic pass removed unused characteristic instances and had an empty final log. The first actual task had an integral/tilt coefficient inference conflict and hit the default 200000 heartbeat limit (two diagnostic locations in that one task). Per the user policy, the theorem was raised to 1000000; integral digit types and the existing coefficient map were made explicit. The next actual failure was ordinary localization-map/zero-coefficient elaboration and use of a field-only homomorphism lemma on a Witt domain, with no further heartbeat timeout. These were corrected using the original inclusion and fraction-ring injectivity; the actual leaf then passed at 1000000 with an empty log. No mathematical assumptions changed. All 26 new declarations were checked individually and axiom-audited; all 3296 dependent entries used only `propext`, `Classical.choice`, `Quot.sound`, with one further axiom-free entry and no `sorryAx`. Static import audit covered 563 reachable project modules, with no forbidden imports or new proof holes. CPU 0--13, LEAN_NUM_THREADS=10, Lean -j1, one worker; process-group RSS sampled every 0.5 seconds with an 85 GiB stop. No memory stop, cold build, cache deletion or Mathlib compilation. TeichmullerSeries and related Witt dependencies had precompiled artifacts before the first diagnostic. Evidence: `/tmp/scene1-witt-bounded-expansion-attempt{1,2,3,4}.metrics.log`, `/tmp/scene1-witt-bounded-expansion-final-audit.metrics.log`, `/tmp/scene1-witt-bounded-expansion-axioms.json`, `/tmp/scene1-witt-bounded-expansion-static.json`.

### Teichmuller scaling stability of bounded Witt expansions

| source-id | declarations | source / fidelity | boundary / status |
| --- | --- | --- | --- |
| `JT-SCENE1-INITIAL-THETA-BOUNDED-WITT-EXPANSION-OPERATIONS` | `InitialThetaBoundedWittExpansion.hasBoundedExpansion_teichmuller_mul`; `Act1Scene1/IutInitialThetaBoundedWittExpansionOperations.lean` | Joshi II `se:ff-rings` / `W(O_F)⊂B` (511--512, 719--727), together with the actual finite-remainder expansion and Teichmuller multiplication law in `WittTeichmullerExpansion`. For a nonzero actual Teichmuller representative `r`, maps a bounded expansion with coefficient bound `C` to the expansion with digits `r*c n` and explicit bound `‖r‖*C`; the ambient denominator and p-power are unchanged. | Scene1/Derived; proved algebraic scaling stability. This is an input for later rho-norm representation independence, not a rho norm, Frechet completion, Tate-log convergence, or paper `B` identity. No reference code copied; no Core or Prologue change. |

Acceptance (2026-10-21):

| task | exit | seconds | peak process-group RSS (KiB) |
| --- | ---: | ---: | ---: |
| Leaf attempt 1 | 1 | 213.734 | 9,087,836 |
| Leaf attempt 2 | 0 | 204.564 | 9,096,844 |
| Act1Scene1 aggregate | 0 | 188.899 | 9,262,332 |
| Checks.SceneBounds | 0 | 172.583 | 9,478,360 |
| Axioms.SceneBounds | 0 | 146.637 | 9,458,392 |

The first leaf diagnostic was an ordinary duplicate local-instance/API elaboration error; the second leaf passed with an empty log. No heartbeat timeout or override occurred. The new declaration was checked individually and axiom-audited; its dependencies used only `propext`, `Classical.choice`, `Quot.sound`, with no `sorryAx`. Static import audit covered 564 reachable project modules, with no forbidden imports or proof holes. CPU 0--13, LEAN_NUM_THREADS=10, Lean -j1, one worker; process-group RSS sampled every 0.5 seconds with an 85 GiB stop. No Mathlib compilation was performed during the direct leaf/check/audit commands. Evidence: `/tmp/scene1-local-laws-IutInitialThetaBoundedWittExpansionOperations.log`, `/tmp/scene1-local-laws-Act1Scene1.log`, `/tmp/scene1-local-laws-SceneBounds.log`, `/tmp/scene1-bounded-ops-static.json`.
