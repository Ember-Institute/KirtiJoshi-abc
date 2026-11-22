# 三足域与有限高度归一化

固定来源为 refer/iut 提交 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8，许可证为 Apache 2.0。对实际供应的 Legendre 曲线，三足中间域与点域同构。曲线的 $j$ 不变量来自三足中间域，经该同构成为点域上的 Legendre $j$。有限高度求和、扩张缩放和同构不变性一起给出曲线供应器高度等于 $j$ 不变量的有限高度除以点域次数。该公式由本地的 auxiliaryHeight 恒等式及双向高度比较消费。 [源定理](../../../../refer/iut/Iut/Tripod/Height.lean#L603) · [本地归一化](../../../Definitions/Def_AbcAdaptation_Reference_Iut_Tripod_HeightNormalization.lean#L23) · [本地消费者](../../../Solutions/Source_TripodProviderAuxiliaryHeight.lean#L16)

源端使用 Lean 4.35.0-rc3 重放并导出原始表达式，目标端为 Lean 4.33.1 和 Mathlib 0df444a360eaa60ab8c11dca51a86af692955474。归一化定理的源命令与目标命令逐字一致。迁移审查在完整内核类型和证明项上核对三足域识别、$j$ 传输和归一化主定理。$j$ 传输的公开绑定位置一致，展开表达式中的内部绑定位置有差异，完整类型通过内核定义相等。归一化证明中的域自作用实例在审查重放时由该域的标准忠实标量作用实例接替。在两份证明均通过完整目标类型检查后，使用证明无关性比较。 [域与 j 审查](field-and-j/cross-version-result-v3.json) · [归一化审查](normalization/cross-version-result-v2.json) · [旧稿和来源摘要](platform/dependencies.json)

CurveProviders.tate、localData、h 的完整类型和定义值也通过内核比较。实际 Tate 输入的七条手写或生成声明均通过完整类型和值的跨版本审查。均匀化元两条证明复核了其调用的 `qOrder` 生成证明。局部参数存在性证明从目标定义实际传给 `Exists.choose` 的证明取名，确认源的 `tateParameter._proof_1` 对应目标的 `tateParameter._proof_5`。两侧完整表达式在内核中定义相等，审查了旧完备化 API 的对应与 JExistence 参数顺序。 [供应器审查](provider-height/cross-version-result.json) · [Tate 输入源端回执](tate-inputs-drafts/ci-026142-15bb9e12.result.json) · [均匀化元存在性](tate-inputs-drafts/uniformizer-proof/uniformizer-proof-review.result.json) · [所选均匀化元的证明](tate-inputs-drafts/uniformizer-proof-2/uniformizer-proof-2-review.result.json) · [参数存在性对应](tate-inputs-drafts/parameter-norm/existence-proof-review.result.json.gz) · [两个定义及 j 等式](tate-inputs-drafts/remaining-supply/remaining-supply-review.result.json.gz)

平台复用了私有 FieldInvariant，并私有发布 FieldLegendreFacts、FieldIdentification、FieldTransport 和 JTransport。h_eq_finHeight_div 使用三项已证的有限高度公式。提交 93da123b-c25a-4eff-b7e3-dbeee8b2bd29 获 ACCEPTED，节点 3ba94824-130b-402a-bc95-e768360bb56d 回读为 Proved。 [平台依赖](platform/platform-import-readback.json) · [验收](platform/receipts/h_eq_finHeight_div/verification-result.json) · [节点终态](platform/receipts/h_eq_finHeight_div/final-item.json)

独立审读使用剥离注释后的 Lean 陈述与定义。三语保留局部 Tate 和式按曲线定义域次数归一化，以及有限 $j$ 高度按点域次数归一化。 [审读输入](blind/Target.lean.txt) · [中文](independent-readback/zh-Hans.md) · [English](independent-readback/en.md) · [日本語](independent-readback/ja.md)

## MCP-CI 回执

| 任务 | 退出码 | 墙钟秒 | CPU 秒（用户态 + 系统态） | 峰值 RSS GiB | 诊断 |
| --- | --- | --- | --- | --- | --- |
| [ci-026080-a7a01815](receipts/ci-026080-a7a01815.result.json) | 0 | 155.65 | 100.28（4.46 + 95.82） | 4.72 | 三个曲线供应器高度定义通过 |
| [ci-026081-96ebef55](receipts/ci-026081-96ebef55.result.json) | 1 | 155.16 | 100.89（5.18 + 95.71） | 4.81 | $j$ 传输陈述内部绑定位置不同 |
| [ci-026082-98e75d76](receipts/ci-026082-98e75d76.result.json) | 1 | 156.91 | 101.96（7.90 + 94.06） | 4.99 | 归一化定理证明引用已迁移的库实例及未导入的数域代数性实例 |
| [ci-026090-1e772788](receipts/ci-026090-1e772788.result.json) | 0 | 72.61 | 70.31（3.14 + 67.17） | 4.10 | 平台归一化解答及陈述通过 |
| [ci-026098-250e9320](receipts/ci-026098-250e9320.result.json) | 1 | 156.97 | 153.49（8.17 + 145.32） | 4.83 | 核对了 $j$ 传输完整类型，map_legendreJ 映射到错误的命名空间 |
| [ci-026099-0a6109f5](receipts/ci-026099-0a6109f5.result.json) | 0 | 163.06 | 158.94（13.79 + 145.15） | 5.03 | 归一化定理的完整类型和值通过 |
| [ci-026109-15534529](receipts/ci-026109-15534529.result.json) | 0 | 280.36 | 273.03（8.85 + 264.18） | 4.87 | 三足域识别和 $j$ 不变量传输的完整类型和值通过 |

回执均为独占工作区，快照 ID 为空。资源使用调度器的进程树 RSS，PSS 和 degraded 标记未知。通过的审查仅报告 propext、Classical.choice 和 Quot.sound。原生七模块的 Checks、ImportAudit、Act1Scene1 和 AxiomAudit 已由 ci-019679-3acf973e 验收，该任务覆盖 84 个声明。 [原生项目回执](../main-chain-open-20261116/b1-tripod-all-review-v260-result.json)

## Tate 输入生成证明

以下审查使用独占工作区 `3da69dc8` 和 Lean `4.33.1`。PSS 和 degraded 标记未知。

| 任务 | 退出码 | 墙钟秒 | CPU 秒（用户态 + 系统态） | 峰值 RSS GiB | 诊断 |
| --- | ---: | ---: | ---: | ---: | --- |
| [`ci-026250-cdc3100d`](tate-inputs-drafts/uniformizer-proof/ci-026250-cdc3100d.result.json) | 1 | 68.31 | 68.09（4.39 + 63.70） | 4.58 | 审查工具的 `nameField` 缺少 `do`，阻止元程序执行 |
| [`ci-026263-81548b47`](tate-inputs-drafts/uniformizer-proof/ci-026263-81548b47.result.json) | 0 | 64.02 | 64.23（4.92 + 59.31） | 4.60 | 补上 `do` 后，完整类型、证明值和公理检查通过 |
| [`ci-026273-6f179b6c`](tate-inputs-drafts/parameter-norm/ci-026273-6f179b6c.result.json) | 1 | 69.06 | 69.02（5.85 + 63.17） | 4.65 | 对应整数顺序实例缺少映射，Tate 参数生成证明中的证据项数目有差异 |
| [`ci-026283-d6fd14d8`](tate-inputs-drafts/uniformizer-proof-2/ci-026283-d6fd14d8.result.json) | 0 | 109.56 | 109.80（5.59 + 104.21） | 4.62 | 所选均匀化元的完整类型和证明项通过 |
| [`ci-026293-dd4511f3`](tate-inputs-drafts/parameter-norm/ci-026293-dd4511f3.result.json) | 1 | 148.59 | 148.49（6.95 + 141.54） | 4.67 | `one_lt_norm_j` 完整内核比较通过，Tate 参数生成证明仍有类型差异 |
| [`ci-026334-f6579098`](tate-inputs-drafts/parameter-norm/ci-026334-f6579098.result.json) | 0 | 72.11 | 72.13（5.26 + 66.87） | 4.60 | 按实际 `Exists.choose` 调用确定对应，存在性证明检查通过 |
| [`ci-026342-89288c59`](tate-inputs-drafts/remaining-supply/ci-026342-89288c59.result.json) | 0 | 121.41 | 120.32（7.40 + 112.92） | 4.76 | `tateParameter`、`tateParameter_tateJ`、`tateInputs` 的完整类型与值通过 |

## 实际 Tate 输入的源端审查

独占审查 ci-026142-15bb9e12 在 Lean 4.35.0-rc3 核对了七条原始声明的完整类型和值，并生成十四份归一化证书。源端仅使用 Lean 标准公理。任务退出码为 0，墙钟 555.29 秒，CPU 467.74 秒（用户态 21.15 秒，系统态 446.59 秒），进程树峰值 RSS 为 9.23 GiB，PSS 未取得。诊断是引用参考工程的一条生成引理。同一七条声明的目标端结果见上方对应表。 [审查回执](tate-inputs-drafts/ci-026142-15bb9e12.result.json) · [源端证书](tate-inputs-drafts/source-common-core-certificates.json.gz) · [目标声明候选](tate-inputs-drafts/target-candidates.json)

完整表达式与大型证书以 gzip 归档。复现审查前将相应文件解压至配置记录的路径。 [三足域与 j 传输表达式](field-and-j/cross-version-expressions-v3.jsonl.gz) · [归一化表达式](normalization/cross-version-expressions-v2.jsonl.gz)

## Joshi II 的平方和与 P7 的统一素数下界

平方和引理复用已验收的 `sum_affine_quadratic`。四个声明分别给出平方系数、代入 Tate 根对数后的系数、负对数的逐处严格下界，以及总和为负时的有限加权平均比较。以 $m=(\ell-1)/2$ 代入，奇素数 $\ell\ge5$ 足以得到严格数值界。Joshi III 定理 9.11.1（Form 2）仍明列奇素数 $\ell\gg0$。接入规范高高度估计的条件性草稿为每个 $K,d$ 接收统一的 $N(K,d)$，由 Northcott 有限性和既有素数选择将该下界传给同一 P7 见证上的比较。论文区域、包络体积、带符号的 q-pilot 和局部估计的接合仍开放。 [平方和 Lean 草稿](joshi-ii-square-logs/Source_JoshiIINormalizedSquareLogs.lean) · [既有求和恒等式](../../../Theorems/Thm_AbcAdaptation_Reference_Iut_sum_affine_quadratic.lean) · [三语稿及原文页码](c2-prime-bound/readback.md)

原文核对使用 2026-11-21 取得的 arXiv PDF。II v3 的 SHA-256 为 `a25e58456673d905f6be328773926ec8a5dbb419fe278ca478827f163ccdf4af`，III v4 的 SHA-256 为 `86a92ca893e774e1ea591ed9825a30627f3f19d8df0b26b7f5855dc0923f0429`。 [Joshi II](https://arxiv.org/pdf/2303.01662v3#page=28) · [Joshi III](https://arxiv.org/pdf/2401.13508v4#page=127)

三个任务均在 `/home/admin-wsl/Coq/abc/prove2me_workspace` 独占运行，HEAD 为 `9cf23097`，快照 ID 为空。调度器记录进程树峰值 RSS，PSS 和 degraded 标记未知。各目标的 `actual_arguments` 均为 `lean` 加所列单文件。所有显式公理输出仅含 `propext`、`Classical.choice` 和 `Quot.sound`，审查通过且无 `sorryAx`。项目联合审查导入了 `Checks`、`ImportAudit`、`Act1Scene1` 和 `AxiomAudit`。回执的范围是列出的独立草稿及联审文件。 [项目联审源文件](c2-prime-bound/ReviewCorollary22PrimeBoundProject.lean#L8)

| MCP-CI 回执 | 输入文件与 SHA-256 前缀 | 退出码 | 墙钟秒 | CPU 秒（用户态 + 系统态） | 峰值 RSS GiB | 诊断 |
| --- | --- | ---: | ---: | ---: | ---: | --- |
| [ci-026499-66ab10f9](c2-prime-bound/ci-026499-66ab10f9.result.json) | `ReviewCorollary22PrimeBound.lean` · `d59204c50bbecf91` | 0 | 254.81 | 254.17（27.78 + 226.39） | 7.64 | 第 297 行建议将 `simpa` 换为 `simp` |
| [ci-026517-9dc5bb10](c2-prime-bound/ci-026517-9dc5bb10.result.json) | `ReviewCorollary22PrimeBoundProject.lean` · `988aba8a62256e96` | 0 | 318.92 | 313.19（28.90 + 284.29） | 8.18 | 第 301 行为同一条 lint 建议 |
| [ci-026524-eff346a4](joshi-ii-square-logs/ci-026524-eff346a4.result.json) | `Source_JoshiIINormalizedSquareLogs.lean` · `bb66ec1398f52dfd` | 0 | 87.90 | 84.71（1.32 + 83.39） | 1.99 | 第 29 行 `ring` 未执行，第 39 行有 tactic 组合 lint 建议 |


## 论文右端接入同一 P7

`withRHSData` 保留初始 θ 数据、q-pilot 及 Theorem 1.10 的十二个算术不变量。算术证书的四项证明在新右端上复用。只替换 θ 区域时，原容器、测度与包络系统仍可使用，新的逐包包含证明给出所需 `thetaPilot_subset`。 [右端运输与局部估计](joshi-ii-square-logs/Source_ReferenceIutPaperRHSTransport.lean)

`PaperRHSSupplyAtLeast` 接收同一选中点和素数的实际初始数据、局部数据、q-pilot 和塔算术。它保留模域次数、高度、判别式与导子关系，供应新的论文右端、来源谓词及新右端的局部估计。规范高高度推论 2.2 使用这一供应函数和独立的论文比较条件。供应函数的范围是 `ConcreteThetaDataExistence` 给出的所有满足关系的具体见证。论文标准点、区域、测度及比较的证明保留为显式输入。 [规范 P7 和 c2 的组合](c2-prime-bound/Source_TripodCanonicalCorollary22PaperRHS.lean)

| MCP-CI 独占审查 | 输入 SHA-256 前缀 | 退出码 | 墙钟秒 | CPU 秒（用户态 + 系统态） | 峰值 RSS GiB | 诊断 |
| --- | --- | ---: | ---: | ---: | ---: | --- |
| [ci-026674-84dc49e4](joshi-ii-square-logs/ci-026674-84dc49e4.result.json) | `88948eb6dd10edcf` | 0 | 147.45 | 145.57（6.01 + 139.56） | 7.97 | 四项公理输出，无诊断 |
| [ci-026706-0e022888](c2-prime-bound/ci-026706-0e022888.result.json) | `ca729e482cadbe4e` | 0 | 158.79 | 154.40（28.28 + 126.12） | 8.22 | 十一项公理输出，既有 `simpa` lint 建议 |

两项审查均导入 Checks、ImportAudit、Act1Scene1 与 AxiomAudit。全部显式公理输出仅含 `propext`、`Classical.choice`、`Quot.sound`。进程树 RSS 来自调度器，PSS 和 degraded 标记未知。

## Joshi III 的归一化乘积与规范 P7 的有限处包体积

令 $m=(\ell-1)/2$，$M=\mathbb Q(j(E))$，并令 $B$ 为 P7 的坏模域处集。对 $v\in B$，取同一 P7 数据选出的代表处 $s(v)$、Tate 根 $r_v=\mathrm{TL.qroot}(s(v))$ 和相对局部次数 $d_v=[K_{t,s(v)}:M_v]$。以 $V_{j,p}$ 表示其第 $j$ 个标签集在有限素数 $p$ 的包络对数体积，$S$ 表示局部数据的有限坏特征集。Lean 专门化保留原见证的等式 `X = concreteVariantData D LT TL QI`，并给出

$$
\log\!\left(\prod_{j=1}^m\prod_{v\in B}
  \|r_v\|^{(j/m)^2/(d_v[M:\mathbb Q])}\right)
=\frac{1}{m^2}\sum_{j=1}^m\sum_{p\in S}V_{j,p}.
$$

包权重是各坐标处权重的乘积。原有限处包体积公式将未缩放坐标的权重求和为一，得到 $\sum_{p\in S}V_{j,p}=j^2 X.\mathrm{qPilot.lhs}$。代表处公式把同一个带符号的 q-pilot 写成 $\sum_{v\in B}\log\|r_v\|/(d_v[M:\mathbb Q])$。通用引理显式使用模域映射的相容等式，P7 专门化从原点数据取得它。 [包权重](../../../Solutions/Source_ReferenceIutConcreteContainer.lean#L157) · [有限处公式](../../../Solutions/Source_ReferenceIutCor312FiniteThetaHullVolume.lean#L224) · [代表处公式](../../../Solutions/Source_ReferenceIutCor312RepresentativeQPilot.lean#L87) · [P7 专门化](../../../Solutions/Source_ReferenceIutCor312RepresentativeProduct.lean#L117)

乘积使用 Joshi III 式 (9.9.4)–(9.9.6) 的平方指数和 P7 的完整次数归一化。局部权重见 Joshi III §9.10.5，全局次数可写成 Mochizuki III 注记 3.1.1(ii) 的完整模域纤维次数和。原论文的 Bloch–Kato 标准点范数、Form 2 的全纯包络及其体积仍待与 P7 数据逐项识别。 [Joshi III 的乘积](<../../../../refer/JoshiTeich/Arithmetic Teichmuller Spaces 3.tex#L3467>) · [Joshi III 的局部权重](<../../../../refer/JoshiTeich/Arithmetic Teichmuller Spaces 3.tex#L3552>) · [模域纤维权重](../../../Solutions/Source_ReferenceIutCor312PointRepresentativeWeight.lean#L21)

四个任务均从 `/home/admin-wsl/Coq/abc/prove2me_workspace` 以独占模式检查单文件。HEAD 为 `9cf23097`，快照 ID 为空。内存列来自调度器的进程树 RSS，PSS 和 degraded 标记未知。联合审查导入 `Checks`、`ImportAudit`、`Act1Scene1` 和 `AxiomAudit`。显式公理输出仅含 `propext`、`Classical.choice` 和 `Quot.sound`，`no_sorryAx` 检查通过。 [联合审查源码](joshi-iii-representative-product/ReviewCor312RepresentativeProduct.lean)

| MCP-CI 回执 | 输入 SHA-256 前缀 | 退出码 | 墙钟秒 | CPU 秒（用户态 + 系统态） | 峰值 RSS GiB | 诊断 |
| --- | --- | ---: | ---: | ---: | ---: | --- |
| [ci-026631-b9378258](joshi-iii-representative-product/ci-026631-b9378258.result.json) | `cd415337fc121c65` | 1 | 70.98 | 70.57（5.90 + 64.67） | 7.57 | 类型类搜索未取得模域到挠点域所需的标量塔 |
| [ci-026641-3d10738a](joshi-iii-representative-product/ci-026641-3d10738a.result.json) | `3d80df25e3ddb8c0` | 1 | 149.73 | 147.66（5.76 + 141.90） | 7.55 | 储存的标量塔使用继承的标量作用，实例与指定模域映射不符 |
| [ci-026663-f887862b](joshi-iii-representative-product/ci-026663-f887862b.result.json) | `1f95f8142c7bf8a6` | 0 | 195.21 | 193.75（6.07 + 187.68） | 7.67 | 无诊断 |
| [ci-026672-29e2ba52](joshi-iii-representative-product/ci-026672-29e2ba52.result.json) | `fa80d762ea12d09d` | 0 | 150.95 | 150.25（7.60 + 142.65） | 8.17 | 无诊断，五条声明公理审查通过 |

### 标准 p-adic 复数范数

同一个 Tate 根由有限完成域等距嵌入其代数闭包，再运到标准 $\mathbb C_p$。标准范数的 $[K_{t,s(v)}:\mathbb Q_p]$ 次幂等于原 Haar 范数。次数塔约去 $d_v$，因此上式的标准范数指数为 $(j/m)^2[M_v:\mathbb Q_p]/[M:\mathbb Q]$。换算适用于任意局部理论的代表元乘积，有限处包对数体积恒等式使用具体局部理论，保留模域映射相容性假设。 [Lean 源码](../../../Solutions/Source_ReferenceIutCor312RepresentativePadicProduct.lean) · [独立中、英、日读回](joshi-iii-representative-product/standard-cp-norm-readback.md)

采用 Joshi III §4.5 的第 $m$ 个坐标作为平方指数的基准。式 (9.9.4) 印出的下标为 $1$，在 $0<|r|<1$、$m>1$ 时与该式的 $j=1$ 分支冲突。论文标准点的 $H^1_e$ 类、Bloch–Kato 映射及其有限处和无穷处加权体积仍需核对。 [原文及权重核对](joshi-iii-representative-product/paper-weight-crosscheck.md)

| MCP-CI 回执 | 输入 SHA-256 前缀 | 退出码 | 墙钟秒 | CPU 秒（用户态 + 系统态） | 峰值 RSS GiB | 诊断 |
| --- | --- | ---: | ---: | ---: | ---: | --- |
| [ci-026731-7f47e5ca](joshi-iii-representative-product/ci-026731-7f47e5ca.result.json) | `b06aed934742ca9c1` | 1 | 189.04 | 188.61（45.46 + 143.15） | 8.33 | 范数幂引理在内核用完 heartbeat，后续引用无法解析 |
| [ci-026751-a2c6295a](joshi-iii-representative-product/ci-026751-a2c6295a.result.json) | `2898e550aa58d54bc` | 0 | 97.39 | 97.57（7.07 + 90.50） | 8.18 | 拆出代数闭包等距性及完成保范数性，默认 heartbeat 通过，无诊断 |
| [ci-026766-f44b6bd1](joshi-iii-representative-product/ci-026766-f44b6bd1.result.json) | `1f95f8142c7bf8a6` | 0 | 51.82 | 52.10（5.82 + 46.28） | 7.69 | 生成代表元乘积的独立导入产物 |
| [ci-026771-5c61fe61](joshi-iii-representative-product/ci-026771-5c61fe61.result.json) | `a14b57a41d238538` | 0 | 65.78 | 65.22（5.62 + 59.60） | 7.67 | 生成标准范数换算的首个独立导入产物 |

联合审查实际检查 `ReviewCor312RepresentativePadicProduct.lean`，导入 Checks、ImportAudit、Act1Scene1 和 AxiomAudit。七项显式公理输出仅含 `propext`、`Classical.choice`、`Quot.sound`，`no_sorryAx` 检查通过。各回执均来自独占工作区，快照 ID 为空。内存为调度器的进程树 RSS，PSS 和 degraded 标记未知。 [联合审查源码](joshi-iii-representative-product/ReviewCor312RepresentativePadicProduct.lean)

### 逐处比较值与有限包体积

在同一 P7 选定的有限处 $s(v)$，用实际完成域中的普通对数定义 $L_{s(v)}=log_p(1+p^*r_v)/p^*$。Tate 根非负阶，故范数至多为一。归一化对数范数律给出 $\|L_{s(v)}\|=\|r_v\|$。经同一完成域嵌入并消去正局部次数幂，这一等式也适用于标准 $\mathbb C_p$。显式给定逐处比较值及其与 $L_{s(v)}$ 的等式，即可代入代表元乘积及有限包对数体积公式。实际 $H^1_e$ 成员资格及 Bloch–Kato 比较等式仍须在论文载体上证明。 [Lean 源码](../../../Solutions/Source_ReferenceIutCor312RepresentativeComparisonLog.lean) · [独立中、英、日读回](joshi-iii-representative-product/comparison-log-readback.md) · [类与归一化来源](joshi-iii-representative-product/bloch-kato-comparison.md)

| MCP-CI 回执 | 输入 SHA-256 前缀 | 退出码 | 墙钟秒 | CPU 秒（用户态 + 系统态） | 峰值 RSS GiB | 诊断 |
| --- | --- | ---: | ---: | ---: | ---: | --- |
| [ci-026780-90533cbf](joshi-iii-representative-product/ci-026780-90533cbf.result.json) | `04163edc34105d7f` | 0 | 54.34 | 54.02（4.85 + 49.17） | 7.67 | 复验供比较值使用的公开嵌入及范数律 |
| [ci-026785-ea2e9895](joshi-iii-representative-product/ci-026785-ea2e9895.result.json) | `f4dd11598a02295e` | 1 | 54.17 | 53.41（4.51 + 48.90） | 8.09 | 局部素数实例重名，有限处嵌入的自然数投影换算失败 |
| [ci-026792-c4787faa](joshi-iii-representative-product/ci-026792-c4787faa.result.json) | `37ca687d4f557cc1` | 0 | 51.76 | 51.32（4.45 + 46.87） | 8.14 | 区分局部实例，并用嵌入的 `map_natCast` 法则。八项公理审查通过 |
| [ci-026802-4a1bed20](joshi-iii-representative-product/ci-026802-4a1bed20.result.json) | `f4cce0924792d2b0` | 0 | 62.27 | 61.82（5.31 + 56.51） | 7.66 | 生成独立导入产物 |

联合审查实际检查 `ReviewCor312RepresentativeComparisonLog.lean` 并导入 Checks、ImportAudit、Act1Scene1 和 AxiomAudit。八项输出只有 `propext`、`Classical.choice` 和 `Quot.sound`。各任务使用独占工作区及空快照 ID，PSS 和 degraded 标记未知。

### Form 2 的逐点阈值与固定族下界

Form 2 沿用 Joshi II 的平方和估计。在第 $m$ 个坐标作标准点的解释下，数值估计的统一阈值为 $\ell\ge5$，由参考 `c2` 的 $\ell\ge7$ 满足。Form 2 的完整来源供应仍需齐备。给定每个适用点的论文供应阈值 $N_x$ 及公共界 $N_x\le N(K,d)$，`PaperRHSSupplyAtLeast.of_pointwise` 将同一 P7 实参及 $N_x\le N(K,d)\le X.\ell$ 传给逐点供应。Joshi 与 P7 的支持差异仍须证明逐处对应。 [精确接口](c2-prime-bound/Source_TripodCanonicalCorollary22PaperRHS.lean#L15) · [论文及窗口核对](c2-prime-bound/form2-prime-threshold.md) · [独立中、英、日读回](c2-prime-bound/paper-rhs-pointwise-readback.md)

[ci-026800-0077539e](c2-prime-bound/ci-026800-0077539e.result.json) 独占检查 `ReviewTripodCanonicalCorollary22PaperRHSPointwise.lean`，输入哈希前缀 `af8512b614cb249e`，退出码 0。墙钟 86.02 秒，CPU 85.35 秒（24.17 + 61.18），进程树峰值 RSS 8.22 GiB，PSS 与 degraded 标记未知。审查导入 Checks、ImportAudit、Act1Scene1 和 AxiomAudit。十三项输出只有 Lean 标准公理，第 305 行有既有 `simpa` 提示。

### 同一 P7 代表处的环境 Kummer 类

在实际有限完成域中，主单位 $1+p^*r$ 由同一 Tate 根构造。它经过普通 Kummer 映射给出连续 $H^1(G,mathbb Q_p(1))$ 中的类。环境对数在这类上取 $log_p(1+p^*r)$，除以 $p^*$ 后与逐处归一化值相等。把该值代入标准 $mathbb C_p$ 范数乘积，得到同一有限包对数体积恒等式。论文的 $H^1_e$ 成员资格及真实 Bloch–Kato 比较等式仍开放。 [Lean 源码](../../../Solutions/Source_ReferenceIutCor312RepresentativeKummerLog.lean) · [来源与消费者](joshi-iii-representative-product/kummer-log-sources.md) · [中文](joshi-iii-representative-product/kummer-log-readback/zh-Hans.md) · [English](joshi-iii-representative-product/kummer-log-readback/en.md) · [日本語](joshi-iii-representative-product/kummer-log-readback/ja.md)

| MCP-CI 回执 | 输入 SHA-256 前缀 | 退出码 | 墙钟秒 | CPU 秒（用户态 + 系统态） | 峰值 RSS GiB | 诊断 |
| --- | --- | ---: | ---: | ---: | ---: | --- |
| [ci-026815-82c3bf43](joshi-iii-representative-product/ci-026815-82c3bf43.result.json) | `4c502eece135c0e3` | 1 | 73.08 | 74.14（25.29 + 48.85） | 7.83 | 内核归一化等式在 whnf 用完默认 heartbeat，随后的引用缺失 |
| [ci-026823-2f0240e3](joshi-iii-representative-product/ci-026823-2f0240e3.result.json) | `da265fc226dc80fb` | 1 | 51.08 | 51.35（6.25 + 45.10） | 7.71 | 展开定义后，重写目标仍含 let |
| [ci-026824-8f02e03a](joshi-iii-representative-product/ci-026824-8f02e03a.result.json) | `bade4a811ca92185` | 0 | 49.42 | 50.82（8.01 + 42.81） | 7.76 | 先约简 let 再局部重写，默认 heartbeat 通过并生成产物 |
| [ci-026827-16c29d38](joshi-iii-representative-product/ci-026827-16c29d38.result.json) | `c6a9782340948dd3` | 0 | 52.76 | 51.54（4.28 + 47.26） | 7.88 | 六项公理审查通过，无诊断 |

联合审查导入 Checks、ImportAudit、Act1Scene1 与 AxiomAudit，六项输出仅含 `propext`、`Classical.choice` 和 `Quot.sound`。物理内存取调度器的进程树 RSS，PSS 和 degraded 标记未知。 [审查源码](joshi-iii-representative-product/ReviewCor312RepresentativeKummerLog.lean)
