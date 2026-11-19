# `finHeight_mapEquiv` 的独立读回

`gpt-6.2-sol` 审读者在全新上下文中读取冻结的 Lean 代码、所需定义和 `mission_auditor.md`。英文原稿和经核对的两份译文按原字节存档。三语主公式一致。 [英文原稿](readback.en.frozen.md) · [简体中文](readback.zh-Hans.md) · [日本語](readback.ja.md) · [来源记录](provenance.json) · [冻结材料](../frozen-materials.json)

| 核对项 | 三语中的对应 |
| --- | --- |
| 量词和结构 | 给定特征零且在有理数域上有限维的两个数域、任意域同构 $e\colon T\simeq T'$ 以及任意 $y\in T$。两侧是同构像与原元素的有限高度。 [目标声明](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcAdaptation_Reference_Iut_Tripod_FiniteHeightMapEquiv.lean:131) |
| 有限处与归一化 | 各有限处对应整数环的非零素理想。绝对值的底数是素理想商环的基数，指数为分母的素理想阶减去分子的素理想阶。零的绝对值为零。 [定义材料](../blind/FinitePlace.lean) · [赋值材料](../blind/AdicValuation.lean) |
| 正部对数与求和 | 两侧均在各自数域的全部有限处取正部对数的和。读回保留 $\log^+(0)=0$，以及空支集与无限支集时有限和取零的约定。取 $y=0$ 时两侧均为零。 [有限高度定义](../blind/FiniteHeight.lean) · [有限和定义](../blind/FiniteSum.lean) |

## 直观解释（非严格）

数域同构把一个有限处及其绝对值一起搬到另一个数域。每个求和项的值保持相同，因此整个有限部分的高度也相同。 [有限处绝对值等式](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcAdaptation_Reference_Iut_Tripod_FiniteHeightMapEquiv.lean:112) · [来源和使用](../SOURCE_LEDGER.md)
