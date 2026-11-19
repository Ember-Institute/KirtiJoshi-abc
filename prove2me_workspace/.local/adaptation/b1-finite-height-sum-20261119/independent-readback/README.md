# 有限高度求和的独立读回

`gpt-6.2-sol` 审读者在全新上下文中收到冻结的 Lean 代码、必要定义和 `mission_auditor.md`。英文原稿逐字归档，中文和日文采用项目对照表中的「素元」。中文同时沿用本单元已有的「良好约化」。审读模型、原稿、译文修订和冻结输入的摘要见归档记录。 [英文原稿](readback.en.frozen.md) · [简体中文](readback.zh-Hans.md) · [日本語](readback.ja.md) · [归档记录](provenance.json) · [冻结输入清单](../frozen-materials.json) · [术语记录](/home/admin-wsl/Coq/abc/docs/三语术语名词关键对照.md:44)

| 核对项 | 三语中的对应 |
| --- | --- |
| 曲线供应数据 | 有理数域代数闭包中的所有参数均进入 \(3\) 挠点和 \(5\) 挠点有限性的量词，包括 \(0,1\)。算术条件、每个素数的表示数据及目标等式均使用去掉 \(0,1\) 的三足点。 [供应接口](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcAdaptation_Reference_Iut_Tripod_CurveProviders.lean:28) |
| 曲线及其定义域 | \(F_x\) 由点坐标、三个选定平方根以及 \(3\) 挠点与 \(5\) 挠点的仿射坐标生成。\(E_x\) 是这一定义域上的 Legendre 曲线。 [域定义](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcAdaptation_Reference_Iut_Tripod_CurveOfFieldsData.lean:64) · [曲线构造](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcAdaptation_Reference_Iut_Tripod_CurveOf.lean:25) |
| 算术和表示 | 十项算术条件及模素数表示的四个字段均已读回。还原了层间有限处关系、\(\ell\ge7\) 与 \(p(v)\ne2\) 的位置，以及开核和基下伽罗瓦作用。 [算术条件](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcAdaptation_Reference_Iut_Concrete_CurveArithmetic.lean:50) · [表示字段](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcAdaptation_Reference_Iut_Concrete_CurveData.lean:54) |
| 归一化 | 分子按乘法约化有限集求 \(\operatorname{ord}_w(q_w)f(w)\log p(w)\) 的和，分母为正的 \([F_x:\mathbb Q]\)。右端在同一数域的全部有限处上取绝对值的正部对数之和。 [局部数据装配](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcAdaptation_Reference_Iut_Concrete_LocalHeightDataAssembly.lean:39) · [有限高度定义](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_TripodCanonicalHighHeightInputs.lean:19) |
| 退化情形 | 读回包括空的乘法约化有限集、\(j(E_x)=0\) 时对数取零，以及 Mathlib 有限和的约定。原定理用乘法约化有限集覆盖有限高度的支集，因此此处的非零项确实有限。 [支集步骤](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcAdaptation_Reference_Iut_Tripod_FiniteHeightSum.lean:43) |
| 分母消去 | 辅助引理涵盖任意指标类型、有限集和各项局部数据条件。它在 \(d\ge1\) 时把 \(dH\) 写成加权和。 [辅助引理](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcAdaptation_Reference_Iut_Tripod_FiniteHeightSum.lean:14) |

## 直观说明

乘法约化处的 Tate 参数阶给出 \(j\) 不变量的正部对数。良好约化处的这项贡献为零。因此把局部高度的归一化分母乘回去，就能在曲线的定义域上将两边写为同一个有限和。 [来源与验收](../SOURCE_LEDGER.md) · [论文原文与定位](../paper-context.json)
