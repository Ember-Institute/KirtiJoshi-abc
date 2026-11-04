# Scene1 进度总览

### 状态判定

| 标记 | 状态 | 使用条件 |
| --- | --- | --- |
| 🟢 | 已闭合 | 本行精确义务已证明，所需实际输入已落实，相关验收已通过 |
| 🔵 | 条件性完成 | 定理及其显式条件已验证，但条件尚未从目标实际数据全部推出 |
| 🟡 | 部分完成 | 已有可引用子结果，仍缺构造、比较、身份等式或整单验收 |
| ⚪ | 未建立 | 尚无满足本行要求的已验收构造或证明 |
| 🔴 | 路线已排除 | 已证明某条具体路线不成立；必须保留排除范围及所用条件 |

“已闭合”只对该行声明的范围有效。局部构造闭合，不自动关闭所属最终闸门。
给定 `InitialThetaData` 后的实际适配，不等于从 arithmetic seed 构造出完整真实模型；
actual carrier 上的定理，不自动成为论文 carrier 上的定理。
必要充分条件已证明，也不表示实际数据满足该条件。

不按文件数、声明数、S1 编号或复选框数计算总完成百分比。
四个闸门的关闭数只表示验收状态，不表示工作量比例或剩余时间。

## 当前结论

| 项目 | 当前值 |
| --- | --- |
| 更新日期 | 2026-11-04（Asia/Shanghai） |
| 已提交数学基线 | `b2ac96f`：加入独立标准 p-only 全半径 rho completion carrier；此前的 bounded rho 比较、单半径 completion 与范数幂律分别见 `82ea173`、`89f4cc5` |
| 最近局部进展 | 标准全半径 completion 叶、Scene1 聚合、Checks、Axioms、ImportAudit 均已通过；正在起草实际↔标准全半径 product-level 环等价，尚未编译 |
| Scene1 整体 | **未完成；最终闸门关闭 0/4；15 项父义务全部开放** |
| 当前推进位置 | 将原始 inclusion 后的系数范数提前交给抽象局部化接口，已把多个具体子叶降至约 8.7 GiB；下一步把单半径 completion 等价沿半径重参数组装为全半径 product-level 等价 |
| 尚未闭合的比较边界 | 完整 actual→standard rho value 幂律已在 `82ea173` 通过，单半径 completion 比较已在 `89f4cc5` 通过；旧 named `ambientInclusion` 方块、原 bounded inclusion 的 completion 相容包装和全半径比较仍另行验收 |
| 完整值定理验收 | `final_named_value_pow`：136.3 秒，峰值 `9098108 KiB`（约 8.677 GiB），退出码 0；早先 11.606 GiB 的超时草稿已由新 presentation 路线替代 |
| 最新成功聚合验收 | 标准全半径 carrier：Scene1 峰值 `9442316 KiB`（约 9.005 GiB），Checks `9547676 KiB`（约 9.105 GiB），Axioms `9524288 KiB`（约 9.083 GiB），ImportAudit `9434712 KiB`（约 8.998 GiB） |
| 内存边界 | 单叶验收上限 16 GiB；当前监控停止线 15 GiB，总编译内存上限 100 GiB。低于内存线但超时的构建仍不算通过 |
| 尚未接通的主要连接 | 共同真实 geometry producer、global holomorphoid、论文 Fréchet `B`/ρ-norm、H¹ₑ/BK、paper representatives、跨来源 collation、theta locus/`thetaVolume` 与最终 Corollary 3.12 |
| Prologue 边界 | `R5`；四项 source laws 仍由 Scene1 producer 从共同真实来源证明 |

阅读顺序：先看四个闸门，再看当前路线，最后看最近单元变化与内存记录。
总体义务以[开发计划](开发计划.V1Act1Scene1.md)、[证明义务台账](具有明确参考来源指示的证明义务.md)
和[来源台账](../ArithmeticTeichmullerSpaces/SOURCE_LEDGER.md)为准；本轮构建证据见
[Scene1Witt比较内存.jsonl](Scene1Witt比较内存.jsonl)。

## 四个最终验收闸门

G1–G4 对应[开发计划 §3](开发计划.V1Act1Scene1.md#3-未完成义务按最终闸门分解)。
每行的“已有结果”概括子结果，不表示该闸门已经关闭。

| 闸门 | 当前状态 | 已有结果 | 关闭所需的剩余工作 | 证据入口 |
| --- | --- | --- | --- | --- |
| **G1：目标与归一化冻结** | 🟡 部分完成 | raw/degree-normalized 换算、weighted source sum、grouped volume 会计、actual qProduct lower bound 和条件性最终消费者已有 | 在同一 paper carrier 上冻结 q-term、局部/全局次数、`p*`、`2ℓ`、无穷处项和最终目标，证明 paper normalization 身份 | [计划 G1](开发计划.V1Act1Scene1.md#g1目标符号和归一化) |
| **G2：共同真实来源模型装配** | 🟡 部分完成 | 给定 `InitialThetaData` 后，actual Tate/q-root、局部 tilt/Fontaine/Witt、perfectoid 局部法律及实际与标准 carrier 比较已有 | 从同一 arithmetic seed 产生 geometry、完整 `InitialThetaData/TateFamily`、holomorphoid、period/H¹ₑ/BK 和四项 source laws，完成论文 `B` 身份 | [计划 G2](开发计划.V1Act1Scene1.md#g2共同真实来源和-producer)；[父义务台账](具有明确参考来源指示的证明义务.md) |
| **G3：论文处集与重数会计** | 🟡 部分完成 | actual representatives、prime fibers、selected/omitted mass、Galois fiber 权重和 grouped volume 会计已有 | 识别论文处集和 `L'` representatives，闭合 multiplicity、residue/inertia degree、paper weights 与 mixed-moduli descent | [计划 G3](开发计划.V1Act1Scene1.md#g3论文处集代表和重数) |
| **G4：实际 theta-volume 与最终连接** | 🟡 部分完成 | ordinary-log/Kummer hull、Haar/cost、actual volume 比较、period-ring 和 Tate kernel 的局部链已有 | 接通 H¹ₑ/BK、theta-value、不同 untilt/holomorphoid、paper theta locus 与 `thetaVolume`，在同一归一化下完成最终 proof term | [计划 G4](开发计划.V1Act1Scene1.md#g4论文-theta-locusvolume-和最终-corollary) |

qLogTerm 的字面符号问题按既有决定暂作笔误处理，等待作者回复后再讨论。
本总览不把它列为当前停工项；G1 的其他归一化和来源义务仍保留。

四个闸门关闭后，还须通过[计划 §6 的构建与审计](开发计划.V1Act1Scene1.md#6-构建与审计规则)，
才能宣布 Scene1 完成。单个单元的编译、审计或推送通过，不等于最终验收完成。

## 当前证明路线

下图展示当前构造与待完成连接，不是完整 Lean 导入图。
实线表示已有局部构造或已通过叶编译的连接；虚线表示仍需证明、装配或整单验收。
绿色只覆盖节点写明的局部范围。

```mermaid
flowchart TD
    S["输入：arithmetic / Tate seed"]
    P["未建立：共同 geometry producer"]
    D["输入：给定 InitialThetaData"]
    T["已闭合：actual tilt 与独立标准 tilt<br/>整数环等价及 local-degree 范数幂律"]
    E["已闭合：bounded Witt 环等价<br/>独立 p-only 标准 rho value"]
    W["已闭合：标准 p-only 全半径<br/>completion carrier"]
    O["叶编译通过：原 inclusion 后<br/>系数范数幂律"]
    N["叶编译通过：numerator 幂律<br/>denominator 幂律与 quotient 幂律"]
    A["叶编译通过：两侧<br/>localization presentation 值公式"]
    V["已闭合：完整 value_pow<br/>原 bounded 环与原范数；82ea173"]
    Q["已闭合：单半径 completion 等价<br/>双向连续与范数幂律；89f4cc5"]
    U["进行中：actual↔standard<br/>全半径 product equivalence"]
    F["已闭合：actual period ring<br/>completion、Frobenius、theta 与 Tate kernel"]
    H["已闭合：actual H¹ / ordinary log<br/>hull 与局部定量界"]
    B["未建立：论文 Fréchet B 身份<br/>global holomorphoid、H¹ₑ/BK"]
    R["部分完成：actual representatives<br/>paper 处集、重数与跨来源 collation"]
    L["未建立：paper theta locus<br/>及 thetaVolume 身份"]
    C["待完成：Corollary 3.12<br/>G1–G4 与整体审计"]

    S -.-> P
    P -.-> D
    D --> T
    T --> E
    E --> O
    E --> W
    O --> N
    E --> A
    N --> V
    A --> V
    V --> Q
    W -.-> U
    Q -.-> U
    U -.-> B
    D --> F
    D --> H
    V -.-> B
    F -.-> B
    H -.-> B
    D --> R
    B -.-> R
    R -.-> L
    B -.-> L
    L -.-> C

    classDef done fill:#dcfce7,stroke:#15803d,color:#14532d;
    classDef partial fill:#fef3c7,stroke:#b45309,color:#78350f;
    classDef open fill:#f3f4f6,stroke:#6b7280,color:#111827;
    class T,E,O,W,N,A,V,Q,F,H done;
    class R partial;
    class S,D,P,U,B,L,C open;
```

当前 value 路线已通过局部化 presentation 和系数范数比较证明完整商值幂律。
它没有把旧 named `ambientInclusion` 方块作为已证明前提；该方块仍单独开放。
独立标准 bounded Witt carrier 已扩展为 p-only 全半径 completion carrier，并通过 Scene1、Checks、Axioms、ImportAudit；
它仍尚未被识别为论文 Fréchet `B`。实际↔标准全半径 product equivalence 只完成设计，尚未编译验收。

### 关键子结果与缺口

| 路线位置 | 状态 | 已证明范围或验收缺口 | 所属闸门／证据 |
| --- | --- | --- | --- |
| 条件性最终定理 | 🔵 条件性完成 | `cor312_of_scene1_data` 与 canonical actual-hull consumer 已有证明；完整真实输入、来源法律和 paper identity 仍须产生 | G1/G2/G4；[计划 §2.3](开发计划.V1Act1Scene1.md#23-scene1-条件性消费者与会计) |
| Actual Tate/q-root 与局部会计 | 🟢 已闭合 | 给定数据后的 q 参数、q-order、根、有限支撑和 raw/degree-normalized 恒等式已有 | G1/G3；[Scene1 聚合](../ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1.lean) |
| Actual representatives 与处集会计 | 🟢 已闭合 | actual carrier 内的 representative image、prime support、finite fibers、omitted mass 和 grouped volume 已有；paper 身份另计 | G3；[计划 §2.3](开发计划.V1Act1Scene1.md#23-scene1-条件性消费者与会计) |
| Actual period-ring 与 Tate kernel | 🟢 已闭合 | actual bounded Witt/ρ-norm、completion、Frobenius、theta、twisted integral representatives、full Tate kernel 与实际正合列已有 | G2/G4；[period-ring 边界](#period-ring-路线的边界) |
| Actual H¹、ordinary log 与 hull | 🟢 已闭合 | actual rational H¹、带 integral 来源的 Kummer 像、ordinary log、tensor hull、Haar/cost 和实际定量界已有 | G4；[父义务台账](具有明确参考来源指示的证明义务.md) |
| 标准 tilt 与 integer-ring bridge | 🟢 已闭合 | 标准 fraction field 的范数、完备性、代数闭性、拓扑比较和整数环 bridge 已有；比较保留 local-degree 范数幂律 | G2；`GeometricTiltNorm.lean`、`IutInitialThetaPadicTiltTopology.lean` |
| 独立标准 bounded Witt rho value | 🟢 已闭合 | 仅依赖 p 的 expansion、localization、presentation-independent value、指定半径范围内有限性、零点分离和素数校准已提交 | G2/G4；`7e40f65`；[标准 value](../ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/PadicWittRhoValue.lean) |
| 标准 p-only 全半径 completion carrier | 🟢 已闭合 | 由单半径标准 completion 组装全半径产品 carrier，含坐标范数、稠密嵌入、分离性和坐标收敛；叶、Scene1、Checks、Axioms、ImportAudit 已通过 | G2/G4；`b2ac96f`；[全半径 carrier](../ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/PadicWittAllRadiusCompletion.lean) |
| 实际↔标准全半径 product equivalence | ⚪ 未建立 | 已确定用 `ENNReal.powOrderIso` 重参数和各半径 completion ring equivalence 组装；新文件正在起草，尚未编译或登记审计 | G2/G4；`IutInitialThetaPadicWittRhoProductEquiv.lean`（待验收） |
| 共享 carrier 比较与 `ambientEquiv` | 🟢 局部闭合 | 系数、field-Witt 和 fraction ambient 等价已有 proof term；相关叶有低于 16 GiB 的成功记录，范围不含 bounded ambient inclusion 方块 | G2/G4；`d4a05cd`；[ambient 等价叶](../ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/IutInitialThetaPadicWittRhoAmbientEquiv.lean) |
| 原 inclusion 后的系数范数幂律 | 🟢 叶验收通过 | `coefficient_inclusion_norm_pow` 已在默认预算下通过独立叶编译；新接口直接保存两侧 inclusion 后的系数范数 | G2/G4；[系数范数叶](../ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/IutInitialThetaPadicWittRhoCoefficientNorm.lean) |
| 分子、分母与商值幂律 | 🟢 叶验收通过 | `numerator_value_pow`、`denominator_value_pow`、`quotient_value_pow` 分别通过默认预算叶编译；最终局部化值定理也已在 `82ea173` 通过 | G2/G4；[商值叶](../ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/IutInitialThetaPadicWittRhoQuotientValue.lean) |
| 两侧 localization presentation 值公式 | 🟢 叶验收通过 | actual arbitrary-contraction 与 standard Away presentation 的值公式已有成功编译记录 | G2/G4；[presentation 叶](../ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/IutInitialThetaWittRhoLocalizationPresentation.lean) |
| Actual→standard 完整 rho 幂律 | 🟢 已闭合 | 原 bounded `ringEquiv` 上的 `value_pow` 在默认 heartbeat 下通过，保留原范数、标准独立收缩元和半径 rho^localDeg；聚合、审计和推送已完成 | G2/G4；`82ea173`；[最终值声明](../ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/IutInitialThetaPadicWittRhoValuePow.lean) |
| 旧 named `ambientInclusion` / `toAmbient` 比较 | ⚪ 未建立 | 已测试的具体交换图仍未通过；ambient 环等价和新系数范数叶不能代替该命名映射的相容证明 | G2/G4；[计划中的构建边界](开发计划.V1Act1Scene1.md#2026-11-03named-ambient-inclusion-的内核阻塞已复核) |
| 论文 `B`、H¹ₑ/BK 与 global holomorphoid | ⚪ 未建立 | actual/local 构件尚未识别为论文要求的 carrier、拓扑、子空间及比较映射 | G2/G4；[父义务台账](具有明确参考来源指示的证明义务.md) |
| Paper representatives、theta locus 与 `thetaVolume` | 🟡 部分完成 | actual 会计和 hull 可复用；paper carrier、跨来源 transport、locus/volume 身份及最终共同装配仍缺 | G2/G3/G4；[计划 §3](开发计划.V1Act1Scene1.md#3-未完成义务按最终闸门分解) |

“已闭合”只覆盖本行的精确范围。`82ea173`、`89f4cc5` 和 `b2ac96f` 的 Scene1、Checks、
Axioms、ImportAudit 与推送均已通过；这些局部单元不关闭论文 `B` 身份或父义务。
`integralKummerSubmodule` 是带 integral 来源的有理像载体；特定像类非零不表示一般 integral H¹
系数映射单射。actual ordinary log 仍须与论文 Bloch–Kato log 比较。

### Period-ring 路线的边界

| 层次 | 状态 | 已有结果 | 仍保留的目标 |
| --- | --- | --- | --- |
| Actual bounded Witt 与 ρ-norm | 🟢 已闭合 | 有界 Witt ring、半径 norm、乘法性和 completion 构造已有 | 与论文对象、来源及归一化的身份 |
| 全半径 completion、Frobenius 与 theta | 🟢 已闭合 | actual completion、各半径求值、Frobenius、theta、Tate-log 和 principal-unit period 局部链已有 | 论文 `B`/ρ-norm、holomorphoid 与 H¹ₑ/BK 身份 |
| Twisted integral 代表与 Tate kernel | 🟢 已闭合 | 指定实际 twisted 解可缩放到原始 `A_inf`；full Tate kernel、唯一实际 `ℚₚ` 标量分类与正合列已有 | 论文 carrier、topology 及来源比较 |
| Actual ρ=1 `B⁺` candidate | 🟢 已闭合 | actual 单位球 candidate 的 Frobenius 自同构和 `PadicInt` 结构已有 | 论文 `B⁺` 标记、Galois 作用、global holomorphoid 与标量相容 |
| 环带指数延拓 | 🟡 部分完成 | overlap 法律、闭区间有界逼近和条件性消费者已有 | 精确 Witt 代表或全半径延拓；固定正内半径的单位界不足以推出整性 |
| Actual / standard bounded rho 比较 | 🟢 已闭合 | 原环等价上的完整 `value_pow` 已验收，并已扩展到单半径 completion、双向连续和完成范数幂律 | 原 bounded inclusion 的 completion 相容包装、全半径/Fréchet 比较及论文 `B` 身份 |
| 标准全半径 completion carrier | 🟢 已闭合 | p-only 全半径产品 carrier、坐标收敛和审计入口已验收 | 实际半径重参数、product-level completion equivalence 及论文 Fréchet `B` 身份 |

### 已排除路线：避免重复投入

| 具体路线 | 状态与排除范围 | 当前保留方向 | 证据 |
| --- | --- | --- | --- |
| 从任意抽象 AG/TG 接口自动产生 universal geometry producer | 🔴 反模型排除仅凭现有抽象字段无条件产生 witness；不评价真实 orbicurve | 为真实 geometry 证明 cartesian、covering 和 local 来源法律 | [计划 2026-10-23](开发计划.V1Act1Scene1.md#2026-10-23任意无约束-agtg-的统一-producer-反模型) |
| Actual contracting q-root 直接充当旧 theta base | 🔴 q-root 范数小于 1，与旧 period/normalization/transfer 的非负 logVolume 要求冲突 | 另一 theta lift、different untilt 或 negative-log cost | 计划 N1；S1.243/S1.321 |
| Signed Haar log-volume 直接等同旧 `VolumeTransfer` | 🔴 正长度 ordinary-log hull 的 signed log-volume 为负，排除指定直接身份 | 证明 actual `-log(volume)` cost 的 paper identity | 计划 N2；S1.321/S1.322/S1.406 |
| 指定 representative certificates 与 reference q-pilot equality 联合使用 | 🔴 已证明指定证书组合与 selected/reference strict gap 不相容 | 从 paper source 重审 representatives、omitted mass 和 degree/weight | [计划 2026-10-29](开发计划.V1Act1Scene1.md#2026-10-29canonical-degree-one-representative-certificate-的乘积不相容性) |
| 固定正内半径上的单位界直接推出 `A_inf` 整性 | 🔴 实际环带反例排除只凭该单位界取得 integral 代表；不排除附带 Frobenius 方程的识别 | 使用实际 Frobenius 方程，或构造全半径延拓 | [计划 2026-10-30](开发计划.V1Act1Scene1.md#2026-10-30固定环带的双侧单位界不足以推出-a_inf-整性) |

这些结果只排除表中具体路线，不构成 Corollary 3.12 的反例。
内核超时和超内存属于构建失败证据，不标为数学上的“路线已排除”。

## 最近单元变化与内存记录

本轮把映射后的系数范数作为抽象接口参数，在构造比较数据时证明其幂律；下游直接消费已保存的
函数及法律。随后从系数范数推出 Teichmüller digits 与 weighted value 幂律，再与 denominator 幂律组合。
这条路线保留原始两侧范数、独立 p-only 标准收缩元及原 bounded 环等价，没有增加自由比较假设。

已验收的完整值目标为：令 `d = localDeg(w)`、`B = InitialThetaPadicBoundedWittComparison`，
对 `ρ ≠ 0`、`ρ ≠ ⊤` 及原 actual bounded Witt 元素 `x`，证明

```text
PadicWittRhoValue.value p ρ (B.ringEquiv D w x) ^ d
  = InitialThetaWittRhoValue.value D w (ρ ^ d) x
```

### 最新受控构建

记录采用每 0.5 秒采样的进程组 RSS；15 GiB 是监控停止线，16 GiB 是单叶验收上限。
下表为本轮代表性运行，成功行均使用默认 heartbeat。资源值属于相应源码版本的那次运行，
不表示后来修改源码或依赖后已经自动重验。

| 构建记录 label | 范围 | 耗时 | 峰值 RSS（KiB / GiB） | 结果 |
| --- | --- | --- | --- | --- |
| `mapped_data_coefficient_observers` | 泛型 observer 局部化接口 | 57.9 秒 | `4216116` / 4.021 | 退出码 0 |
| `generic_coefficient_value_function` | 泛型系数范数→完整 numerator 值函数 | 77.6 秒 | `4506444` / 4.298 | 退出码 0 |
| `actual_mapped_data_coefficient_observers` | Actual/standard 比较数据专门化 | 119.4 秒 | `9119608` / 8.697 | 退出码 0 |
| `coefficient_norm_observer_projection` | 原 inclusion 后系数范数幂律 | 144.2 秒 | `9094516` / 8.673 | 退出码 0 |
| `numerator_observer_value_function` | Numerator 值幂律 | 142.9 秒 | `9102332` / 8.681 | 退出码 0 |
| `observer_final_denominator_power` | Denominator 幂律 | 148.8 秒 | `9092852` / 8.672 | 退出码 0 |
| `rho_quotient_value_microleaf` | Quotient 值幂律 | 137.3 秒 | `9096292` / 8.675 | 退出码 0 |
| `rho_localization_presentations_final` | 两侧局部化 presentation 值公式 | 125.2 秒 | `9149096` / 8.725 | 退出码 0 |
| `rho_value_pow_current_direct_calc` | 旧完整 `value_pow` 草稿 | 204.6 秒 | `12169780` / 11.606 | 退出码 1；Kernel deterministic timeout，后已被新路线替代 |
| `final_named_value_pow` | 最终完整 `value_pow` | 136.3 秒 | `9098108` / 8.677 | 退出码 0；已随 `82ea173` 验收推送 |
| `completion_equiv_coe_ringhom_final` | 单半径 completion 等价与 Source coe 相容 | 134.8 秒 | `9109084` / 8.687 | 退出码 0；已随 `89f4cc5` 验收推送 |
| `scalar_coeff_norm_1m_diagnostic` | 旧单声明 100 万 heartbeat 诊断 | 344.1 秒 | `15746664` / 15.017 | 触及 15 GiB 监控线后停止；设置已撤回，后续 observer 路线已使该系数目标通过 |
| `standard_all_radius_completion` | 标准 p-only 全半径 completion 叶 | 79.4 秒 | `5544044` / 5.287 | 退出码 0 |
| `standard_allradius_scene1` | Scene1 全半径聚合 | 137.4 秒 | `9442316` / 9.005 | 退出码 0 |
| `standard_allradius_checks` | Checks 审计入口 | 164.0 秒 | `9547676` / 9.105 | 退出码 0 |
| `standard_allradius_axioms` | Axioms 审计入口 | 155.4 秒 | `9524288` / 9.083 | 退出码 0 |
| `standard_allradius_importaudit` | ImportAudit 审计入口 | 140.1 秒 | `9434712` / 8.998 | 退出码 0 |

### 历史资源边界

| 单元或尝试 | 已记录结果 | 判定 |
| --- | --- | --- |
| 早期整体 rho comparison | `104733916 KiB`，约 99.88 GiB，退出码 137 | 未验收 |
| 早期 field bridge | `111356192 KiB`，约 106.20 GiB，退出码 137 | 未验收 |
| 早期 field-Witt inclusion | `44895852 KiB`，约 42.82 GiB，退出码 137 | 未验收 |
| 拆分和接口调整后的 coefficient、field-Witt、`ambientEquiv` 等叶 | 多个成功运行低于 16 GiB | 对应局部叶通过；完整值定理另由 `82ea173` 验收 |
| 旧 named ambient inclusion | 多次约 11.6 GiB 触发 deterministic timeout；提高预算的受控诊断达到 15 GiB 停止线 | 仍未通过；不由这些日志单独判断数学真伪或具体 Kernel 缺陷 |
| 旧最终值定理的点态 wrapper、等式方向调整和直接 calc 组合 | 多次在约 11.6 GiB 触发 deterministic timeout | 新 presentation/裸函数 transfer 路线已得到最终验收；旧草稿保留为历史失败证据 |

命令、耗时、峰值、退出码、错误和停止原因见[机器可读记录](Scene1Witt比较内存.jsonl)。
此前已将临时构建目录中尚未归档的 57 条记录补入该文件，并按 label/log 去重；人工停止的
重复或依赖过期运行明确记为人工停止，不记为自然退出或内存停止。
早期约 100 GiB 运行的摘要保存在[开发计划](开发计划.V1Act1Scene1.md#2026-11-02rho-比较的-kernel-资源边界与载体接口调整)中；
它们不具备后来受控运行的同等监控条件。一次不限内存诊断授权已使用，后续继续遵守单叶上限。

## 后续顺序

最终 presentation/value 推导已移到抽象函数或载体层，并通过具体原始声明验收。
标准 p-only 全半径 carrier 已完成并通过四个入口；下一步是把实际↔标准单半径
completion equivalence 沿 `ρ ↦ ρ ^ localDeg(w)` 组装成 product-level equivalence，再决定是否限制到闭包 carrier。
product-level 文件尚未编译，不能登记为新成果。
已有记录表明，旧具体 wrapper、`trans` 或 `calc` 不能替代已验收的新 presentation 路线。

product-level completion equivalence 通过后，还须按依赖顺序重验最终源码、必要消费者、
Scene1 聚合、Checks、Axioms、ImportAudit、来源及资源记录，再提交推送。上述局部单元即使完成，
也只关闭 bounded/full-radius 比较的局部范围；Fréchet completion 与论文 `B` 身份仍须证明。

Scene1 总体按[计划 §5](开发计划.V1Act1Scene1.md#5-执行顺序)推进共同真实 geometry producer、
holomorphoid、period/H¹ₑ/BK 和论文 `B`，随后闭合 paper representatives、multiplicity、
mixed-moduli descent、G1 归一化及 G4 theta-volume。
只有同一真实输入上的 G1–G4 与最终整体审计全部通过，才能宣布 Scene1 完成。
