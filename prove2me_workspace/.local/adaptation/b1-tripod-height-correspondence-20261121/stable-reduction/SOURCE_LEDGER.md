# 实际 Legendre 曲线的稳定约化

`AbcAdaptation.Tripod.stable_reduction_curveOf x h3 h5` 具有 `(curveOf x h3 h5).CurveArithmetic` 的 `stable_reduction` 字段所需类型。该字段由现有的 `CurveProviders.ofArithmetic` 接收。 [字段声明](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Concrete_CurveArithmetic.lean#L54) · [供应器入口](../../../../Solutions/Source_TripodProviderRepresentation.lean#L47)

| 模块 | 来源与消费者 |
| --- | --- |
| `Source_ReferenceIutStableModel.lean` | `StableOdd.lean:39–220`。复用目标的 `IsIntegralModel` 及其 `b₄` 引理和既有有限处范数转换。提供奇特征分支和 Raynaud 判据共用的 `hasStableReductionAt_of_isStableModel`。 |
| `Source_TripodStableOdd.lean` | `StableOdd.lean:259–371`。参数整时用 Legendre 模型，参数不整时以实际曲线域中的 √λ 转到 λ⁻¹。复用 `valuation_two_eq_one_of_ne`。覆盖全部奇剩余特征，包括 3。 |
| `Source_ReferenceIutTorsionFlex.lean` | `StableTwo.lean:61–317` 中的 flex、三分点多项式和整性证明。输入为非无穷远的三挠点，输出为正规形与 Newton 下降所需的等式。 |
| `Source_ReferenceIutThreeTorsionNormalForm.lean` | `StableTwo.lean:195–232, 323–517`。证明正规形有稳定模型，包含两种单位情形及按 (v(B)) 下降。 |
| `Source_ReferenceIutStableThreeTorsion.lean` | `StableTwo.lean:529–633`。从两个独立有理三挠点得到 Raynaud 判据的有限处结论。 |
| `Source_TripodStableTorsionPoints.lean` | `StableTwo.lean:649–700` 的实际曲线下降部分。先把几何基转到实际模型，再由 `six_torsion_rational_curveOf` 下降到实际曲线域。显式给出两点被 3 杀死、各自非零、互异且互非相反数。 |
| `Source_TripodStableReduction.lean` | `StableTwo.lean:704–711`。剩余特征 2 调用有理三挠点判据，其余有限处调用奇特征分支。 |

原证明使用 iut 提交 `07cb1da58f6d428a670dbb5dd6093d428bcbcdd8` 中的定义域和约化谓词。目标实现保持这些结论的目标命名空间版本，并把完整 `CurveProviders` 构造前需要的 √λ 和三挠点直接取在实际 `curveOf` 上。 [奇特征源](../../../../../refer/iut/Iut/Tripod/StableOdd.lean#L343) · [Raynaud 判据源](../../../../../refer/iut/Iut/Tripod/StableTwo.lean#L615) · [全处组合源](../../../../../refer/iut/Iut/Tripod/StableTwo.lean#L704)

## MCP-CI 回执

| 回执 | 输入 SHA-256 前缀 | 退出码 | 墙钟秒 | CPU 秒（用户态 + 系统态） | 峰值 RSS GiB | 诊断 |
| --- | --- | ---: | ---: | ---: | ---: | --- |
| [ci-026806-255b0e22](ci-026806-255b0e22.result.json) | `ea84e1a9736afcc2` | 0 | 47.44 | 47.73（5.56 + 42.17） | 7.58 | 无诊断 |
| [ci-026807-1b1f0693](ci-026807-1b1f0693.result.json) | `62fbc4f0373972ca` | 1 | 21.85 | 20.79（2.26 + 18.53） | 4.16 | 三挠点下降的基变换定义域透明度及自然数倍乘失败 |
| [ci-026808-0a3ec4f0](ci-026808-0a3ec4f0.result.json) | `e64672e498e7d841` | 1 | 49.92 | 47.88（6.10 + 41.78） | 7.57 | 缺少 `sqrtLam_sq` 的直接导入 |
| [ci-026809-022635a2](ci-026809-022635a2.result.json) | `a74e55d2f28196e5` | 0 | 50.66 | 48.90（8.42 + 40.48） | 7.64 | 无诊断 |
| [ci-026811-45275e54](ci-026811-45275e54.result.json) | `ddc5c34e80da48f5` | 0 | 59.08 | 56.54（6.00 + 50.54） | 7.57 | 导入原平方根等式 |
| [ci-026812-b042ebf0](ci-026812-b042ebf0.result.json) | `1bba8169a28edbd5` | 0 | 58.23 | 57.52（8.29 + 49.23） | 7.61 | 无诊断 |
| [ci-026814-bfe4f9ee](ci-026814-bfe4f9ee.result.json) | `d4eae2d0d466ee52` | 0 | 29.85 | 28.94（3.76 + 25.18） | 4.18 | 统一定义域并显式写出 6 = 2 · 3 |
| [ci-026818-2dd0b0c5](ci-026818-2dd0b0c5.result.json) | `fd6662eb396bc059` | 0 | 48.78 | 48.68（5.26 + 43.42） | 7.58 | 无诊断 |
| [ci-026820-ffff1e4a](ci-026820-ffff1e4a.result.json) | `9eff5d5ca3cd28f8` | 0 | 40.75 | 40.20（4.10 + 36.10） | 7.57 | 无诊断 |
| [ci-026822-54e0e125](ci-026822-54e0e125.result.json) | `5deba34ae28a3406` | 0 | 58.08 | 57.29（4.06 + 53.23） | 7.91 | 四项公理审查通过 |

联合审查导入 Checks、ImportAudit、Act1Scene1 与 AxiomAudit。独占回执的快照 ID 为空，物理内存取进程树 RSS，PSS 与 degraded 标记未知。四个端点仅依赖 `propext`、`Classical.choice` 和 `Quot.sound`。 [审查源码](ReviewTripodStableReduction.lean) · [独立中、英、日读回](independent-readback.md)
