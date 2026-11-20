# English

Let $P$ be an actual Legendre curve provider, $K$ a compactly bounded subset, and $d$ a natural number. For a tripod point $x$ with $x\in K$ and $[\mathbb Q(x):\mathbb Q]\leq d$, `curveInputs_height_eq` states

$$\bigl((P.\mathrm{curve}(x)).\mathrm{localHeightData}(P.\mathrm{arith}(x),P.\mathrm{tate}(x))\bigr).\mathrm{height}=P.h(x).$$

Both sides use the same provider curve, arithmetic certificate, and Tate inputs. The proof is definitional equality. The membership argument matches the complete `CurveInputs.height_eq` field, but the proof does not use it: the equality holds at every tripod point for the supplied $P$.

The source constructor chooses `h := P.h` and the provider's actual curves and inputs. `toCorollary22Inputs` forwards this equality as `localData_height`. The theorem `Corollary22Inputs.c2` then uses it to identify the local height of its selected curve with the global height in its threshold and conclusion. This equality computes the provider height; it does not construct a provider or a complete `CurveInputs` record. Mochizuki's IUT IV, Corollary 2.2(i), defines the all-primes q-height through the normalized degree of the divisor determined by local q-parameters. That definition supplies the paper context for retaining the same local data throughout.

# 简体中文

设 $P$ 是实际的 Legendre 曲线供应数据，$K$ 是紧致有界子集，$d$ 是自然数。对满足 $x\in K$ 及 $[\mathbb Q(x):\mathbb Q]\leq d$ 的 三足点 $x$，`curveInputs_height_eq` 陈述

$$\bigl((P.\mathrm{curve}(x)).\mathrm{localHeightData}(P.\mathrm{arith}(x),P.\mathrm{tate}(x))\bigr).\mathrm{height}=P.h(x).$$

等式两边使用同一组供应数据中的曲线、算术证书与 Tate 输入。证明是定义等式。成员关系参数用于匹配完整的 `CurveInputs.height_eq` 字段，但证明并不使用它；对给定的 $P$，此等式在每个 三足点都成立。

源码构造器选取 `h := P.h`，并使用 供应数据指定的实际曲线与输入。`toCorollary22Inputs` 将该等式作为 `localData_height` 传递。随后 `Corollary22Inputs.c2` 用它把所选曲线的局部高度与阈值、结论中的全局高度对应起来。该等式计算 供应数据给出的高度，尚未构造供应数据 或完整的 `CurveInputs` 记录。望月新一《集合论多宇宙间算术 Teichmüller 理论》第四篇推论 2.2(i) 将包含全部有限处的 q-高度定义为局部 q-参数所确定除子的归一化次数。这一原文定义说明了为何始终保留同一组局部数据。

# 日本語

$P$ を実際の Legendre 曲線の供給データ、$K$ をコンパクト有界部分集合、$d$ を自然数とする。$x\in K$ かつ $[\mathbb Q(x):\mathbb Q]\leq d$ を満たす tripod の点 $x$ に対し、`curveInputs_height_eq` は

$$\bigl((P.\mathrm{curve}(x)).\mathrm{localHeightData}(P.\mathrm{arith}(x),P.\mathrm{tate}(x))\bigr).\mathrm{height}=P.h(x)$$

を主張する。両辺は同じ供給データの曲線、算術的証明書、Tate 入力を用いる。証明は定義上の等式である。所属の引数は完全な `CurveInputs.height_eq` フィールドの型に合わせるためにあり、証明自体では使わない。与えられた $P$ に対し、この等式はすべての tripod の点で成り立つ。

ソースの構成子は `h := P.h` とし、供給データに含まれる曲線と入力を選ぶ。`toCorollary22Inputs` はこの等式を `localData_height` として渡す。その後、`Corollary22Inputs.c2` が、選んだ曲線の局所高さを閾値と結論に現れる大域的な高さと同一視する。この等式は 供給データによる高さを計算するものであり、供給データや完全な `CurveInputs` レコードを構成しない。望月新一の「宇宙際 Teichmüller 理論」第 IV 論文、系 2.2(i) は、すべての有限素点を含む q-高さを、局所 q-パラメータが定める因子の正規化次数として定義する。この原文の定義が、同じ局所データを一貫して使う数学的背景となる。

[Local height field](../../../../Solutions/Source_TripodCurveInputsHeightFields.lean#L27) · [Source height field](../../../../../refer/iut/Iut/Tripod/CurveFacts.lean#L503)
