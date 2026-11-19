# Local ramification facts for the Legendre tower

## English

Fix the Legendre curve `P.curve x` and a prime $\ell\ge 7$. Assume that the image of its mod-$\ell$ representation contains $\mathrm{SL}_2(\mathbf F_\ell)$. Assume also that $\ell$ does not divide the normalized valuation `qOrder w hw` of the Tate parameter at any place in `badAll`. The theorem `towerLocalFacts_of_primeData` uses these inputs to form `Pr` and takes $K_\ell$ to be its torsion field. [Theorem](../../../../Solutions/Source_TripodTowerLocalFacts.lean#L27)

Let $v$ be a finite place of $K_\ell$. Write $u$ for the place of the tripodal field below $v$ and $p$ for its residue characteristic. The three fields of `TowerLocalFacts` use the same relative index $e(v/u)$. [Fields](../../../../Solutions/Source_ReferenceIutTowerLocalFacts.lean#L124)

- `padicValNat_relRamIdx_le` bounds the $p$-adic valuation of $e(v/u)$ by `wildConst ℓ p`. This bound is 12, 2, 1 and 1 at $p=2,3,5,\ell$, respectively, and zero otherwise.
- `relRamIdx_eq_one` gives $e(v/u)=1$ when $p\notin\{2,3,5,\ell\}$ and $u$ satisfies `¬ IsBadTpdOf F E (VBadOf ℓ) u`. This means that no bad place of $F$ for `VBadOf ℓ` lies above $u$.
- `relRamIdx_le` gives $e(v/u)\le 30\ell$ when $p\notin\{2,3,5,\ell\}$.

For step (iii), also assume a place in `badAll` of residue characteristic distinct from $2$ and $\ell$, `AnabelianExistence AG TG`, and the universal core condition for the curve. Let `D` be the resulting initial theta data and `QI` its q-pilot inputs. Its torsion field `D.Kt` is $K_\ell$. Take any local theory `LT` on `D.Kt` and theta local data `TL` on that theory. Write `S = (TL.withBadChars QI).dst` for the distinguished set. It is the union of $\{2,3,5,\ell\}$, the q-pilot's bad residue characteristics, and the rational primes ramified in `D.Kt`. The theorem gives the bound below. [Step (iii)](../../../../Solutions/Source_TripodTowerLocalFacts.lean#L45) · [Bad characteristics](../../../../Solutions/Source_ReferenceIutThetaLocalBadChars.lean#L26) · [Distinguished set](../../../../Solutions/Source_ReferenceIutConcreteInvariants.lean#L62)

$$
\sum_{p\in S}\log p
\le 2D.\mathrm{dmod}\bigl(\mathrm{logDifferentDeg}(D.\mathrm{tripodalField})
  +D.\mathrm{logConductorDeg}\bigr)+5+\log\ell .
$$

MCP-CI leaf check `ci-022425-1c8a3663` passed. [Receipt](../receipts/round-ci-022425-1c8a3663-result.json)

## 中文

固定 Legendre 曲线 `P.curve x` 和素数 $\ell\ge 7$。假设其模 $\ell$ 表示的像包含 $\mathrm{SL}_2(\mathbf F_\ell)$，且任意 `badAll` 有限位的 Tate 参数的归一化赋值 `qOrder w hw` 均不被 $\ell$ 整除。`towerLocalFacts_of_primeData` 据此构造 `Pr`，并取其挠点域为 $K_\ell$。 [定理](../../../../Solutions/Source_TripodTowerLocalFacts.lean#L27)

设 $v$ 为 $K_\ell$ 的有限位，$u$ 为其下方的三足域有限位，$p$ 为其剩余特征。`TowerLocalFacts` 的三个字段使用同一个相对分歧指数 $e(v/u)$。 [字段](../../../../Solutions/Source_ReferenceIutTowerLocalFacts.lean#L124)

- `padicValNat_relRamIdx_le` 将 $e(v/u)$ 的 $p$ 进赋值限制在 `wildConst ℓ p` 以下。$p$ 为 $2,3,5,\ell$ 时上界依次为 $12,2,1,1$，其余为零。
- `relRamIdx_eq_one` 在 $p\notin\{2,3,5,\ell\}$ 且 `¬ IsBadTpdOf F E (VBadOf ℓ) u` 时给出 $e(v/u)=1$。后一条件表示 $F$ 中没有属于 `VBadOf ℓ` 所定义坏位集且位于 $u$ 上方的位。
- `relRamIdx_le` 在 $p\notin\{2,3,5,\ell\}$ 时给出 $e(v/u)\le 30\ell$。

步骤 (iii) 还假设 `badAll` 中存在剩余特征不同于 $2$ 和 $\ell$ 的位，并给定 `AnabelianExistence AG TG` 与该曲线的普遍核心条件。记所得初始 theta 数据为 `D`，其 q-pilot 输入为 `QI`，其挠点域 `D.Kt` 即 $K_\ell$。对 `D.Kt` 上任意局部理论 `LT` 及其局部 theta 数据 `TL`，指定素数集 `S = (TL.withBadChars QI).dst` 是 $\{2,3,5,\ell\}$、q-pilot 的坏位剩余特征集合和在 `D.Kt` 中分歧的有理素数集合的并。定理给出以下上界。 [步骤 (iii)](../../../../Solutions/Source_TripodTowerLocalFacts.lean#L45) · [坏位剩余特征](../../../../Solutions/Source_ReferenceIutThetaLocalBadChars.lean#L26) · [指定素数集](../../../../Solutions/Source_ReferenceIutConcreteInvariants.lean#L62)

$$
\sum_{p\in S}\log p
\le 2D.\mathrm{dmod}\bigl(\mathrm{logDifferentDeg}(D.\mathrm{tripodalField})
  +D.\mathrm{logConductorDeg}\bigr)+5+\log\ell .
$$

MCP-CI 叶检查 `ci-022425-1c8a3663` 通过。 [回执](../receipts/round-ci-022425-1c8a3663-result.json)

## 日本語

Legendre 曲線 `P.curve x` と素数 $\ell\ge 7$ を固定する。mod $\ell$ 表現の像が $\mathrm{SL}_2(\mathbf F_\ell)$ を含むと仮定する。さらに `badAll` の各素点で Tate パラメータの正規化付値 `qOrder w hw` が $\ell$ で割り切れないと仮定する。`towerLocalFacts_of_primeData` はこれらの入力から `Pr` を構成し、そのねじれ点体を $K_\ell$ とする。 [定理](../../../../Solutions/Source_TripodTowerLocalFacts.lean#L27)

$v$ を $K_\ell$ の有限素点、$u$ をその下にある三脚体の有限素点、$p$ をその剰余標数とする。`TowerLocalFacts` の三つのフィールドは同じ相対分岐指数 $e(v/u)$ を使う。 [フィールド](../../../../Solutions/Source_ReferenceIutTowerLocalFacts.lean#L124)

- `padicValNat_relRamIdx_le` は $e(v/u)$ の $p$ 進付値を `wildConst ℓ p` で上から抑える。$p=2,3,5,\ell$ での上界は順に $12,2,1,1$ であり、それ以外では零である。
- `relRamIdx_eq_one` は $p\notin\{2,3,5,\ell\}$ かつ `¬ IsBadTpdOf F E (VBadOf ℓ) u` なら $e(v/u)=1$ を与える。後者の条件は、`VBadOf ℓ` が定める $F$ の悪い素点で $u$ の上にあるものが存在しないことを表す。
- `relRamIdx_le` は $p\notin\{2,3,5,\ell\}$ なら $e(v/u)\le 30\ell$ を与える。

ステップ (iii) では、剰余標数が $2$ と $\ell$ のいずれとも異なる素点が `badAll` に存在すると仮定する。さらに `AnabelianExistence AG TG` と曲線の普遍的な核の条件を仮定する。得られる初期 theta データを `D`、その q-pilot の入力を `QI` とする。ねじれ点体 `D.Kt` は $K_\ell$ である。`D.Kt` 上の任意の局所理論 `LT` とその局所 theta データ `TL` に対し、指定素数の集合 `S = (TL.withBadChars QI).dst` は $\{2,3,5,\ell\}$、q-pilot の悪い素点の剰余標数、`D.Kt` で分岐する有理素数の和集合である。定理は次の上界を与える。 [ステップ (iii)](../../../../Solutions/Source_TripodTowerLocalFacts.lean#L45) · [悪い素点の剰余標数](../../../../Solutions/Source_ReferenceIutThetaLocalBadChars.lean#L26) · [指定素数の集合](../../../../Solutions/Source_ReferenceIutConcreteInvariants.lean#L62)

$$
\sum_{p\in S}\log p
\le 2D.\mathrm{dmod}\bigl(\mathrm{logDifferentDeg}(D.\mathrm{tripodalField})
  +D.\mathrm{logConductorDeg}\bigr)+5+\log\ell .
$$

MCP-CI の葉モジュール検査 `ci-022425-1c8a3663` は通過した。 [結果](../receipts/round-ci-022425-1c8a3663-result.json)
