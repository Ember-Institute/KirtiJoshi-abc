# Uniformization transport to the Takeuchi pairs

## 中文

`of_closure_eq` 把同一个一致化映射用于生成同一子群的 Nielsen 生成元。`of_signs` 把它用于符号可以分别改变的生成元。本地证明向生成子群加入中央矩阵 $-I$ 得到 `pmGroup`。因为 $-I$ 在上半平面上作用为恒等，加入它或改变生成元的符号都保持轨道。

设 $g$ 同时共轭两个生成元。若 $\det g>0$，`conj_pos` 用 $z\mapsto\pi(g^{-1}\cdot z)$ 一致化原曲线。若 $\det g<0$，`conj_neg` 对该映射的两个坐标取复共轭，得到复共轭曲线的一致化。负行列式分支中，上半平面的 $g^{-1}$ 作用与目标坐标都包含一次复共轭，因此复合映射仍是全纯的。

`uniformizes_takeuchiPair_of_conjugacy` 接收 Nielsen 约化和平方迹分类给出的见证。它把一致化搬运到相应的 `takeuchiPair i`，供复数域 CanLift 证明调用。

## English

`of_closure_eq` keeps the uniformizing map for a Nielsen move that preserves the generated subgroup. `of_signs` permits a separate sign change for each generator. The local proof adjoins the central matrix $-I$ to form `pmGroup`. The matrix $-I$ acts as the identity on the upper half-plane. Adding it and changing generator signs preserve the orbits.

Suppose $g$ simultaneously conjugates the generators. For $\det g>0$, `conj_pos` uniformizes the original curve by $z\mapsto\pi(g^{-1}\cdot z)$. For $\det g<0$, `conj_neg` conjugates both output coordinates and uniformizes the complex-conjugate curve. In that case, the action of $g^{-1}$ and the output map each apply complex conjugation. Their composition is holomorphic.

`uniformizes_takeuchiPair_of_conjugacy` uses the witnesses from Nielsen descent and the squared-trace classification. It transports the uniformization to the corresponding `takeuchiPair i` for the complex CanLift proof.

## 日本語

`of_closure_eq` は、Nielsen 変換後の生成元が同じ部分群を生成するとき、同じ一意化写像を用いる。`of_signs` は、各生成元の符号を個別に変えた場合にもその写像を用いる。本実装では中心に属する行列 $-I$ を加えて `pmGroup` を作る。$-I$ は上半平面に恒等写像として作用するため、$-I$ の追加と生成元の符号変更は軌道を保つ。

$g$ が同時共役を与えるとする。$\det g>0$ なら、`conj_pos` は $z\mapsto\pi(g^{-1}\cdot z)$ で元の曲線を一意化する。$\det g<0$ なら、`conj_neg` はその写像の二つの出力座標の複素共役を取り、複素共役曲線を一意化する。この場合、$g^{-1}$ の作用と出力写像がそれぞれ複素共役を一度適用するため、合成は正則である。

`uniformizes_takeuchiPair_of_conjugacy` は Nielsen 降下と跡の二乗の分類で得られたデータを受け取る。一意化を対応する `takeuchiPair i` に移し、複素数体上の CanLift の証明に渡す。

## Sources

| Step | Pinned source | Local declaration |
| --- | --- | --- |
| Nielsen generators and signs | [of_closure_eq](https://github.com/lana-agents/orbicurve-cores/blob/61616dcd77fbe45c083a8ebfa7cc80728f86e841/OrbicurveCores/S1/Transport.lean#L36) · [of_signs](https://github.com/lana-agents/orbicurve-cores/blob/61616dcd77fbe45c083a8ebfa7cc80728f86e841/OrbicurveCores/S1/Transport.lean#L70) | [of_closure_eq](../../../../Solutions/Source_ReferenceIutCanLiftUniformizationTransport.lean#L29) · [of_signs](../../../../Solutions/Source_ReferenceIutCanLiftUniformizationTransport.lean#L80) |
| Determinant sign | [conj_pos](https://github.com/lana-agents/orbicurve-cores/blob/61616dcd77fbe45c083a8ebfa7cc80728f86e841/OrbicurveCores/S1/Transport.lean#L151) · [conj_neg](https://github.com/lana-agents/orbicurve-cores/blob/61616dcd77fbe45c083a8ebfa7cc80728f86e841/OrbicurveCores/S1/Transport.lean#L196) | [conj_pos](../../../../Solutions/Source_ReferenceIutCanLiftUniformizationTransport.lean#L155) · [conj_neg](../../../../Solutions/Source_ReferenceIutCanLiftUniformizationTransport.lean#L203) |
| Classified pair | [exists_takeuchiPair](https://github.com/lana-agents/orbicurve-cores/blob/61616dcd77fbe45c083a8ebfa7cc80728f86e841/OrbicurveCores/S1/Transport.lean#L251) | [uniformizes_takeuchiPair_of_conjugacy](../../../../Solutions/Source_ReferenceIutCanLiftTakeuchiTransport.lean#L23) |
