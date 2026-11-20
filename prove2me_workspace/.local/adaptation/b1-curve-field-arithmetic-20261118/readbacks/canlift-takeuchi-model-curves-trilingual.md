# Takeuchi model curves and the exceptional `j`-invariants

| Model index | Weierstrass equation | `j` |
| ---: | --- | ---: |
| 0 | $y^2=x(x^2+44x-16)$ | $488095744/125$ |
| 1 | $y^2=(x-24)(x+8)(x+12)$ | $1556068/81$ |
| 2 | $y^2=x(x^2-16)$ | $1728$ |
| 3 | $y^2=x^3-1728$ | $0$ |

## 中文

四个模型均满足 `a₁ = a₃ = 0`。每个模型的三次多项式都有一份 Belyi 证书。证书用三次幂和平方分别写出分子及分子减去 1728 倍分母，并核对临界点因子、极点、互素性、单根和次数条件。椭圆轨形覆盖仍需用这些等式构造。 [来源](https://github.com/lana-agents/orbicurve-cores/blob/61616dcd77fbe45c083a8ebfa7cc80728f86e841/OrbicurveCores/S1/Certificates.lean) · [证书](../../../../Solutions/Source_ReferenceIutCanLiftTakeuchiCertificates.lean#L362)

`qcurve` 沿用固定版本的四个有理 Weierstrass 模型及其顺序。判别式均非零，计算得到表中的四个互异 `j` 值，且它们属于本地的 `canLiftExceptionalJ`。复基变换得到 `ccurve`，其 `j` 值是相应有理数在复数域中的像。复共轭固定这些有理系数，因此固定四个复模型。 [固定版本的模型曲线](https://github.com/lana-agents/orbicurve-cores/blob/61616dcd77fbe45c083a8ebfa7cc80728f86e841/OrbicurveCores/S1/Main.lean#L33) · [本地模型](../../../../Solutions/Source_ReferenceIutCanLiftTakeuchiModelCurves.lean#L29)

`exceptionalJ_of_model_uniformizations` 用本地 `IsUniformization` 表述 S1 的有限分类步骤。假设每个模型或其复共轭由某个分类矩阵对一致化，并且同一个矩阵对的一致化蕴含 `j` 相等。四个模型有不同的 `j` 值，所以分配给它们的分类索引互异，恰好用遍四个索引。若待判定的曲线或其复共轭由这四对中的一对一致化，则该曲线的 `j` 为对应的有理例外值。S1 的应用还需要模型的 Belyi 证书、一致化的刚性及分类矩阵对之间的一致化传递。 [S1 证明](https://github.com/lana-agents/orbicurve-cores/blob/61616dcd77fbe45c083a8ebfa7cc80728f86e841/OrbicurveCores/S1/Main.lean#L82) · [本地有限分类步骤](../../../../Solutions/Source_ReferenceIutCanLiftTakeuchiModelRigidity.lean#L28)

## English

All four models satisfy `a₁ = a₃ = 0`. Each model cubic has a Belyi certificate. The identities express the numerator as a cube times a constant and the numerator minus 1728 times the denominator as a square times the same constant. Further identities determine the critical factors and poles and certify coprimality, simple roots and the degree condition. These identities are inputs to the elliptic orbifold covering construction. [Source](https://github.com/lana-agents/orbicurve-cores/blob/61616dcd77fbe45c083a8ebfa7cc80728f86e841/OrbicurveCores/S1/Certificates.lean) · [Certificates](../../../../Solutions/Source_ReferenceIutCanLiftTakeuchiCertificates.lean#L362)

`qcurve` preserves the four rational Weierstrass models and their order from the pinned source. Each discriminant is nonzero. The four computed `j`-invariants are distinct and belong to `canLiftExceptionalJ`. On base change to complex coefficients, each model retains its rational `j`-invariant, and complex conjugation fixes the model. [Pinned model curves](https://github.com/lana-agents/orbicurve-cores/blob/61616dcd77fbe45c083a8ebfa7cc80728f86e841/OrbicurveCores/S1/Main.lean#L33) · [Local models](../../../../Solutions/Source_ReferenceIutCanLiftTakeuchiModelCurves.lean#L29)

`exceptionalJ_of_model_uniformizations` states the finite classification step of S1 with the local `IsUniformization`. For each model, assume that a classified matrix pair uniformizes that model or its complex conjugate. Assume also that curves uniformized by the same pair have the same `j`-invariant. The four distinct values force the assigned indices to exhaust the four pairs. If one of those pairs uniformizes a curve or its complex conjugate, the curve has the matching rational `j`-invariant. The application in S1 uses the Belyi certificates for the models, rigidity of uniformization, and transport of uniformization to the classified pairs. [S1 proof](https://github.com/lana-agents/orbicurve-cores/blob/61616dcd77fbe45c083a8ebfa7cc80728f86e841/OrbicurveCores/S1/Main.lean#L82) · [Local finite classification step](../../../../Solutions/Source_ReferenceIutCanLiftTakeuchiModelRigidity.lean#L28)

## 日本語

四つのモデルはいずれも `a₁ = a₃ = 0` を満たす。各モデルの三次多項式には Belyi 証明書がある。分子は定数倍の三乗であり、分子から分母の 1728 倍を引いた式は同じ定数倍の二乗である。他の恒等式は臨界点と極を記述し、互いに素であること、単根性と次数の条件を保証する。これらは楕円オービフォールド被覆の構成に用いられる。 [上流](https://github.com/lana-agents/orbicurve-cores/blob/61616dcd77fbe45c083a8ebfa7cc80728f86e841/OrbicurveCores/S1/Certificates.lean) · [証明書](../../../../Solutions/Source_ReferenceIutCanLiftTakeuchiCertificates.lean#L362)

`qcurve` は固定リビジョンの四つの有理 Weierstrass モデルとその順序を保つ。各判別式は非零であり、計算された四つの `j` 不変量は相異なり、いずれも `canLiftExceptionalJ` に属する。複素数体への基底変換で得られる `ccurve` の `j` 不変量は対応する有理数の像である。また、複素共役は有理係数を固定するので、四つの複素モデルを固定する。 [固定リビジョンのモデル曲線](https://github.com/lana-agents/orbicurve-cores/blob/61616dcd77fbe45c083a8ebfa7cc80728f86e841/OrbicurveCores/S1/Main.lean#L33) · [ローカルのモデル](../../../../Solutions/Source_ReferenceIutCanLiftTakeuchiModelCurves.lean#L29)

`exceptionalJ_of_model_uniformizations` はローカルの `IsUniformization` で S1 の有限分類の段階を表す。各モデルまたはその複素共役が分類された行列対の一つで一意化され、同じ行列対で一意化された曲線の `j` 不変量が等しいと仮定する。四つのモデルの `j` 不変量は相異なるので、割り当てられる添字は四つの行列対をすべて尽くす。与えられた曲線またはその複素共役がこのうち一つの行列対で一意化されれば、その曲線は対応する有理 `j` 不変量をもつ。S1 への適用には、モデルの Belyi 証明書、一意化の剛性、分類された行列対への一意化の移送を用いる。 [S1 の証明](https://github.com/lana-agents/orbicurve-cores/blob/61616dcd77fbe45c083a8ebfa7cc80728f86e841/OrbicurveCores/S1/Main.lean#L82) · [ローカルの有限分類](../../../../Solutions/Source_ReferenceIutCanLiftTakeuchiModelRigidity.lean#L28)
