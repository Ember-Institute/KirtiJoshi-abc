# M2 arithmetic and CanLift Proposition 2.7

## English

### The normal form and its projective action

Let $x,y,z>0$ satisfy $x^2+y^2+z^2=xyz$ and the three strict triangle inequalities. Let $\Gamma=\langle n_A,n_B\rangle$ be the Fricke normal-form group and assume its commensurator $\Delta$ is dense in $\mathrm{SL}_2(\mathbb R)$. The theorem `goodLattice_normal` proves that $\Gamma$ is discrete and gives a measurable set of finite hyperbolic area in the upper half-plane. Every orbit meets the set. For each point of the upper half-plane, only finitely many elements of $\Gamma$ send it into the set. Commensurator superrigidity takes this lattice and a matrix action of $\Delta$ on $\mathbb P^1(k)$. Here $k$ is a proper nontrivially normed field with decidable equality and its Borel measurable structure. It requires that no finite-index subgroup of $\Gamma$ have a common fixed point. It also requires a sequence in $\Gamma$ whose images of $(0,1,\infty)$ converge to a triple with a repeated point. These inputs give a projective action of $\mathrm{SL}_2(\mathbb R)$ extending the action of $\Delta$. For each point $w$ of the projective line, the map $g\mapsto\Phi(g)\cdot w$ is continuous. [Fricke lattice][lattice] · [Lattice condition][lattice-condition] · [Local superrigidity][superrigid] · [Pinned superrigidity][up-superrigid]

Write $u_t=\left(\begin{smallmatrix}1&t\\0&1\end{smallmatrix}\right)$ and $K=[n_A,n_B]$. The central matrix $-I$ belongs to $\Delta$, and $u_2=(-I)K$, so the extension agrees with the matrix action at $u_2$. Over a field of characteristic zero, if $\Phi(u_2)$ is translation by $2$, `smul_uU_rat` gives translation by $q$ at $u_q$ for every rational $q$. It uses `root_of_translation`. For $m>0$, a projective $m$-th root commutes with translation by $2$, so it fixes infinity and acts on finite points by an affine map. The iterate condition forces that map to be translation by $2/m$. [Membership of the unipotent][comm] · [Rational translations][rat-transl] · [Pinned unipotent proof][up-rat-transl]

### Complex rationality and the bound at each prime

For a ring embedding $\sigma:\mathbb R\to\mathbb C$, apply $\sigma$ to the matrix entries of each element of $\Delta$. The action of $K$ is translation by $2$, and $n_A$ moves infinity. Powers of $K$ and of its conjugate exclude a common fixed point in every finite-index subgroup. The powers of $K$ also send the standard triple to $(\infty,\infty,\infty)$ in the limit. Superrigidity gives $\Phi$, and continuity extends the rational translation formula to every real $t$. Let $u_L(s)=\left(\begin{smallmatrix}1&0\\s&1\end{smallmatrix}\right)$. The square of $u_1 u_L(-1)u_1$ is $-I$, which acts trivially. Using this relation, `complex_rigidity` gives $\sigma(r)^2=(r:\mathbb C)^2$ for the nonzero lower-left entry $r$ of a matrix in $\Gamma$. Apply it to $n_A,n_B,n_A n_B$, whose lower-left entries are $x,-y,z$. Every irrational real number moves under some ring embedding into $\mathbb C$. Thus $x^2,y^2,z^2$ are rational. [Complex action][complex-action] · [Limit of the triple][complex-limit] · [Non-elementarity][non-elem] · [Local complex rigidity][complex-rigidity] · [Complex embeddings][embedding] · [Local rationality][rationality] · [Pinned complex rigidity][up-complex] · [Pinned rationality][up-rationality]

The rational parameter squares give a rational matrix representative up to nonzero real scalar for each element of $\Delta$. Fix a prime $p$ and $\gamma\in\Gamma$, and write $R$ for the chosen rational representative of $\gamma$. The action `aP` casts the rational representatives to $\mathbb Q_p$ and acts on $\mathbb P^1(\mathbb Q_p)$. The actions of $K$ and $n_A$ again give the required fixed-point condition. If $\lvert\operatorname{tr}(R)^2/\det R\rvert_p>1$, the $p$-adic trace norm squared exceeds the determinant norm. The two characteristic roots then have different norms. After rescaling the matrix powers, the images of the standard triple converge to a triple with a repeated point. The projective action of $\gamma^n$ agrees with the $n$-fold action of $\gamma$, so this gives the sequence for superrigidity. The extension sends zero to $2/p^j$ under $u_{2/p^j}$. These real parameters tend to zero, while the $p$-adic norm of their images stays at least $\lVert2\rVert_p>0$. This contradicts continuity and proves $\lvert\operatorname{tr}(R)^2/\det R\rvert_p\le 1$. [Rational representatives][rational-comm] · [The $p$-adic action][padic-action] · [Limit of matrix powers][padic-limit] · [Continuity contradiction][padic-contradiction] · [Local prime bound][padic-bound] · [Pinned prime bound][up-padic]

### Integer squared traces and the core theorem

The determinant-one condition gives $\operatorname{tr}(\gamma)^2=\operatorname{tr}(R)^2/\det R$ after the rational value is cast to $\mathbb R$. A rational number with $p$-adic norm at most $1$ at every prime has denominator $1$ in lowest terms. A prime dividing a larger denominator would give norm greater than $1$. This gives an integer squared trace for **every** $\gamma\in\Gamma$. The resulting `normalFormTraceIntegrality` supplies the trace transport to the original lattice generators when their commutator trace is $-2$, the first trace is nonzero, and the commensurator is dense. Sign changes and conjugation preserve squared traces. [Integer criterion][integer] · [Local integrality][integrality] · [Normal-form input][normal-integrality] · [Trace transport][transport] · [Pinned integrality][up-integrality] · [Pinned transport and classification][up-transport]

For a complex elliptic curve with nonexceptional $j$, the complex proof excludes infinite commensurator index for its once-punctured uniformization. Infinite index gives density, and trace integrality gives a pair classified by Takeuchi. Uniformization transport and rigidity then force one of the four exceptional $j$-values. Finite index supplies the invariant polynomial generator used in the complex core proof. The four certified model uniformizations and `normalFormTraceIntegrality` give `canLift27Complex` through `canLift27Complex_of_fricke_integrality`. [Excluding infinite index][classification] · [Model uniformizations][models] · [Pinned classification][up-models] · [Polynomial generator][index] · [Local complex assembly][complex-assembly] · [Pinned complex conclusion][up-complex-conclusion]

`canLift27_of_complex` takes `canLift27Complex` and gives `canLift27 : CanLift27.{0}`. It applies to elliptic curves over characteristic-zero fields at universe level zero with $j$ outside $\{0,1728,488095744/125,1556068/81\}$. The normalized sign quotient is a core of the normalized once-punctured curve. In particular, it shares a finite étale cover with that curve. Every orbicurve presentation that shares a finite étale cover with the normalized curve has exactly one finite étale cover to the core. The Lefschetz argument uses the algebraic closure and countable algebraically closed subfields. It embeds those subfields into $\mathbb C$, applies the complex case, and descends the core property along the embeddings. [Proposition and exceptional values][core] · [Core relation][core-relation] · [Local Lefschetz theorem][lefschetz] · [Pinned Lefschetz theorem][up-lefschetz] · [Proposition 2.7][prop27]

### Use in the tripod construction

`genuineEtalePi1Theory canLift27` supplies the once-punctured core property on normalization presentations for `modelAG`. For the given curve provider $P$, compactly bounded set $K$, and degree bound $d$, `pointThetaDataExistence_from_canLift27` obtains core finiteness from `coreFiniteness_of_modelAG (genuineEtalePi1Theory canLift27) P K d`. It passes that proof to `pointThetaDataExistence_from_source` with the same $P,K,d$, the curve facts, the Northcott hypothesis, and anabelian existence for the given tempered geometry. The result is pointwise theta-data existence for the source P7 construction. [Étale fundamental group model][genuine] · [Core finiteness][core-finiteness] · [Tripod consumer][tripod]

## 简体中文

### 正规形及其射影作用

设 $x,y,z>0$ 满足 $x^2+y^2+z^2=xyz$ 和三个严格三角不等式。$\Gamma=\langle n_A,n_B\rangle$ 为 Fricke 正规形生成的群，且其可公度子 $\Delta$ 在 $\mathrm{SL}_2(\mathbb R)$ 中稠密。`goodLattice_normal` 证明 $\Gamma$ 是离散的，并在上半平面给出一个双曲面积有限的可测集。每条轨道都与该集合相交。对上半平面的每个点，$\Gamma$ 中只有有限个元素将它送入该集合。可公度子超刚性定理使用该格子和 $\Delta$ 在 $\mathbb P^1(k)$ 上的矩阵作用。这里 $k$ 是具有非平凡范数的域，闭球紧致，等式可判定，并配备 Borel 可测结构。它要求 $\Gamma$ 的任何有限指数子群都没有公共不动点，并要求 $\Gamma$ 中有一列元素，使标准三点 $(0,1,\infty)$ 的像收敛到有重复坐标的三元组。由此得到 $\mathrm{SL}_2(\mathbb R)$ 的射影作用 $\Phi$，延拓 $\Delta$ 的作用。固定射影点 $w$ 后，$g\mapsto\Phi(g)\cdot w$ 连续。 [Fricke 格子][lattice] · [格子条件][lattice-condition] · [本地超刚性][superrigid] · [固定上游][up-superrigid]

记 $u_t=\left(\begin{smallmatrix}1&t\\0&1\end{smallmatrix}\right)$、$K=[n_A,n_B]$。中心元 $-I$ 属于 $\Delta$，且 $u_2=(-I)K$，所以延拓在 $u_2$ 处与原矩阵作用一致。在特征零域上，若 $\Phi(u_2)$ 作平移 $2$，`smul_uU_rat` 给出每个有理数 $q$ 处 $\Phi(u_q)$ 作平移 $q$。证明使用 `root_of_translation`。当 $m>0$ 时，平移 $2$ 的射影 $m$ 次根与该平移交换，因此固定无穷远点，在有限点上是仿射变换。迭代等式迫使该仿射变换为平移 $2/m$。 [幂单矩阵的成员关系][comm] · [有理平移][rat-transl] · [固定上游][up-rat-transl]

### 复数分支的有理性与逐素数界

对任意环嵌入 $\sigma:\mathbb R\to\mathbb C$，逐项映射 $\Delta$ 中的矩阵。$K$ 作平移 $2$，$n_A$ 移动无穷远点。任一有限指数子群中均有 $K$ 及其共轭的正整数次幂，排除公共不动点。$K$ 的幂把标准三点送往 $(\infty,\infty,\infty)$。超刚性给出 $\Phi$，连续性把有理平移公式推广到所有实数 $t$。记 $u_L(s)=\left(\begin{smallmatrix}1&0\\s&1\end{smallmatrix}\right)$。矩阵 $u_1 u_L(-1)u_1$ 的平方为 $-I$，其作用为恒等。`complex_rigidity` 利用此关系，证明 $\Gamma$ 中矩阵的非零左下项 $r$ 满足 $\sigma(r)^2=(r:\mathbb C)^2$。对 $n_A,n_B,n_A n_B$ 应用该结论，左下项依次为 $x,-y,z$。任意无理实数都会被某个到 $\mathbb C$ 的环嵌入移动，因此 $x^2,y^2,z^2$ 均为有理数。 [复数作用][complex-action] · [三点的极限][complex-limit] · [非初等性][non-elem] · [复刚性][complex-rigidity] · [复嵌入][embedding] · [平方有理性][rationality] · [固定上游刚性][up-complex] · [固定上游有理性][up-rationality]

参数的平方为有理数后，$\Delta$ 的每个元素都是某个有理矩阵的非零实数倍。固定素数 $p$ 和 $\gamma\in\Gamma$，记 $R$ 为 $\gamma$ 选定的有理代表。`aP` 把有理代表的各项映入 $\mathbb Q_p$，得到在 $\mathbb P^1(\mathbb Q_p)$ 上的作用。$K$ 和 $n_A$ 的作用仍给出非初等性。若 $\lvert\operatorname{tr}(R)^2/\det R\rvert_p>1$，迹的 $p$ 进范数的平方大于行列式的范数，两个特征根的范数不同。对矩阵幂缩放后，标准三点的像收敛到有重复坐标的三元组。$\gamma^n$ 的射影作用等于 $\gamma$ 的作用迭代 $n$ 次，因此这些幂给出超刚性所需的序列。在延拓作用下，$u_{2/p^j}$ 把零送到 $2/p^j$。实数参数趋于零，而像的 $p$ 进范数至少为 $\lVert2\rVert_p>0$。这与连续性矛盾，故 $\lvert\operatorname{tr}(R)^2/\det R\rvert_p\le 1$。 [有理代表][rational-comm] · [p 进作用][padic-action] · [矩阵幂的极限][padic-limit] · [连续性矛盾][padic-contradiction] · [本地逐素数界][padic-bound] · [固定上游][up-padic]

### 平方迹整性与核定理

因为 $\det\gamma=1$，$\operatorname{tr}(\gamma)^2$ 等于 $\operatorname{tr}(R)^2/\det R$ 在实数中的像。在每个素数处范数均不大于 $1$ 的有理数，其既约分母为 $1$。若分母更大，其素因子处的范数就大于 $1$。由此得到 $\Gamma$ 中**每个**元素的平方迹为整数。`normalFormTraceIntegrality` 将结论交给迹的搬运定理。只要原生成对的交换子迹为 $-2$、第一个生成元的迹非零，且可公度子稠密，便能将整性搬回原格子群。换符号与共轭保持平方迹。 [整数判据][integer] · [本地整性][integrality] · [正规形整性输入][normal-integrality] · [迹的搬运][transport] · [固定上游整性][up-integrality] · [固定上游搬运和分类][up-transport]

对 $j$ 非例外的复椭圆曲线，复数证明排除其一次穿孔一致化群在可公度子中指数无穷的情形。无穷指数使可公度子稠密。平方迹整性随之给出 Takeuchi 分类的生成对，一致化的搬运和刚性迫使 $j$ 为四个例外值之一。有限指数给出复数核证明所用的不变多项式生成元。四条模型曲线的一致化和 `normalFormTraceIntegrality` 经 `canLift27Complex_of_fricke_integrality` 得到 `canLift27Complex`。 [排除无穷指数][classification] · [模型一致化][models] · [固定上游分类][up-models] · [不变多项式][index] · [本地复数组装][complex-assembly] · [固定上游复数结论][up-complex-conclusion]

`canLift27_of_complex` 将 `canLift27Complex` 推广为 `canLift27 : CanLift27.{0}`。它适用于宇宙层级零的特征零域上的椭圆曲线，且 $j\notin\{0,1728,488095744/125,1556068/81\}$。归一化的符号商是归一化的一次穿孔曲线的核。两者有公共有限 étale 覆盖。任何与归一化曲线有公共有限 étale 覆盖的轨形曲线表示，都恰有一个到该核的有限 étale 覆盖。Lefschetz 论证先取代数闭包，再用其中可数的代数闭子域。把这些子域嵌入 $\mathbb C$，应用复数情形，再沿嵌入下降核性质。 [命题及例外值][core] · [核关系][core-relation] · [本地 Lefschetz 定理][lefschetz] · [固定上游 Lefschetz 定理][up-lefschetz] · [命题 2.7][prop27]

### 三足构造中的使用

`genuineEtalePi1Theory canLift27` 为 `modelAG` 中的归一化表示提供一次穿孔曲线的核性质。给定曲线提供者 $P$、紧致有界集 $K$ 和次数界 $d$，`pointThetaDataExistence_from_canLift27` 从 `coreFiniteness_of_modelAG (genuineEtalePi1Theory canLift27) P K d` 得到核有限性。它把该证明连同同一组 $P,K,d$、曲线性质、Northcott 假设及给定缓和几何的远阿贝尔存在性传给 `pointThetaDataExistence_from_source`。结论给出来源 P7 构造所需的逐点 Θ 数据的存在性。 [Étale 基本群模型][genuine] · [核有限性][core-finiteness] · [三足构造][tripod]

## 日本語

### 標準形と射影作用

正の実数 $x,y,z$ が $x^2+y^2+z^2=xyz$ と三つの狭義の三角不等式を満たすとする。$\Gamma=\langle n_A,n_B\rangle$ を Fricke 標準形の生成する群とし、その可公度化群 $\Delta$ が $\mathrm{SL}_2(\mathbb R)$ で稠密であると仮定する。`goodLattice_normal` は $\Gamma$ が離散的であることを示し、上半平面に双曲面積が有限な可測集合を与える。各軌道はこの集合と交わる。上半平面の各点をこの集合に移す $\Gamma$ の元は有限個である。可公度化群の超剛性定理は、この格子と $\Delta$ の $\mathbb P^1(k)$ への行列作用を使う。ここで $k$ は非自明なノルムを持つ体で、閉球がコンパクトであり、等号が決定可能で、Borel 可測構造を備える。どの有限指数部分群にも共通の固定点が存在せず、標準の三点 $(0,1,\infty)$ の像が重複を含む三つ組に収束する $\Gamma$ の元の列が存在すると仮定する。定理は $\Delta$ の作用を延長する $\mathrm{SL}_2(\mathbb R)$ の射影作用 $\Phi$ を与える。射影直線の各点 $w$ を固定すると、$g\mapsto\Phi(g)\cdot w$ は連続である。 [Fricke 格子][lattice] · [格子の条件][lattice-condition] · [ローカルの超剛性][superrigid] · [固定した上流の超剛性][up-superrigid]

$u_t=\left(\begin{smallmatrix}1&t\\0&1\end{smallmatrix}\right)$、$K=[n_A,n_B]$ とおく。中心元 $-I$ は $\Delta$ に属し、$u_2=(-I)K$ なので、延長は $u_2$ で元の行列の作用と一致する。標数零の体で $\Phi(u_2)$ が $2$ の平行移動を与えるなら、`smul_uU_rat` により、有理数 $q$ ごとに $\Phi(u_q)$ は $q$ の平行移動を与える。証明は `root_of_translation` を使う。$m>0$ のとき、平行移動 $2$ の射影的な $m$ 乗根はその平行移動と可換なので、無限遠点を固定し、有限点ではアフィン変換になる。反復の等式により、そのアフィン変換は $2/m$ の平行移動である。 [冪単行列の所属][comm] · [有理数の平行移動][rat-transl] · [固定した上流][up-rat-transl]

### 複素数での有理性と各素数での評価

環埋め込み $\sigma:\mathbb R\to\mathbb C$ を任意に取り、$\Delta$ の行列の成分に適用する。$K$ は $2$ の平行移動として作用し、$n_A$ は無限遠点を動かす。各有限指数部分群は $K$ とその共役の正の冪を含むため、共通の固定点は存在しない。$K$ の冪による標準の三点の像は $(\infty,\infty,\infty)$ に収束する。超剛性定理が $\Phi$ を与え、連続性により有理パラメータでの平行移動の式をすべての実数 $t$ に延長する。$u_L(s)=\left(\begin{smallmatrix}1&0\\s&1\end{smallmatrix}\right)$ とおく。$u_1 u_L(-1)u_1$ の二乗は $-I$ であり、その作用は恒等写像である。`complex_rigidity` はこの関係を用いて、$\Gamma$ の行列の左下成分 $r$ が零でなければ $\sigma(r)^2=(r:\mathbb C)^2$ を得る。これを $n_A,n_B,n_A n_B$ に適用すると、左下成分は順に $x,-y,z$ である。任意の無理実数を動かす $\mathbb C$ への環埋め込みがあるため、$x^2,y^2,z^2$ は有理数である。 [複素射影作用][complex-action] · [三点の極限][complex-limit] · [非初等性][non-elem] · [複素剛性][complex-rigidity] · [複素数への埋め込み][embedding] · [二乗の有理性][rationality] · [固定した上流の剛性][up-complex] · [固定した上流の有理性][up-rationality]

パラメータの二乗が有理数なら、$\Delta$ の各元は有理行列の零でない実数倍である。素数 $p$ と $\gamma\in\Gamma$ を固定し、$\gamma$ の有理代表を $R$ とする。`aP` は有理代表の成分を $\mathbb Q_p$ に移し、$\mathbb P^1(\mathbb Q_p)$ に作用させる。$K$ と $n_A$ の作用はこの場合も非初等性を与える。$\lvert\operatorname{tr}(R)^2/\det R\rvert_p>1$ なら、跡の $p$ 進ノルムの二乗は行列式のノルムより大きく、二つの特性根のノルムは異なる。行列の冪をスカラー倍で調整すると、標準の三点の像は重複を含む三つ組に収束する。$\gamma^n$ の射影作用は $\gamma$ の作用の $n$ 回反復に等しく、その冪の列が超剛性定理の仮定を満たす。延長の作用では $u_{2/p^j}$ が零を $2/p^j$ に送る。この実パラメータは零に収束する一方、像の $p$ 進ノルムは $\lVert2\rVert_p>0$ 以上である。連続性に矛盾するため、$\lvert\operatorname{tr}(R)^2/\det R\rvert_p\le 1$ が成り立つ。 [有理代表][rational-comm] · [p 進射影作用][padic-action] · [行列の冪の極限][padic-limit] · [連続性との矛盾][padic-contradiction] · [各素数での評価][padic-bound] · [固定した上流][up-padic]

### 跡の二乗の整数性と核の定理

$\det\gamma=1$ なので、$\operatorname{tr}(\gamma)^2$ は $\operatorname{tr}(R)^2/\det R$ の実数への像に等しい。すべての素数でノルムが $1$ 以下の有理数は、既約分母が $1$ である。分母が $1$ より大きければ、その素因子でノルムが $1$ より大きくなる。したがって $\Gamma$ の**各元**の跡の二乗は整数である。`normalFormTraceIntegrality` は、この結果を跡の整数性の移送に渡す。元の生成対について交換子の跡が $-2$、第一生成元の跡が零でなく、可公度化群が稠密なら、整数性は元の格子群にも成り立つ。符号の変更と共役は跡の二乗を保つ。 [整数性の判定][integer] · [整数性の証明][integrality] · [標準形での整数性入力][normal-integrality] · [跡の移送][transport] · [固定した上流の整数性][up-integrality] · [固定した上流の移送と分類][up-transport]

複素楕円曲線の $j$ が例外値でなければ、複素数上の証明は一点除去曲線の一意化群が可公度化群で無限指数になることを排除する。無限指数なら可公度化群は稠密で、跡の二乗の整数性から Takeuchi の分類に属する生成対が得られる。一意化の移送と剛性により、$j$ は四つの例外値のいずれかに等しくなる。有限指数の場合、複素数上の核の証明に使う不変多項式の生成元が得られる。四つのモデル曲線の一意化と `normalFormTraceIntegrality` を `canLift27Complex_of_fricke_integrality` に渡すと、`canLift27Complex` が得られる。 [無限指数の排除][classification] · [モデルの一意化][models] · [固定した上流の分類][up-models] · [不変多項式][index] · [ローカルの複素数上の証明][complex-assembly] · [固定した上流の複素数上の結論][up-complex-conclusion]

`canLift27_of_complex` を `canLift27Complex` に適用すると、`canLift27 : CanLift27.{0}` が得られる。宇宙レベル零の標数零の体上の楕円曲線で、$j\notin\{0,1728,488095744/125,1556068/81\}$ のものに適用する。符号商の正規化は、一点除去曲線の正規化の核である。両者は共通の有限エタール被覆を持つ。正規化した曲線と共通の有限エタール被覆を持つ各軌道曲線表示から、核への有限エタール被覆がただ一つ存在する。Lefschetz の議論では代数閉包を取り、その中の可算代数閉部分体を用いる。それらを $\mathbb C$ に埋め込み、複素数の場合を適用して、埋め込みに沿って核の性質を降下させる。 [命題と例外値][core] · [核の関係][core-relation] · [ローカルの Lefschetz 定理][lefschetz] · [固定した上流の Lefschetz 定理][up-lefschetz] · [命題 2.7][prop27]

### 三脚の構成での使用

`genuineEtalePi1Theory canLift27` は `modelAG` の正規化表示に対して、一点除去曲線の核の性質を与える。曲線の供給者 $P$、コンパクト有界集合 $K$、次数の上界 $d$ を与えると、`pointThetaDataExistence_from_canLift27` は `coreFiniteness_of_modelAG (genuineEtalePi1Theory canLift27) P K d` から核の有限性を得る。この証明を、同じ $P,K,d$、曲線の性質、Northcott の仮定、与えた緩和幾何での遠アーベル的な存在性とともに `pointThetaDataExistence_from_source` に渡す。その結果、原典の P7 構成で用いる点ごとの Θ データの存在が得られる。 [エタール基本群のモデル][genuine] · [核の有限性][core-finiteness] · [三脚の構成][tripod]

[lattice]: ../../../../Solutions/Source_ReferenceIutCanLiftGoodLattice.lean#L26
[lattice-condition]: ../../../../Solutions/Source_ReferenceIutCanLiftM2Setup.lean#L50
[superrigid]: ../../../../Solutions/Source_ReferenceIutCanLiftSuperrigidity.lean#L62
[comm]: ../../../../Solutions/Source_ReferenceIutCanLiftFrickeUnipotentCommensurator.lean#L40
[rat-transl]: ../../../../Solutions/Source_ReferenceIutCanLiftUnipotent.lean#L150
[complex-action]: ../../../../Solutions/Source_ReferenceIutCanLiftFrickeComplexAction.lean#L34
[complex-limit]: ../../../../Solutions/Source_ReferenceIutCanLiftFrickeComplexAction.lean#L104
[non-elem]: ../../../../Solutions/Source_ReferenceIutCanLiftNonElementary.lean#L102
[complex-rigidity]: ../../../../Solutions/Source_ReferenceIutCanLiftUnipotentComplex.lean#L89
[embedding]: ../../../../Solutions/Source_ReferenceIutCanLiftComplexEmbedding.lean#L86
[rationality]: ../../../../Solutions/Source_ReferenceIutCanLiftFrickeComplexTraceRationality.lean#L88
[rational-comm]: ../../../../Solutions/Source_ReferenceIutCanLiftFrickeRationalCommensurator.lean#L80
[padic-action]: ../../../../Solutions/Source_ReferenceIutCanLiftPadicAction.lean#L30
[padic-limit]: ../../../../Solutions/Source_ReferenceIutCanLiftPadicUnbounded.lean#L85
[padic-contradiction]: ../../../../Solutions/Source_ReferenceIutCanLiftUnipotentPadic.lean#L28
[padic-bound]: ../../../../Solutions/Source_ReferenceIutCanLiftFrickePadicTraceBound.lean#L35
[integer]: ../../../../Solutions/Source_ReferenceIutCanLiftPadicSquaredTraces.lean#L49
[integrality]: ../../../../Solutions/Source_ReferenceIutCanLiftFinal.lean#L26
[normal-integrality]: ../../../../Solutions/Source_ReferenceIutCanLiftFinal.lean#L38
[transport]: ../../../../Solutions/Source_ReferenceIutCanLiftFrickeTraceTransport.lean#L114
[classification]: ../../../../Solutions/Source_ReferenceIutCanLiftComplexFromArithmetic.lean#L25
[models]: ../../../../Solutions/Source_ReferenceIutCanLiftTakeuchiModelUniformizations.lean#L27
[index]: ../../../../Solutions/Source_ReferenceIutCanLiftComplexFromIndex.lean#L20
[complex-assembly]: ../../../../Solutions/Source_ReferenceIutCanLiftComplexFromFricke.lean#L15
[core]: ../../../../Solutions/Source_ReferenceIutCanLiftPresentation.lean#L104
[core-relation]: ../../../../Solutions/Source_ReferenceIutCanLiftPresentation.lean#L26
[lefschetz]: ../../../../Solutions/Source_ReferenceIutCanLiftLefschetz.lean#L16
[prop27]: ../../../../Solutions/Source_ReferenceIutCanLiftProp27.lean#L12
[genuine]: ../../../../Solutions/Source_ReferenceIutGenuineCore.lean#L80
[core-finiteness]: ../../../../Solutions/Source_TripodCoreModel.lean#L71
[tripod]: ../../../../Solutions/Source_TripodP7FromCanLift.lean#L17
[up-superrigid]: https://github.com/lana-agents/orbicurve-cores/blob/61616dcd77fbe45c083a8ebfa7cc80728f86e841/OrbicurveCores/M2/Superrigidity.lean#L54
[up-rat-transl]: https://github.com/lana-agents/orbicurve-cores/blob/61616dcd77fbe45c083a8ebfa7cc80728f86e841/OrbicurveCores/M2/Unipotent.lean#L151
[up-complex]: https://github.com/lana-agents/orbicurve-cores/blob/61616dcd77fbe45c083a8ebfa7cc80728f86e841/OrbicurveCores/M2/Unipotent.lean#L319
[up-rationality]: https://github.com/lana-agents/orbicurve-cores/blob/61616dcd77fbe45c083a8ebfa7cc80728f86e841/OrbicurveCores/M2/Final.lean#L268
[up-padic]: https://github.com/lana-agents/orbicurve-cores/blob/61616dcd77fbe45c083a8ebfa7cc80728f86e841/OrbicurveCores/M2/Final.lean#L451
[up-integrality]: https://github.com/lana-agents/orbicurve-cores/blob/61616dcd77fbe45c083a8ebfa7cc80728f86e841/OrbicurveCores/M2/Final.lean#L548
[up-transport]: https://github.com/lana-agents/orbicurve-cores/blob/61616dcd77fbe45c083a8ebfa7cc80728f86e841/OrbicurveCores/M2/Final.lean#L595
[up-models]: https://github.com/lana-agents/orbicurve-cores/blob/61616dcd77fbe45c083a8ebfa7cc80728f86e841/OrbicurveCores/S1/Main.lean#L101
[up-complex-conclusion]: https://github.com/lana-agents/orbicurve-cores/blob/61616dcd77fbe45c083a8ebfa7cc80728f86e841/OrbicurveCores/U2/Assembly.lean#L385
[up-lefschetz]: https://github.com/lana-agents/pi1/blob/ca7def953193f861a462aa0831eec8f0a31ff69f/Pi1/Orbicurve/LefschetzMain.lean#L280
