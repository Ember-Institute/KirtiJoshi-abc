# English

Fix a curve provider $P$ and a point $x$. The selected curve $P.\mathrm{curve}(x)$ supplies its own local Tate inputs. The definition of local height data combines these inputs with the arithmetic data of that same curve supplied by $P$. The provider height is the height of the resulting local data. This defines the height for a given provider. Its comparison with the normalized finite height of the Legendre $j$-invariant is a separate theorem.

Paper context: Shinichi Mochizuki, *Arithmetic Elliptic Curves in General Position*, §3, Definition 3.3, introduces the arithmetic degree of the $q$-pilot object. The three Lean definitions here are from `Iut/Tripod/CurveFacts.lean:388–395`; the paper context does not establish their comparison with the finite height of $j$.

# 简体中文

固定曲线供应数据 $P$ 和一个点 $x$。从 $P$ 为 $x$ 选定的曲线取得其局部 Tate 输入，再用 $P$ 为同一条曲线提供的算术数据装配局部高度数据。所定义的高度就是这组局部数据自身的高度。这一定义适用于给定的供应数据；要将所得高度与 Legendre 曲线的 $j$ 不变量的规范化有限高度相等同，还需另外证明。

# 日本語

曲線供給データ $P$ と点 $x$ を固定する。まず、$P$ が $x$ に対して選ぶ曲線から局所 Tate 入力を得る。次に、同じ曲線について $P$ が与える算術データとその Tate 入力を用いて、局所高さデータを構成する。ここで定義する高さは、その局所データの高さである。Legendre 曲線の $j$ 不変量の正規化された有限部分の高さとの一致は、別の定理である。
