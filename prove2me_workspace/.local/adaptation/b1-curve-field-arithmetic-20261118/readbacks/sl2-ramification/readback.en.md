# Formal readback

## `EllipticCurveData.prime_dvd_ramificationIdx`

Let $F$ be a number field, $\overline F$ a chosen algebraic closure of $F$, and $E$ an elliptic Weierstrass curve over $F$. These are the data of $C$. The fields $F$ and $\overline F$ have the same universe level. Write $M=\mathbb Q(j(E))\subseteq F$ for the field of moduli. A finite place $z$ corresponds to a nonzero maximal ideal $\mathfrak p_z$ in the ring of integers. Its residue characteristic is the characteristic of the quotient by $\mathfrak p_z$. A finite place lies over another when its ideal contracts to the ideal of the other place.

Let $W$ be the set of finite places of $F$ where $E$ has multiplicative reduction. This means that some change of Weierstrass variables over $F$ gives a model with multiplicative reduction over the valuation ring of the completion.

The arithmetic record $CA:C.\mathrm{CurveArithmetic}$ supplies the following facts.

- The element $-1$ is a square in $F$.
- At each finite place of $F$, the curve has good or multiplicative reduction after a change of variables over $F$.
- Every point in $E(\overline F)$ killed by $6$ comes from a point in $E(F)$.
- For every prime $r\geq 7$, $F/M$ is Galois and $[F:M]$ is coprime to $r$.
- Every finite place of $F$ lies over a finite place of $M$. Any such pair of places has equal residue characteristics.
- Fix a finite place of $M$ with residue characteristic different from $2$. If $E$ has multiplicative reduction at one place of $F$ above it, $E$ has multiplicative reduction at every such place.
- The set $W$ is finite. Each finite place of $F$ has positive residue degree over its rational prime.
- For each natural number $r$, the sum of residue degrees over places in $W$ of residue characteristic $r$ is at most $[F:\mathbb Q]$.

For every $w\in W$, the record $TI:C.\mathrm{TateInputs}$ gives a parameter $q_w\in F_w^\times$ with $\lVert q_w\rVert<1$. Here $F_w$ is the completion at $w$. The Tate curve of $q_w$ has $j$-invariant equal to the image of $j(E)$ in $F_w$. The record also gives a uniformizer $\pi_w$ of $F_w$. Thus $\pi_w\ne 0$, $\lVert\pi_w\rVert<1$, and all norms of elements of $F_w^\times$ are integer powers of $\lVert\pi_w\rVert$. Let $n_w$ be the unique positive integer with $\lVert q_w\rVert=\lVert\pi_w\rVert^{n_w}$. The natural number $n_w$ is `TI.qOrder w hw`.

Let $\ell$ be a prime natural number with $\ell\ne 2$. Let $R:C.\mathrm{ModEllRepData}\,\ell$ give an additive isomorphism $b:E(\overline F)[\ell]\simeq\mathbb F_\ell^2$. It also gives a homomorphism $\rho:\operatorname{Aut}_F(\overline F)\to\mathrm{GL}_2(\mathbb F_\ell)$ with open kernel in the Krull topology. For every $\sigma\in\operatorname{Aut}_F(\overline F)$ and $P\in E(\overline F)[\ell]$, the record requires $b(\sigma P)=\rho(\sigma)b(P)$. Here $\sigma$ acts on point coordinates and fixes the identity point. Put $K=\overline F^{\ker\rho}$, the torsion field defined by $R$. It is a number field.

For each $w\in W$ with residue characteristic different from $2$ and $\ell$, assume $\ell\nmid n_w$. For every finite place $w'$ of $K$ over $w$, the theorem asserts
$$\ell\mid e(w'/w).$$
Here $e(w'/w)$ is the natural-number ramification index of $\mathfrak p_{w'}$ over $\mathfrak p_w$.

## Child 1. `tateStructureOfTorsion`

Let $E/F$ be an elliptic Weierstrass curve over a number field with chosen algebraic closure $\overline F$. Let $K$ be an intermediate field of $\overline F/F$ that is a number field. The fields $F$, $\overline F$, and $K$ have the same universe level. Put $M=\mathbb Q(j(E))$. Let $V$ be a set of finite places of $M$. Assume every $v\in V$ has residue characteristic different from $2$. Assume $E$ has multiplicative reduction at every finite place of $F$ over every $v\in V$. Multiplicative reduction has the change-of-variables meaning in the preceding statement.

Let $\ell$ be a prime natural number with $\ell\ne 2$. Let $T_K$ be an additive subgroup of $E(K)$ contained in $E(K)[\ell]=\{P:\ell P=0\}$. Assume $\operatorname{Nat.card}(T_K)\geq\ell^2$. Let $w'$ be a finite place of $K$ over some $v\in V$, where the relation is on the corresponding ideals. Then the construction supplies a Tate structure $S$ on the base change $E_{K_{w'}}$.

For a Weierstrass curve $B$ over $k=K_{w'}$, a Tate structure consists of the following data.

- A parameter $q\in k^\times$ with $\lVert q\rVert<1$.
- A change $D$ of Weierstrass variables over $k$ such that $D\cdot B=E_q$, the Tate Weierstrass model of $q$.
- An additive group isomorphism from the multiplicative quotient $k^\times/q^{\mathbb Z}$, written additively, to $B(k)$.
- For each $u\in k^\times$ outside $q^{\mathbb Z}$, the point of the class of $u$ has the Tate coordinates $X_q(u),Y_q(u)$ in the changed model $E_q$.

## Child 2. `TateStructure.finite_torsion` and `TateStructure.exists_root_class`

Let $k$ be a field with a specified rank-one valuation in the multiplicative copy of $\mathbb Z$ with zero adjoined. Assume $k$ is complete for this valuation. Let $B$ be a Weierstrass curve over $k$ with a supplied Tate structure $S$ as defined above. Write $q$ for its Tate parameter. The group $B(k)$ consists of the nonsingular affine $k$-points and the point at infinity. For a natural number $\ell\ne 0$, let $B(k)[\ell]=\{P\in B(k):\ell P=0\}$. The first assertion states that $B(k)[\ell]$ is finite.

If $\ell^2\leq\operatorname{Nat.card}(B(k)[\ell])$, the second assertion supplies $u\in k^\times$ and $m\in\mathbb Z$ with
$$u^\ell=q^{\,1+\ell m}\quad\text{in } k^\times.$$
The exponent on the right is an integer. The group $k^\times$ consists of all nonzero field elements.

### Source calculation at the chosen places

In the setting of the parent theorem, take $S$ on $E_{K_{w'}}$ and let $q$ be its parameter. The global torsion points give the lower bound $\ell^2\leq\operatorname{Nat.card}(E(K_{w'})[\ell])$. Hence the supplied root-class calculation gives the displayed equality in $K_{w'}^\times$.

Write $\operatorname{ord}_{w'}$ for the normalized additive valuation of $K_{w'}^\times$. The Tate $j$-invariant of $q$ agrees with the image of $j(E)$ in $K_{w'}$. The change of fields gives $\operatorname{ord}_{w'}(q)=e(w'/w)n_w$. Taking additive valuations of the root equality gives
$$\ell\,\operatorname{ord}_{w'}(u)=(1+\ell m)e(w'/w)n_w.$$
The right side is congruent to $e(w'/w)n_w$ modulo $\ell$. Thus $\ell$ divides $e(w'/w)n_w$. Since $\ell$ is prime and $\ell\nmid n_w$, it divides $e(w'/w)$.
