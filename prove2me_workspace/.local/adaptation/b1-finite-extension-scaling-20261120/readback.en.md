# Scaling the finite height in a number field extension

Let $k$ and $K$ be number fields with an algebra map $k\to K$. Let $v$ and $w$ be finite places of $k$ and $K$, with prime ideals $\mathfrak p_v$ and $\mathfrak p_w$. Write $w\mid v$ when $\mathfrak p_w\cap\mathcal O_k=\mathfrak p_v$. The absolute ramification indices and residue degrees at $w$ and $v$ are $e_w,f_w$ and $e_v,f_v$. Set $d_K(w)=e_wf_w$ and $d_k(v)=e_vf_v$. If $w\mid v$, write $e(w/v)$ and $f(w/v)$ for the relative indices.

1. `under_int_eq_under_int`. If $w\mid v$, then $\mathfrak p_w\cap\mathbb Z=\mathfrak p_v\cap\mathbb Z$. Contraction along $\mathbb Z\to\mathcal O_k\to\mathcal O_K$ gives this equality.
2. `residueChar_eq_of_liesOver`. If $w\mid v$, the residue characteristics at $w$ and $v$ agree. Both characteristics generate the same prime ideal of $\mathbb Z$.
3. `ramIdx_eq_mul`. If $w\mid v$, then $e_w=e_v\,e(w/v)$ by the ramification index formula for the tower.
4. `inertDeg_eq_mul`. If $w\mid v$, then $f_w=f_v\,f(w/v)$ by the degree formula for the tower of residue fields.
5. `localDeg_eq_mul`. If $w\mid v$, then $d_K(w)=d_k(v)e(w/v)f(w/v)$.
6. `relLocalDeg`. For any pair $w,v$, define the natural number $d(w/v)$ as the product of the Lean expressions for the relative ramification index and residue degree. It gives the relative local degree for $w\mid v$.
7. `relLocalDeg_ne_zero`. If $w\mid v$, then $d(w/v)\ne0$. The relative ramification index is nonzero. The residue degree formula and $f_w>0$ give a nonzero relative residue degree.
8. `sum_localDeg_liesOver`. Let $S$ be a finite set with $w\in S\iff w\mid v$. Then $\sum_{w\in S}d_K(w)=[K:k]d_k(v)$. Match the places with the primes above $\mathfrak p_v$ and apply the formula for the local degree at each place.
9. `sum_relLocalDeg_liesOver`. For the same full fiber $S$, $\sum_{w\in S}d(w/v)=[K:k]$. Cancel the positive factor $d_k(v)$.
10. `apply_algebraMap_eq_pow`. If $w\mid v$, then $|y|_w=|y|_v^{d(w/v)}$ for every $y\in k$. The left side uses the image in $K$. The absolute values are those of the project's finite places. For a nonzero element, the logarithm formula combines the ramification index and residue degree. For zero, use $d(w/v)>0$.
11. `posLog_apply_algebraMap_eq`. If $w\mid v$, then $\log^+|y|_w=d(w/v)\log^+|y|_v$ for every $y\in k$. The Lean expression uses $\log^+(a)=\max(\log a,0)$ with $\log 0=0$.
12. `finHeight_algebraMap`. For every $y\in k$,
    $$h_{\mathrm{fin}}^K(y)=[K:k]h_{\mathrm{fin}}^k(y),\qquad
    h_{\mathrm{fin}}^F(y)=\sum_{u\text{ finite in }F}\log^+|y|_u.$$
    On the left, take the image of $y$ in $K$. Group the terms with finite support by their lower place. For a positive lower-place term, the nonzero relative degree ensures that all places above it occur in the sum. Apply the relative degree sum on that fiber.

[Source declarations and target commands](SOURCE_LEDGER.md)
