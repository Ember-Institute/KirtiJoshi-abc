# Logarithmic comparisons on the modular fundamental domain

## English

Let $\mathcal F$ denote `ModularGroup.fd`, the standard closed fundamental domain for $\mathrm{SL}_2(\mathbb Z)$ on the complex upper half-plane $\mathbb H$. Its points satisfy $|\tau|\ge 1$ and $|\operatorname{Re}\tau|\le 1/2$. Write $\Delta_{\mathrm{mod}}=(E_4^3-E_6^2)/1728$, $j=E_4^3/\Delta_{\mathrm{mod}}$, and $\Delta_{\mathrm{Silv}}=(2\pi)^{12}\Delta_{\mathrm{mod}}$. The logarithms below are real natural logarithms, and $e=\exp(1)$. [Fundamental domain](/home/admin-wsl/Coq/mathlib4-0df444a/Mathlib/NumberTheory/Modular.lean:367) · [Local normalizations](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceHeightsLatticeModular.lean:57)

### `modularDeltaJ_fd_comparison`

There exists a nonnegative real constant $C_\Delta$ such that for every $\tau\in\mathcal F$,
$$
\left|-\log|\Delta_{\mathrm{Silv}}(\tau)|-\log\max\{|j(\tau)|,1\}\right|\le C_\Delta .
$$

[Local declaration](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceHeightsModularComparisons.lean:31) · [Pinned Heights declaration](https://github.com/lana-agents/heights/blob/721496ca4c158e511d25d8ccf6bfe8503eda73c1/Heights/ModularJ.lean#L189)

### `modularIm_logLogJ_fd_comparison`

There exists a nonnegative real constant $C_{\mathrm{im}}$ such that for every $\tau\in\mathcal F$,
$$
\left|\log(\operatorname{Im}\tau)-\log\!\bigl(\log\max\{|j(\tau)|,e\}\bigr)\right|\le C_{\mathrm{im}} .
$$

[Local declaration](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceHeightsModularComparisons.lean:83) · [Pinned Heights declaration](https://github.com/lana-agents/heights/blob/721496ca4c158e511d25d8ccf6bfe8503eda73c1/Heights/ModularJ.lean#L447)

## 中文

记 $\mathcal F$ 为 `ModularGroup.fd`，即 $\mathrm{SL}_2(\mathbb Z)$ 作用于复上半平面 $\mathbb H$ 的标准闭基本域，其中各点满足 $|\tau|\ge 1$ 和 $|\operatorname{Re}\tau|\le 1/2$。记 $\Delta_{\mathrm{mod}}=(E_4^3-E_6^2)/1728$、$j=E_4^3/\Delta_{\mathrm{mod}}$、$\Delta_{\mathrm{Silv}}=(2\pi)^{12}\Delta_{\mathrm{mod}}$。以下对数均为实自然对数，且 $e=\exp(1)$。 [基本域](/home/admin-wsl/Coq/mathlib4-0df444a/Mathlib/NumberTheory/Modular.lean:367) · [本地归一化](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceHeightsLatticeModular.lean:57)

### `modularDeltaJ_fd_comparison`

存在非负实常数 $C_\Delta$，使每个 $\tau\in\mathcal F$ 都满足
$$
\left|-\log|\Delta_{\mathrm{Silv}}(\tau)|-\log\max\{|j(\tau)|,1\}\right|\le C_\Delta .
$$

[本地声明](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceHeightsModularComparisons.lean:31) · [固定版本的 Heights 声明](https://github.com/lana-agents/heights/blob/721496ca4c158e511d25d8ccf6bfe8503eda73c1/Heights/ModularJ.lean#L189)

### `modularIm_logLogJ_fd_comparison`

存在非负实常数 $C_{\mathrm{im}}$，使每个 $\tau\in\mathcal F$ 都满足
$$
\left|\log(\operatorname{Im}\tau)-\log\!\bigl(\log\max\{|j(\tau)|,e\}\bigr)\right|\le C_{\mathrm{im}} .
$$

[本地声明](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceHeightsModularComparisons.lean:83) · [固定版本的 Heights 声明](https://github.com/lana-agents/heights/blob/721496ca4c158e511d25d8ccf6bfe8503eda73c1/Heights/ModularJ.lean#L447)

## 日本語

`ModularGroup.fd` を $\mathcal F$ と書く。これは複素上半平面 $\mathbb H$ 上の $\mathrm{SL}_2(\mathbb Z)$ の作用の標準閉基本領域である。その各点は $|\tau|\ge 1$ かつ $|\operatorname{Re}\tau|\le 1/2$ を満たす。$\Delta_{\mathrm{mod}}=(E_4^3-E_6^2)/1728$、$j=E_4^3/\Delta_{\mathrm{mod}}$、$\Delta_{\mathrm{Silv}}=(2\pi)^{12}\Delta_{\mathrm{mod}}$ とおく。以下の対数は実数の自然対数であり、$e=\exp(1)$ である。 [基本領域](/home/admin-wsl/Coq/mathlib4-0df444a/Mathlib/NumberTheory/Modular.lean:367) · [ローカルの正規化](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceHeightsLatticeModular.lean:57)

### `modularDeltaJ_fd_comparison`

ある非負の実定数 $C_\Delta$ が存在して、任意の $\tau\in\mathcal F$ について次が成り立つ。
$$
\left|-\log|\Delta_{\mathrm{Silv}}(\tau)|-\log\max\{|j(\tau)|,1\}\right|\le C_\Delta .
$$

[ローカルの宣言](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceHeightsModularComparisons.lean:31) · [固定リビジョンの Heights の宣言](https://github.com/lana-agents/heights/blob/721496ca4c158e511d25d8ccf6bfe8503eda73c1/Heights/ModularJ.lean#L189)

### `modularIm_logLogJ_fd_comparison`

ある非負の実定数 $C_{\mathrm{im}}$ が存在して、任意の $\tau\in\mathcal F$ について次が成り立つ。
$$
\left|\log(\operatorname{Im}\tau)-\log\!\bigl(\log\max\{|j(\tau)|,e\}\bigr)\right|\le C_{\mathrm{im}} .
$$

[ローカルの宣言](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceHeightsModularComparisons.lean:83) · [固定リビジョンの Heights の宣言](https://github.com/lana-agents/heights/blob/721496ca4c158e511d25d8ccf6bfe8503eda73c1/Heights/ModularJ.lean#L447)
