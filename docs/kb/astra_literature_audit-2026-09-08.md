# Targeted literature and official-companion audit, 2026-09-08

**Outcome:** no inspected theorem closes the exact production `|Bad| <= n` obligation. The fresh official-main status is useful; **68.04 and its mathematical direction were already known to this campaign**, as witnessed by `docs/kb/proximity-astra-companion-2026-09-04.md` and `scripts/probes/astra_companion_6804_ordinary_gates.lean`. Do not count this audit as a new mathematical advance or a new production bound.

The same-session three-source argument was subsequently independently reviewed:
the remaining first-step branches are now `|J|<=2`; the literature comparisons
below retain the more general exceptional-budget formulation.

## Production target and exact quantifiers

`n=2^30`, `k=2^29`, `P=365375409332725729550921208179070755120141565953`. The integer budget is `floor(P/2^128)=n`. At `delta_1=(2^28+1)/n`, a witness support needs `t=3n/4-1=805306367` points.

For **every** received pair `(u,v)`, let J contain **all** degree-<k pairs with joint core >=t. The newly audited first step proves `|J|<=4`, `|Bcovered|<=n`, and `|J|=4 => Bad=Bcovered`. Thus the exact remaining obligation is, for all `(u,v)` with `|J|<=3`,

`|Bad \ Bcovered| <= n-|Bcovered|`.

A sufficient but potentially stronger uniform target at `|J|=j` is `|Bad \ Bcovered| <= n-j*(n-t)`; its j=3 allowance is `n/4-3=268435453`. An exception set may depend on `(u,v)` but **cannot depend on the selected support**. Extensions may depend on the support. The spike in `07-audit/audit.md` rules out declaring this exceptional set empty.

## BCHKS25: exact available theorem, insufficient constant

[Author-hosted paper, Theorem 4.6, pp.28–29](https://www.math.toronto.edu/swastik/rs-proximity-gaps-2025.pdf) treats degree-M seed curves and the original same-support event. Its code has dimension `k_paper+1`, so our reduced rate is `rho=(k-1)/n`, not k/n. For `0<gamma<1-sqrt(rho)`,

`|E| <= M * ([2(m+1/2)^5 + 3(m+1/2)*gamma*rho]/[3*rho^(3/2)] * n + (m+1/2)/sqrt(rho))`,

`m=max(ceil(sqrt(rho)/(1-sqrt(rho)-gamma)),3)`.

At our first step with M=1, m=17. Direct high-precision evaluation gives leading coefficient approximately `3094887.360259`, additive term `24.748737`, and cap approximately `3.3231099992791176e15`. This is over three million times n. Even a full correct formalization of that bound therefore does not close our target. No `O(n)/P` slogan fixes this constant gap.

The freshly fetched [ArkLib #865](https://github.com/Verified-zkEVM/ArkLib/pull/865) at `272fe77c77fc0ae18506fb245983af8c01b23ef0` supplies precisely the global-exception-set bridge above (`ExceptionalSet.lean`) but expressly does not prove the RS exception count. #888/#890 and integration `83352bc58d93029cacdc30f8ff4bd5db5cebf432` are algebraic-building-block opportunities documented in the existing remote audit, not a substitute finite count. No merge/build attempted; toolchain boundary preserved.

## Current official companion: refresh, not a newly discovered campaign advance

Live API pinned main to [bac8e813cd07f0b73ff7d68402e3b1944b0927f3](https://github.com/proximity-prize/proximity-prize/commit/bac8e813cd07f0b73ff7d68402e3b1944b0927f3), September 8 10:39:34Z. Current lower metadata is `6804`, radius `10341375/33554432`. Source exports exactly `ProtocolClaim 6804 10341375 33554432`.

[PR #517](https://github.com/proximity-prize/proximity-prize/pull/517) merged September 6 08:36:41Z; retained source commit `1b2ca03c8b0ad8a53d647f1eb13aa60b928b8a2c`. The construction uses coefficient-dependent second jets, common/residual factor accounting, six first-jet phases and finite certificate tables. This is relevant technique, but the campaign already has companion arithmetic explorations; this audit does not establish a fresh coefficient theorem beyond them.

Source-inspected profile: KoalaBear sextic field `(2130706433)^6`, domain `2^18`, base dimension `2^17`, eight interleavings; errors 80791, agreements 181353. Exact source constants are MCA budget `274980722500476168` and scalar-list budget `5610918919`. The public claim bounds **certified IRS combination-round error**, and its score is a 128-fold spot-check term. It is not a theorem about our prime-field code or its n/P target. The exact-source theorem was read, not rebuilt or independently kernel-replayed here.

[PR #45](https://github.com/proximity-prize/proximity-prize/pull/45) merged August 21 02:57:32Z at head `e4c8dfbf73ba1cc152e72d67c63435aae1021397`, radius `305433/1048576`, score 63.58. [PR #72](https://github.com/proximity-prize/proximity-prize/pull/72) merged August 21 09:15:15Z at `19bc7d3e21b2261257e1961acd720b2c395d87e1`, radius `307083/1048576`, score 63.99. #72 builds universal implicit numerators before factor selection, yielding actual-degree aggregate resultant accounting; its final bad-seed cap is `10^17` and list cap 30000 on the same companion field. These donor bounds do not transport numerically to our n budget.

## Two recent papers: exact relevance boundary

[Goyal–Guruswami–Sun–Wootters, arXiv:2607.08516v1, Theorem 5.6](https://arxiv.org/html/2607.08516v1#S5.SS2): for **random evaluation-point RS codes**, rate `R<=1-delta-2eta`, subject to `q>=n exp(Omega(ell^4/eta^7))` and sufficiently large n, MCA numerator is `ell*n*ceil((1-R)/eta)+O(ell^2/eta^3)` with high probability over the code. At R=1/2, ell=1 and our delta_1, eta is strictly below 1/8, so the displayed leading integer factor is at least 5. It neither certifies the fixed subgroup nor reaches n, even before the remainder. No exact usable remainder constant was extracted.

[Gao–Yang–Xu–Kan, arXiv:2607.10572v1, Lemmas 2–3](https://arxiv.org/html/2607.10572v1#S3): list-decoding counterexamples yield lower bounds `ceil((L+1)q/(q+L))` on bad scalars after appending a coordinate (radius p*n/(n+1)) or puncturing/appending (radius p). This is a lower-bound mechanism for a related code, not a universal upper bound. The constructive common-support-plus-one reasoning is relevant to our old order-16 attack but supplies no exceptional-count control for |J|<=3. The paper's maximal-set wording should not replace our directly checked same-support event.

## Scope / artifacts

Read root/cone guides, existing September 8 audit, order-16 note, first-step and independent audit, companion note and existing arithmetic theorem declarations. Web/API reads were current; the source snapshot and PR metadata are retained beside this report. No tracked edit, ref change, merge, commit, build, paid service or external message occurred. Search was targeted, not an exhaustive new-publication survey.
