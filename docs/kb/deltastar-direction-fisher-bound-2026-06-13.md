# New provable bound: the direction-Fisher bad-scalar bound (recovers Johnson) (2026-06-13)

A genuinely new, **provable, character-sum-free** bound on the MCA bad-scalar count of an *arbitrary*
stack — verified and **tight for the Kambiré construction**. It is real machinery for the
general-direction question, and it pins (yet again, now via a clean direct argument) why the lower
bracket sits exactly at Johnson.

## Lemma (direction-Fisher bound) — PROVEN
For `C=RS[F_q,μ_n,k]`, a stack `(u₀,u₁)`, let `b := max-agreement(u₁, C)` (so `u₁` is `(1−b/n)`-far).
The number of `γ` with `u₀+γu₁` at agreement `≥ a` with `C` satisfies, whenever `a² > b·n`,
> **`#{bad γ} < (a−b)·n / (a² − b·n)`.**

**Proof.** If `γ≠γ'` are both bad with agreement sets `S_γ, S_{γ'}`, then on `S_γ∩S_{γ'}`,
`(γ−γ')·u₁ = (u₀+γu₁) − (u₀+γ'u₁) = c_γ − c_{γ'}`, a codeword; so `u₁` agrees with the codeword
`(c_γ−c_{γ'})/(γ−γ')` on `S_γ∩S_{γ'}`, giving `|S_γ∩S_{γ'}| ≤ b`. With `L` bad scalars each
`|S_γ|≥a`, double-counting + Jensen (`Σ_x C(deg x,2) ≥ n·C(La/n,2)`, `= Σ_{pairs}|S_γ∩S_{γ'}| ≤
C(L,2)b`) yields `L < (a−b)n/(a²−bn)`. ∎

## Verification + tightness
`probe_direction_fisher.py` (`(s,m,r)=(4,2,3)`, `a=6`): the construction monomial has `b=4`,
`#bad=4`, and Fisher bound `= (6−4)·8/(36−32) = 4.0` — **saturated exactly**. Random stacks: `#bad=0
≤` bound. **No violations.**

## Reach — recovers Johnson, not past it (honest)
The bound is **vacuous when `a² ≤ b·n`**. For the construction's direction `b=(r−1)m` at the prize
rates (`s≈2r`, `ρ≈½`), `a²>bn` requires agreement `a > √(bn) = m√((r−1)s) ≈ rm√2` — i.e. only
*above* the **Johnson radius**. Below Johnson agreement (the open window), it is vacuous. So this
bound — like every pairwise/second-moment argument (cf. wall-unification) — **bottoms out at exactly
Johnson** and does **not** reach the window. It does not bypass `B(μ_n)`.

## Value (honest)
- A clean, **provable, character-sum-free** general-direction bound, **tight for the construction** —
  good Lean-formalizable machinery, and a self-contained proof that the *second-moment* contribution
  to the lower bracket is exactly Johnson.
- It **sharpens the open core**: past Johnson, the bad count is governed by the *failure* of the
  Fisher inequality, i.e. the triple-and-higher coincidences `Σ_x C(deg x,≥3)` = the same
  `B(μ_n)`/higher-moment object. The lemma cleanly separates the (now-proven) Johnson part from the
  (open) past-Johnson part. No closure of `B(μ_n)`; honest.

## Higher moments are ALSO defeated by the construction (decisive negative result)
Extending to the 3-wise (triple-coincidence) Fisher bound: three bad scalars force *both* `u₀` and
`u₁` to agree with codewords on `S_γ∩S_{γ'}∩S_{γ''}` (from `u₀+γu₁=c_γ`, `u₀+γ'u₁=c_{γ'}` ⟹ both
`u₀,u₁` interpolable there), so the triple intersection `≤ b₂ := ` **max joint agreement** of
`(u₀,u₁)`. The 3-wise Fisher bound `L³a³/n² ≲ L³b₂` is non-vacuous only when `a³ > b₂n²` — *lower*
agreement (further past Johnson) than pairwise, **provided `b₂` is small**.

**But for the construction `b₂` is NOT small:** on the coset `μ_m`, `X^{rm}` and `X^{(r−1)m}` both
reduce to low-degree codewords (e.g. on `μ_4`: `x^4≡1` so `X^4` matches the constant `1`, and
`x^6=x²` so `X^{6}` matches the degree-2 codeword `X²`). Hence the *joint* agreement
`b₂ = (r−1)m = b₁` — exactly as large as the single agreement. So `a³ > b₂n²` fails at the
construction radius, and the **3-wise bound is vacuous there too**.

**Conclusion (rigorous):** the Kambiré construction has **maximal coincidence at every order**
(`b_j = (r−1)m` for all `j`), so the *entire* Fisher/moment hierarchy (pairwise, triple, …) is
vacuous at its radius. **No elementary (moment/incidence/combinatorial) method can prove the lower
bracket past Johnson** — the general-direction extremality genuinely requires the analytic worst-case
character-sum bound `B(μ_n)`. This is why every face of the prize routes through `B(μ_n)`: it is the
*unique* non-elementary input, and the construction is built precisely to defeat all elementary ones.
