# Fourier-flat reformulation: #bad = #distinct first-nonzero Fourier coeff of spectrally-flat sets (2026-06-13)

Continuing the EXACT δ* characterization. By NEWTON'S IDENTITIES, the worst-direction conditions
`e_1(T)=…=e_{m-1}(T)=0` ⟺ power sums `p_1=…=p_{m-1}=0`, and the readout `γ ∝ e_m ∝ p_m`. Writing
`T={ζ^a : a∈A}`, **`p_j(T) = Σ_{a∈A} ζ^{ja} = \hat{1_A}(j)`** (Fourier coefficient of the indicator). So
the `dir(k,t)` bad-count is:
> `#bad = #{ distinct \hat{1_A}(m) : A⊆ℤ/n, |A|=k+m, \hat{1_A}(1)=…=\hat{1_A}(m-1)=0 }`
= # distinct FIRST-NONZERO Fourier coefficients over **spectrally-flat** sets (zero low spectrum).
VERIFIED (`probe_fourier_flat_count.py`): n=16,k=8,m=2 → 40 (matches the bad-count curve exactly);
m=4 → 4; m=3 → 0 (no flat set of that size — a generalized parity/existence obstruction).

## Coherent q-independent theory of δ* built this session (#400 cone)
1. `e_2=0 ⟺ P(ζ)²=P(ζ²)` (verified 50626 cases); signed-single decomposition `e_1=Σ_singles ±ζ^j`.
2. General-direction reduction: `dir(a,b)` bad ⟺ deg-(k..t−1) coeffs of `X^a+γX^b mod m_T` vanish
   = (t−k) linear conditions in γ; q-independent symmetric-function constraints on T.
3. Worst direction has `a=k` (evades the mod-4 obstruction on dir(k+1,k+2)); bad-count curve MONOTONE.
4. **EXACT δ* = 1−t*/n, t* = max{t : #bad(t) > ε*q}** — inverse of a monotone q-independent count.
5. For `dir(k,t)`: #bad = #distinct `\hat{1_A}(m)` over spectrally-flat A (this note). The Kambiré
   construction = subgroup-coset unions = spectrally-flat (Fourier support on the dual subgroup) ⟹
   realizes these, recovering `δ* ≤ 1−ρ−2/s*`.

## Honest open pieces (all q-independent / combinatorial, NOT the char-sum wall)
(a) The full worst-case is the MAX over ALL directions (dir(k,b), b≥t), not only dir(k,t) — verified
    dir(8,12) beats dir(8,11) at t=11. The closed worst-direction-vs-band map is unfinished.
(b) The closed form / EXTREMALITY of `#bad(t)`: is the spectrally-flat count maximized by the coset
    construction (⟹ exactly C(s,r) ⟹ exact δ*)? = a Fourier-extremal problem over ℤ/2^μ.
(c) CAVEAT: "distinct first-nonzero Fourier coeff of flat sets" connects to spectral-flatness/
    flat-polynomial theory — verify it is genuinely combinatorial-closed and does not re-encode subgroup
    additive energy.

## Status
The δ* characterization as the inverse of a monotone q-independent count is solid and verified at n=16.
The Fourier-flat framing is a novel, clean restatement of the remaining content. NOT a closure (open: full
worst-direction map + extremality). RETRACTED earlier: s_max=μ−1 (false n=64). This is the most
prize-shaped, character-sum-free handle of the effort; the open pieces are finite/Fourier combinatorics.
