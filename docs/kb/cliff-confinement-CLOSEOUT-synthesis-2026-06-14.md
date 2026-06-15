# Cliff-confinement survivor — CLOSEOUT synthesis (6-leg fleet + adversarial verify), 2026-06-14

**Bottom line (honest): the audit's top survivor — binding-radius char-uniformity / "cliff
confinement" — is STRUCTURALLY REAL and genuinely off the BGK char-sum wall, but adversarial
verification shows it is PRIZE-INERT: the char-0 calibration it exposes pins δ\* AT the Johnson
radius 1−√ρ (±1/n), and the window interior is exponential. It reproduces the Johnson barrier; it
does not break it. The beyond-Johnson prize redirects to the BGK/deep-moment sup-norm face — the only
remaining one. This is a decisive negative refinement, not a closure.**

## What was driven to ground
Following the #407 audit (which flagged cliff confinement as the one survivor the piecemeal attacks
lumped into "BGK"), a 6-leg fleet investigated each open leg and adversarially verified it. The five
analytic legs returned; the 6th (large-n numerics) was completed by direct takeover (n≤24 exact,
n=32 by sampling).

## The five established facts (all CONFIRMED, in-regime, novel)
1. **Char-uniformity at the binding radius (cliff confinement).** At the binding radius a* (smallest
   agreement with realized far-line incidence ≤ budget~n), char-p incidence = char-0 incidence for
   all PROPER 2-power subgroups (q≠n+1). Verified exactly n≤24 (ρ∈{1/8,1/4,1/2}; best test n=24 ρ=1/4
   NONZERO binding a*=10, char-p=char-0=12 for all primes q≫n³), sampled to n=32 (full window, heavy=0).
   The only systematic violator is q=n+1 (full group), prize-excluded.
2. **Mechanism (why char-uniform).** The bad scalar at scale k+1 is γ_R=−[R](x^b)/[R](x^a); a char-p
   agreement needs the divided difference D(R,i)=[R](x^a)[R∪i](x^b)−[R](x^b)[R∪i](x^a) — NONZERO in
   char-0 — to vanish mod a prime above q. Cleared of denominators, D(R,i)∈Z[ζ_n] has q-INDEPENDENT
   height, so char-p≠char-0 only for the sporadic finite primes dividing fixed cyclotomic norms.
   This is the SAME height/rigidity as the PROVEN Q1 bad-prime bound (p≤(2k)^{2k/r},
   _BadPrimeBoundCore.lean). Refinement: the binding is OVER-determined (witness s*≥k+2, s−k≥2); the
   p-dependent excess lives ONLY at the deepest under-det scale s=k+1 on the bad side (δ>δ*).
   Proven half in Lean: _RingHomBadScalarMono.lean (merge-only char-p ≤ char-0).
3. **Closed form (the calibration value).** The char-0 binding incidence for the monomial direction
   dir(k,t) is the single binomial **I(t) = C(n/2^s, t/2^s)**, s=ceil(log₂(need+1)), need=t−k−1,
   zero unless 2^s|t. Derived via Newton (e_j=0⟺p_j=0) + Lam-Leung/Mann (vanishing 2-power-root sums
   ⟺ antipodally balanced) + μ₂-quotient even/odd descent (_AntipodalEvenOddDescent.lean). EXACT at
   every computable cell (n≤32); the survivor datum n=16 k=8 binding=4 = C(4,3). q-independent,
   character-sum-free.
4. **LD = MCA at the binding radius.** Raw list-decoding super-list L_super = Σ_{bad γ}(base RS[k]
   list at line_γ); MCA = #{bad γ}; GAP = Σ(base_list−1) is a benign ADDITIVE +1 (the ×n orbit-factor
   hypothesis is REFUTED). At δ* both are O(1) and char-uniform. So the reframing covers BOTH grand
   challenges. Caveat: at low rate the binder is imprimitive x^{n/4} (b>k+1), so the matching
   super-code is C⊕⟨x^b⟩, NOT the canonical interleaved RS[k+1].
5. **Off-BGK at the binding radius.** All four above make δ* at the binding a char-0 vanishing-sums
   coincidence count — no character sum / additive energy / sub-Gaussian period / deep moment.

## The decisive REFUTATION (why it's prize-inert)
The char-0 worst-direction (monomial) binding calibration was computed vs the Johnson radius 1−√ρ:
- **δ\* = Johnson ± 1/n**, all rates: ρ=1/4: δ*∈{0.375(n8),0.417(n12),0.5625(n16),0.55(n20)},
  (δ*−J)·n∈{−1,−1,+1,+1}; ρ=1/2: (δ*−J)·n∈{−0.34,−0.51,+0.31}; ρ=1/8 similar. δ* converges to the
  Johnson EDGE from just inside (Θ(1/n)), NOT into the window interior, NOT toward capacity.
- **Window interior is EXPONENTIAL.** Per-radius incidence is flat below Johnson then explodes toward
  C(n,k+1)≈2^{H(ρ)n}: n=16 k=8 I=[4(δ*),40,8496], ratios 10×,212×, vs C(16,9)=11440 (maxI/C=0.74);
  ratios GROW with n. So I(δ)≫budget for every constant δ above Johnson ⟹ no beyond-Johnson δ* from
  this counting.
The closed form and the refutation are CONSISTENT: I(t)=C(n/2^s,t/2^s) is exact AND its
threshold-crossing (t* = max{t: C(n/2^s,t/2^s)>budget}) lands at δ*=Johnson+Θ(1/n). The binomial is
small at the binding radius (char-uniform) and exponential in the interior.

## Honest verdict
- **Cliff confinement: CONFIRMED** (char-uniformity + mechanism + closed form + LD=MCA), genuinely
  off-BGK, a real and novel mathematical contribution worth formalizing.
- **Prize: NOT delivered.** The char-0 monomial calibration reproduces the Johnson barrier; it does
  not break it. "One rung beyond Johnson" is real but Θ(1/n), vanishing asymptotically. The window
  INTERIOR (the actual capacity-distance prize) has exponential char-0 incidence — no beyond-Johnson
  δ* from far-line counting.
- **Redirect:** the beyond-Johnson prize, if true at all, is NOT a far-line-incidence/counting
  phenomenon (the counting reproduces Johnson) — it must live in the BGK/deep-moment sup-norm analytic
  object, OR the premise (beyond-Johnson for explicit smooth RS) is itself the open phase transition
  (consistent with: capacity-distance MCA for explicit RS proven impossible under poly soundness).

## Lean targets (valuable regardless of prize — they lock in correct structure)
1. `binding_incidence_eq_choose : I(n,k,t) = if 2^s ∣ t then C(n/2^s, t/2^s) else 0` — induction on m,
   base = LamLeungMultisetAntipodal.multiset_antipodal_iff (need=1), step = _AntipodalEvenOddDescent
   μ₂-quotient. Turns the calibration from numerics into a proven q-independent closed form.
2. Over-det char-uniformity: `q > H(n,k) ⟹ char-p incidence at s* = char-0` — extend
   _RingHomBadScalarMono.lean (merge-only ≤) with a no-saturation lemma at over-det scale (s−k≥2) +
   the N(D(R,i))-height separation bound. Both finite/algebraic (cyclotomic norms), NOT analytic.
3. `no_beyond_johnson_from_char0 : δ*_char0 ≤ (1−√ρ) + 1/n` — the honest negative: the char-0
   far-line calibration pins δ* at Johnson, formally redirecting the prize off the counting face.

## Ranked next moves
- (novelty 8 / insight 9 / proximity-to-prize 3 / feasibility 8) Formalize targets 1–2 — real,
  landable, lock in the off-BGK structural facts.
- (n 6 / i 8 / prox 2 / feas 7) Formalize target 3 — the honest Johnson-reproduction no-go.
- (n 5 / i 6 / prox 5 / feas 2) Return to the BGK/deep-moment sup-norm face — the only remaining
  prize lever — with the now-sharpened knowledge that counting cannot beat Johnson.

Probes (this session): /tmp/large_n_confirm.py, /tmp/unified_compare.py; legs' probes in
scripts/probes/probe_ld_vs_mca_binding_radius.py and /tmp (some repo copies wiped by swarm branch
resets). Workflow wf_c60f562a-b3f (6 legs + 3-lens adversarial verify, stopped after harvest).

## CONVERGENCE with the concurrent "Plotkin-proxy" course-correction (cross-check)
A concurrent effort (memory issue407-farline-incidence-is-plotkin-proxy; fast Rust engine
scripts/rust-pg) independently concluded far-line incidence is a PROXY, not the true MCA δ*:
δ*_MCA ≥ Johnson AND ≤ δ*_farline (since ε_MCA ≥ incidence/q). This AGREES with this closeout's
bottom line (far-line counting is prize-inert / reproduces Johnson). Nuance reconciled honestly:
- Their "exact δ*_farline = 1/2+(1/(2ρ)−1)/n → 1/2" matches THIS leg's MONOMIAL calibration at ρ=1/4
  (n16→0.5625, n20→0.55) but not ρ=1/2 (their 0.5 vs my monomial 0.3125).
- Resolution: δ*_farline is an UPPER bound on δ*_MCA, and the MONOMIAL line is a valid affine line, so
  the monomial incidence gives a TIGHTER upper bound. At ρ=1/2 it pins δ*_MCA ∈ [Johnson=0.293, 0.3125]
  — i.e. the monomial proxy is sharper and lands ON Johnson, strengthening (not contradicting) the
  "reproduces Johnson" conclusion. Both efforts agree: the true MCA δ* (≥Johnson floor) is the harder
  BGK object; the right target object is ABF26 §4.5 mcaConjecture, NOT far-line incidence.
