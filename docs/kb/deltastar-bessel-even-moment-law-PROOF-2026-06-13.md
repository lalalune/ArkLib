# PROOF of the Bessel even-moment law E_r(μ_n) = (2r)![x^r] I₀(2√x)^{n/2} (#389)

**Status: PROVEN** (was conjectured/18-of-18-numeric; now a complete rigorous proof). Resolvable
structural layer (NOT the prize — holds only in the no-genuine-relation regime), but a clean novel
closed form, formalizable. Author: δ* lane, 2026-06-13.

## Statement
n = 2^m, μ_n ⊂ F in the no-genuine-relation regime (char 0, or char p above the Lam–Leung threshold
where the only vanishing sums of n-th roots are antipodal). Then the additive energy moment
  E_r(μ_n) = #{(a,b)∈μ_n^{2r} : Σa_i = Σb_j} = (2r)! · [x^r] I₀(2√x)^{n/2},  I₀(2√x)=Σ_q x^q/(q!)².

## Proof (5 steps; each classical/rigorous)

Write μ_n as N=n/2 antipodal pairs {±ζ_1,…,±ζ_N}. E_r = Σ_v R_r(v)², R_r(v)=#{a∈μ_n^r: Σa=v}.

(0) NO-RELATION ⟹ value = net axis coefficients. For n=2^m the ℚ-relation lattice among the n roots
has rank n/2 and is spanned EXACTLY by the antipodal relations ζ+(−ζ)=0; so the reps ζ_1,…,ζ_N are
ℚ-independent and Σa is determined by n_k = #{a_i=ζ_k} − #{a_i=−ζ_k} ∈ ℤ. Thus R_r(v)=R_r(𝐧).

(1) SINGLE-AXIS EGF = BESSEL. Ordered a-sequences with axis-k usage (p_k,q_k) number r!/∏(p_k!q_k!), so
  Σ_r (x^r/r!) R_r(𝐧) = ∏_k g_{n_k}(x),  g_m(x)=Σ_{p−q=m} x^{p+q}/(p!q!)=Σ_q x^{2q+|m|}/(q!(q+|m|)!)=I_{|m|}(2x).

(2) GRAF ADDITION THEOREM collapses the axis convolution. Summing the bivariate EGF over all 𝐧∈ℤ^N:
  Σ_𝐧 (Σ_r x^r/r! R_r(𝐧))(Σ_{r'} y^{r'}/r'! R_{r'}(𝐧)) = ∏_{k=1}^N (Σ_{m∈ℤ} I_{|m|}(2x)I_{|m|}(2y)).
  With Σ_m I_m(2x)w^m = e^{x(w+1/w)} and I_m=I_{−m}:
    Σ_{m∈ℤ} I_m(2x)I_m(2y) = [w⁰] e^{(x+y)(w+1/w)} = I_0(2(x+y)).
  Hence the sum = I_0(2(x+y))^N.

(3) EXTRACT THE DIAGONAL. I_0(2u)=Σ_q u^{2q}/(q!)², so with v=u²: I_0(2u)^N = Σ_s B_s u^{2s},
  B_s = [v^s] I₀(2√v)^N. Put u=x+y, expand (x+y)^{2s}=Σ_{r+r'=2s} C(2s,r) x^r y^{r'}. The coefficient of
  (x^r y^{r'})/(r!r'!) — which equals Σ_𝐧 R_r(𝐧)R_{r'}(𝐧) — is B_{(r+r')/2}·C(r+r',r)·r!·r'!.

(4) SET r'=r (E_r is the diagonal Σ_𝐧 R_r(𝐧)²):
  E_r = B_r·C(2r,r)·(r!)² = B_r·(2r)!/(r!)²·(r!)² = (2r)!·B_r = (2r)![x^r]I₀(2√x)^{n/2}.  ∎

## Verification
- n=2 (N=1): E_r=(2r)!/(r!)²=C(2r,r)=Σ_k C(r,k)² (Vandermonde over μ_2={±1}). ✓ (=in-tree TwoElementEnergy).
- n=4 (N=2): r=1→2·2=4=E_1=n ✓; r=2→24·(1/4+1+1/4)=36=3n²−3n ✓.
- general r=2: recovers E_2=3n²−3n (in-tree Sidon energy). ✓  Matches the 18/18 numeric promotion.

## Scope (honest)
This is the RESOLVABLE layer: it holds in the no-relation regime (small subgroup n<log_n p, or char 0).
In the PRIZE regime (large n, p<n^r) char-p coincidences break the antipodal-only property past
r>log_n p, and E_r DEVIATES upward from the Bessel value — that deviation is exactly the open core
(the moment wall). So the Bessel law PROVES the clean baseline E_r^{(0)} = (2r)![x^r]I₀(2√x)^{n/2}
against which the prize "halo excess" E_r − E_r^{(0)} is measured. Novel closed form (additive moments
of a multiplicative subgroup = Bessel coefficients via Graf's theorem); formalizable (needs: Lam–Leung
n=2^m antipodal [in-tree LamLeungTwoPow], the multinomial EGF, and Graf's addition theorem).

PROMOTED and PROVEN. Grind status: the first conjecture that survived refutation (true) AND is now
fully proven — but it is the resolvable structural layer, NOT the prize open core (which is the
deviation past the no-relation threshold).
