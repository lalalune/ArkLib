"""
#407 fourier-uncertainty-dyadic — REFINED.

Test the CORRECT rigidity: when prod_{s in S}(X-zeta^s) = X^a + lower-than-(a-t),
i.e. it lies in F[X^?]... Let me test multiple coset hypotheses and find which one
matches the vanishing set EXACTLY.

Key reframings:
 (A) e_1=..=e_{t-1}=0  <=>  poly P(X)=X^a + c_t X^{a-t} + ... has a GAP of length t-1 below leading.
 (B) The Lam-Leung tower fact (in-tree): P in F[X^s] (i.e. S = union of mu_s-cosets, index-closed
     under +N/s) <=> ALL e_j vanish except multiples of s. That's a DIFFERENT (stronger) condition
     than just the FIRST t-1 vanishing.

So the honest question: among S with FIRST t-1 e's vanishing, which are mu_s-coset unions and for
which s? And is the COUNT controlled?
"""
import itertools, cmath, math

def poly_coeffs(idx_set, N):
    zeta = [cmath.exp(2j*math.pi*i/N) for i in range(N)]
    coeffs=[1.0+0j]
    for i in idx_set:
        p=zeta[i]; new=[0j]*(len(coeffs)+1)
        for k,c in enumerate(coeffs):
            new[k]+=c; new[k+1]+=-p*c
        coeffs=new
    return coeffs  # coeffs[k]=(-1)^k e_k

def vanishing_pattern(idx_set,N):
    c=poly_coeffs(idx_set,N); a=len(idx_set)
    return [k for k in range(1,a+1) if abs(c[k])>1e-7]  # nonzero e_k positions

def max_s_coset(idx_set,N):
    # largest s | N such that S is closed under +N/s (union of mu_s cosets, mult by zeta^{N/s})
    S=set(idx_set); best=1
    for s in range(1,N+1):
        if N%s: continue
        step=N//s
        if all((x+step)%N in S for x in S):
            best=max(best,s)
    return best

def gap_below_lead(idx_set,N):
    # the largest t such that e_1..e_{t-1} all vanish (consecutive gap below leading coeff)
    c=poly_coeffs(idx_set,N); a=len(idx_set)
    t=1
    while t<a and abs(c[t])<1e-7:
        t+=1
    return t  # e_1..e_{t-1}=0, e_t != 0  (or t=a if prod only)

print("For each S subset mu_N: relate consecutive-gap t to max mu_s-coset-closure s")
print("Hypothesis to test: consecutive gap t  =>  S closed under +N/(largest power of 2 <= ...)?")
for N in [8,16,32]:
    print(f"\n=== N={N} ===")
    # collect, for each gap value t, the distribution of max_s_coset
    from collections import defaultdict
    table=defaultdict(lambda: defaultdict(int))
    examples=defaultdict(list)
    for a in range(2,N+1):
        for idx in itertools.combinations(range(N),a):
            t=gap_below_lead(idx,N)
            if t<2: continue
            s=max_s_coset(idx,N)
            table[t][s]+=1
            if len(examples[(t,s)])<2: examples[(t,s)].append(idx)
    for t in sorted(table):
        dist=dict(table[t])
        print(f"  gap t={t:2d}: distribution of max-coset-s = {dist}")
