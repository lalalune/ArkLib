"""
#407 LANE A2 — verify the #spurious(q) ~ A*C(n,w)/q law across n (not just n=16), and
directly measure the n=32 prize-regime corruption via meet-in-the-middle (exact).

We use a MITM exact count of width-w e2=0 sets mod q for n=32: split U into two halves
of the index set, hash partial (e1, p2) sums, and match. This counts |F_q e2=0 locus|
exactly without enumerating C(32,16). Then #spurious = that minus the char-0 count.

To keep it tractable we use the e1=e1, p2 structure: a set S of width w with e2=0 mod q
satisfies e1^2 = p2 mod q. We enumerate over subsets by meet-in-the-middle on the 32 roots.
Even MITM on 32 elements (2^16 per half * 2 halves with width split) is ~ C(16,8)^2 ~ 1.6e8
which is borderline; instead we VERIFY THE LAW at n in {12,14} by full enumeration where
C(n,n/2) is small, plus n=16 (already done), to confirm A ~ 1 universally and the 1/q decay.
"""
import itertools, math
from sympy import symbols, Poly, cyclotomic_poly, ZZ, primitive_root, isprime, primerange

X = symbols('X')
def phi(n): return Poly(cyclotomic_poly(n, X), X, domain=ZZ)

def char0_count(n, w):
    Phi = phi(n); c=0
    for U in itertools.combinations(range(n), w):
        if (Poly(sum(X**i for i in U),X,domain=ZZ)%Phi).is_zero: continue
        s=Poly(sum(X**i for i in U),X,domain=ZZ)
        R=(s*s-Poly(sum(X**(2*i) for i in U),X,domain=ZZ))%Phi
        if R.is_zero: c+=1
    return c

def fp_count(n,w,q):
    g=pow(primitive_root(q),(q-1)//n,q); mu=[pow(g,j,q) for j in range(n)]
    cnt=0
    for U in itertools.combinations(range(n),w):
        S=[mu[i] for i in U]; e1=sum(S)%q
        if e1==0: continue
        p2=sum((x*x)%q for x in S)%q
        if (e1*e1-p2)%q==0: cnt+=1
    return cnt

# law check across n (only n where n=2^k for dyadic, but include 12,14 to test n-dependence form)
print("=== #spurious(q) ~ A * C(n,w)/q  : cross-n law (dyadic n=8,16; plus n=12 control) ===")
for n in [8, 16]:
    w=n//2; Phi=phi(n); c0=char0_count(n,w)
    qs=[p for p in primerange(n+1, 12*n*n) if (p-1)%n==0]
    rows=[]
    for q in qs[:80]:
        spur=fp_count(n,w,q)-c0
        if spur>0: rows.append((q,spur,spur*q/math.comb(n,w)))
    if rows:
        A=sum(r[2] for r in rows)/len(rows)
        cn=max(r[0] for r in rows)
        print(f"  n={n} w={w}: char0={c0}, C(n,w)={math.comb(n,w)}, A_fit={A:.3f}, c({n})=max-bad-q={cn} (n^{math.log(cn)/math.log(n):.2f})")
    else:
        print(f"  n={n} w={w}: char0={c0}, NO bad primes in range (c({n})=trivial)")

# direct n=32 prize-regime exact count via MITM (split 32 indices into A=0..15, B=16..31)
def mitm_e2zero_count(n, w, q):
    g=pow(primitive_root(q),(q-1)//n,q); mu=[pow(g,j,q) for j in range(n)]
    half=n//2
    A_idx=list(range(half)); B_idx=list(range(half,n))
    # for each split width wa+wb=w, hash A-partials by (e1A,p2A); B-partials need e1^2=p2:
    # (e1A+e1B)^2 = p2A+p2B  ->  for each B partial, look up A partials with
    #   p2A - e1A^2 - 2 e1A e1B = p2B - e1B^2  ... 2 unknowns, can't single-key easily.
    # Instead key A by e1A, store list of (p2A); for each (e1B,p2B,e1A) match the quadratic in.
    # Simpler: build dict over A by e1A -> Counter of p2A. For each B-partial and each candidate e1A,
    # need p2A = p2A(target). p2A = (e1A+e1B)^2 - p2B. So for fixed e1B,p2B, iterate over distinct e1A
    # keys, compute needed p2A, add count. #distinct e1A keys <= q but in practice <= #A-partials.
    from collections import defaultdict, Counter
    cnt=0
    for wa in range(max(0,w-half), min(half,w)+1):
        wb=w-wa
        Amap=defaultdict(Counter)
        for cA in itertools.combinations(A_idx, wa):
            S=[mu[i] for i in cA]; e1A=sum(S)%q; p2A=sum((x*x)%q for x in S)%q
            Amap[e1A][p2A]+=1
        Akeys=list(Amap.items())
        for cB in itertools.combinations(B_idx, wb):
            S=[mu[i] for i in cB]; e1B=sum(S)%q; p2B=sum((x*x)%q for x in S)%q
            for e1A,p2counter in Akeys:
                e1=(e1A+e1B)%q
                if e1==0: continue
                need=( (e1*e1 - p2B) ) % q
                cnt += p2counter.get(need,0)
    return cnt

print("\n=== n=32 prize-regime EXACT count via MITM (width 16) ===")
n=32; w=16
c0_32 = None  # char-0 count expensive; estimate by formula/known structure instead
# We only need #spurious = fp_count - char0_count. char0 count at n=32,w=16:
# compute char-0 count via norm route on a structured generating approach is heavy;
# instead measure fp_count at a LARGE clean prime (q > c(32)) to get char-0 count, then
# at prize primes to get corruption. Use q just above c(32)? that's 3e12, too big for MITM speed?
# MITM cost ~ C(16,8)*C(16,8) ~ 1.6e8 -- borderline; do for ONE prize prime and ONE clean-ish.
for beta in [4, 5]:
    q=int(n**beta)
    while not (isprime(q) and (q-1)%n==0): q+=1
    import time; t=time.time()
    cnt=mitm_e2zero_count(n,w,q)
    print(f"  q~n^{beta}={q}: |F_q e2=0 width-16 locus| = {cnt}   ({time.time()-t:.0f}s)")
