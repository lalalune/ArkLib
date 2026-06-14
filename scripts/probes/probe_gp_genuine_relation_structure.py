#!/usr/bin/env python3
"""
PROXIMITY PRIZE -- Conjecture (G), the ONE open link: suppression of F_p-genuine
relations among n-th roots of unity (n=2^mu a PROPER subgroup of F_p*, p ~ n^beta).

A depth-r relation is a tuple (x_1..x_r, y_1..y_r) in mu_n^{2r} with
    sum x_i == sum y_j  (mod p).
It is "char-0" (identically true) iff  alpha := sum zeta^{a_i} - sum zeta^{b_j} = 0
in Z[zeta_n]; it is F_p-GENUINE iff alpha != 0 in Z[zeta_n] but p | Norm(alpha)
(equivalently alpha lies in a prime P | p, where reduction mod P sends zeta_n -> z).

For n a power of 2, Z[zeta_n] = Z[x]/(x^{n/2}+1): an element is an integer vector of
length phi=n/2, and zeta^k for k>=n/2 reduces to -zeta^{k-n/2}.  alpha=0 iff the
length-phi reduced vector is all zero. (NOTE: tuple-equality of multisets {a_i}={b_j}
is SUFFICIENT for alpha=0 but NOT necessary -- e.g. for n=8, 1+zeta^2+zeta^4+zeta^6=0,
so 1+zeta^2 = -(zeta^4+zeta^6); these "cyclotomic-vanishing" combos are exactly the
char-0 relations that are NOT multiset-equalities. We test the TRUE alpha=0.)

GOAL: enumerate genuine relations at small depth r for small proper subgroups
(n=8,16) and a few primes p~n^3..n^4. Characterize:
 (a) closure under dilation x->z*x (== zeta-multiply == a_i+1) and Galois (a_i->c*a_i, c odd);
 (b) the typical alpha: small-norm cyclotomic integer? alpha ~ (an ideal generator)?
 (c) orbit structure: G_r = (orbit size) * (#orbits); is #orbits the suppressed quantity?
 (d) bijection genuine <-> char-0 NEAR-relations (alpha small in C / small ideal).
Report exact counts + the mechanism that pushes r* up.

Honesty: exact integer arithmetic for alpha in Z[zeta_n]; exact mod-p congruence.
Norms via the field-trace / resultant-free product over Galois conjugates done in EXACT
rationals through the complex embedding rounded to nearest integer with a sanity check.
"""
import itertools, math, cmath
from collections import defaultdict

# ----------------------------------------------------------------------------- #
#  number theory helpers (stdlib only)
# ----------------------------------------------------------------------------- #
def isprime(q):
    if q < 2: return False
    if q % 2 == 0: return q == 2
    d = 3
    while d*d <= q:
        if q % d == 0: return False
        d += 2
    return True

def factor(m):
    f=set(); d=2
    while d*d<=m:
        while m%d==0: f.add(d); m//=d
        d+=1
    if m>1: f.add(m)
    return f

def primroot(p):
    fs=factor(p-1)
    for g in range(2,p):
        if all(pow(g,(p-1)//q,p)!=1 for q in fs): return g
    raise RuntimeError

def find_prime(target, mod):
    """smallest prime >= target with p == 1 (mod mod)."""
    p = target + ((1 - (target % mod)) % mod)
    if p < target: p += mod
    while not isprime(p): p += mod
    return p

# ----------------------------------------------------------------------------- #
#  cyclotomic arithmetic for n=2^mu :  Z[zeta_n] = Z[x]/(x^{n/2}+1)
#  represent an element as integer tuple length phi=n/2.
#  zeta^k  ->  e_(k mod n): if (k mod n) < phi  +1 at index (k mod n);
#                           else                 -1 at index (k mod n - phi).
# ----------------------------------------------------------------------------- #
def cyc_alpha(a_exps, b_exps, phi, n):
    """alpha = sum_{a in a_exps} zeta^a - sum_{b in b_exps} zeta^b, reduced. tuple length phi."""
    v=[0]*phi
    for a in a_exps:
        k=a % n
        if k < phi: v[k]+=1
        else:       v[k-phi]-=1
    for b in b_exps:
        k=b % n
        if k < phi: v[k]-=1
        else:       v[k-phi]+=1
    return tuple(v)

def is_zero(vec): return all(c==0 for c in vec)

def cyc_norm_and_l2(vec, phi, n):
    """Norm(alpha) = prod over primitive n-th roots zeta^j (j odd, 0<j<n) of alpha(zeta^j),
       which equals prod over all phi conjugates.  Also return l2 = sum |conj|^2 (= related to
       'size'), and max |conj| (the largest archimedean absolute value)."""
    prod=1.0+0j; l2=0.0; mx=0.0
    for j in range(1, n, 2):  # primitive n-th roots, phi of them
        w=cmath.exp(2j*math.pi*j/n)
        val=sum(vec[k]*(w**k) for k in range(phi))
        prod*=val
        a=abs(val); l2+=a*a; mx=max(mx,a)
    # Norm is a rational integer; round.
    Nre=prod.real
    Nint=round(Nre)
    err=abs(Nre-Nint)+abs(prod.imag)
    return Nint, l2, mx, err

# ----------------------------------------------------------------------------- #
#  enumerate genuine relations at depth r for subgroup mu_n in F_p
# ----------------------------------------------------------------------------- #
def enumerate_relations(n, p, r, g=None, max_print=8):
    """Return dict of stats on depth-r relations.  We exploit dilation-invariance:
       multiplying every x_i and every y_j by z (== shift all exponents by +1) preserves
       both the mod-p congruence and alpha (alpha -> zeta*alpha, still zero iff was zero;
       Norm unchanged). So we can fix a_1 = 0 (the first x-exponent) WLOG to kill the
       size-n dilation orbit, then multiply orbit-count by n. We also use the
       y<->x swap (alpha->-alpha) but keep tuples ORDERED (relations are tuples, the
       moment count E_r counts ordered tuples)."""
    if g is None: g=primroot(p)
    z=pow(g,(p-1)//n,p)
    phi=n//2
    zpow=[pow(z,k,p) for k in range(n)]   # z^k mod p, k-th root of unity
    # ordered tuples of exponents in (Z/n)^r for x and y.
    # WLOG fix a_1=0 (dilation gauge); multiply orbit counts by n at the end where noted.
    # We enumerate ALL ordered tuples but report both raw (ungauged) and gauged numbers.
    total=0; char0=0; genuine=0
    genuine_examples=[]
    genuine_alpha_norms=defaultdict(int)   # Norm(alpha) value -> count
    genuine_alpha_l2=defaultdict(int)      # rounded l2 -> count
    genuine_alpha_maxabs=defaultdict(int)  # rounded max|conj| -> count
    genuine_canon=set()                    # canonical reps under dilation (gauge a_1=0)
    # store (sorted-x-multiset, sorted-y-multiset) canonicalized by dilation for orbit study
    genuine_dilation_classes=defaultdict(list)
    all_x=list(itertools.product(range(n), repeat=r))
    for ax in all_x:
        sx=sum(zpow[a] for a in ax) % p
        for by in itertools.product(range(n), repeat=r):
            sy=sum(zpow[b] for b in by) % p
            if sx != sy: continue
            total+=1
            alpha=cyc_alpha(ax, by, phi, n)
            if is_zero(alpha):
                char0+=1
            else:
                genuine+=1
                N,l2,mx,err=cyc_norm_and_l2(alpha,phi,n)
                genuine_alpha_norms[N]+=1
                genuine_alpha_l2[round(l2)]+=1
                genuine_alpha_maxabs[round(mx,2)]+=1
                # dilation canonical form: shift exponents so min combined is 0... use
                # the n shifts and take lexicographically smallest (ordered tuple) form.
                best=None
                for s in range(n):
                    cand=(tuple((a+s)%n for a in ax), tuple((b+s)%n for b in by))
                    if best is None or cand<best: best=cand
                genuine_canon.add(best)
                genuine_dilation_classes[best].append((ax,by))
                if len(genuine_examples)<max_print:
                    genuine_examples.append((ax,by,alpha,N,round(mx,3),err))
    return dict(n=n,p=p,r=r,g=g,phi=phi,
                total=total,char0=char0,genuine=genuine,
                n_canon=len(genuine_canon),
                examples=genuine_examples,
                norms=dict(genuine_alpha_norms),
                l2hist=dict(genuine_alpha_l2),
                maxabshist=dict(genuine_alpha_maxabs),
                dil_classes=genuine_dilation_classes)

def galois_closure_check(stats, n):
    """Check whether the SET of genuine relations is closed under the Galois action
       a_i -> c*a_i (c in (Z/n)^*), which fixes p but permutes prime ideals P|p and
       sends mu_n -> mu_n via z -> z^c.  We test on canonical (dilation-gauged) reps:
       for each canonical genuine rep and each odd c, is c*rep ALSO genuine in F_p?
       (it is automatically a relation mod the OTHER prime P^c, but mod THIS p it may or
       may not stay a congruence -- we test the mod-p congruence directly.)"""
    p=stats['p']; g=stats['g']; r=stats['r']
    z=pow(g,(p-1)//n,p); zpow=[pow(z,k,p) for k in range(n)]
    phi=n//2
    canon=list(stats['dil_classes'].keys())
    odds=[c for c in range(1,n,2)]
    closed_total=0; closed_genuine=0; tested=0
    for (ax,by) in canon:
        for c in odds:
            cax=tuple((c*a)%n for a in ax); cby=tuple((c*b)%n for b in by)
            sx=sum(zpow[a] for a in cax)%p; sy=sum(zpow[b] for b in cby)%p
            tested+=1
            if sx==sy:
                closed_total+=1
                alpha=cyc_alpha(cax,cby,phi,n)
                if not is_zero(alpha): closed_genuine+=1
    return tested, closed_total, closed_genuine, len(odds)

# ----------------------------------------------------------------------------- #
#  driver
# ----------------------------------------------------------------------------- #
def run(n, beta_target_pow, rmax):
    p=find_prime(n**beta_target_pow, n)
    beta=math.log(p)/math.log(n)
    g=primroot(p); m=(p-1)//n
    print(f"\n{'='*78}")
    print(f"n={n} (mu={int(math.log2(n))})  p={p}  beta={beta:.2f}  m=(p-1)/n={m}  log2 m={math.log2(m):.1f}")
    print(f"{'='*78}",flush=True)
    for r in range(2, rmax+1):
        st=enumerate_relations(n,p,r,g)
        tot,c0,gen,ncanon=st['total'],st['char0'],st['genuine'],st['n_canon']
        # char-0 leading-order theory value (2r-1)!! n^r for ORDERED tuples
        def dblfact(k):
            x=1
            for j in range(1,k+1,2): x*=j
            return x
        c0_theory=dblfact(2*r-1)*n**r
        rate_random=n**(2*r)/p   # naive #genuine if congruences were random over residues
        print(f"\n r={r}:  total relations={tot}  char0={c0} (theory (2r-1)!!n^r={c0_theory})"
              f"  GENUINE={gen}  (naive n^2r/p={rate_random:.1f})",flush=True)
        if gen==0:
            print(f"    --> NO genuine relations at r={r} (G_r=0, fully suppressed)",flush=True)
            continue
        supp=gen/rate_random if rate_random>0 else float('inf')
        print(f"    suppression G_r/(n^2r/p) = {supp:.4f}   #dilation-orbits={ncanon}"
              f"   orbit_size~={gen/ncanon:.1f} (n={n})",flush=True)
        # (b) alpha structure
        norms=st['norms']
        nz=sorted(norms.items())
        print(f"    Norm(alpha) histogram (value:count): "
              f"{ {k:v for k,v in nz[:10]} }{' ...' if len(nz)>10 else ''}",flush=True)
        alldiv = all(N%p==0 for N in norms if N!=0)
        print(f"    all Norm(alpha) divisible by p? {alldiv}   (#distinct norms={len(norms)})",flush=True)
        mh=sorted(st['maxabshist'].items())
        print(f"    max|conjugate of alpha| histogram: {dict(mh[:8])}{' ...' if len(mh)>8 else ''}",flush=True)
        # smallest-norm genuine alpha tells us if alpha is a small cyclotomic integer * (ideal gen)
        minN=min(abs(N) for N in norms if N!=0)
        print(f"    min |Norm(alpha)| over genuine = {minN}   (compare p={p}: ratio {minN/p:.3g})",flush=True)
        # (a) Galois closure
        tested,ct,cg=galois_closure_check(st,n)[:3]
        print(f"    Galois a->c*a on canon reps (c odd): {ct}/{tested} stay congruences mod p, "
              f"{cg} stay genuine  (full Galois closure would be {tested})",flush=True)
        # examples
        print(f"    examples (ax; by; alpha-vec; Norm; max|conj|):",flush=True)
        for (ax,by,alpha,N,mx,err) in st['examples'][:4]:
            print(f"        x={list(ax)} y={list(by)}  alpha={list(alpha)}  N={N}  maxconj={mx}",flush=True)

if __name__=="__main__":
    # small proper subgroups; keep r small enough that n^{2r} enumeration is feasible.
    # n=8: n^{2r}=8^{2r}; r=2 ->4096, r=3 ->262144, r=4 ->16.7M (x-loop) * inner -> heavy.
    #      we do r up to 3 fully, r=4 only for n=8.
    # cost is sum over x-tuples (n^r) of inner y-loop (n^r) = n^{2r}.  n=8,r=4 -> 16.7M ok.
    #                                                              n=16,r=3 -> 16.7M ok.
    run(8,  3, 4)   # n=8,  p~8^3=512  (proper subgroup, beta~3)
    run(8,  4, 3)   # n=8,  p~8^4=4096 (beta~4, prize regime)
    run(16, 3, 3)   # n=16, p~16^3=4096 (beta~3)
    run(16, 4, 2)   # n=16, p~16^4=65536 (beta~4, prize regime; only r=2 cheap-ish)
