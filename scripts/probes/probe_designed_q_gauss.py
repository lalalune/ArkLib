#!/usr/bin/env python3
"""
DESIGNED-q Gauss-period scan (#389 prize core).

eta_b = sum_{y in mu_n} psi(b y),  psi(x)=exp(2 pi i x / p),  mu_n = n-th roots of unity in F_p^*.
B(n,p) = max_{b != 0} |eta_b|.

GOAL: for FIXED n=2^mu, scan many primes p with n | p-1, and correlate
  B(n,p)  vs  the arithmetic of (p mod n) / the order f = ord_n(p) of p mod n
  (= the residue degree / splitting of p in Q(zeta_n)).

Key known facts to TEST (not assume):
  * Number of distinct Gauss periods is at most the number of orbits of <p> (Frobenius)
    acting on cosets of mu_n in F_p^*.  Periods constant on Frobenius orbits.
  * SEMIPRIMITIVE case: -1 in <p> mod n  (p^t = -1 mod n for some t).  Then periods are
    "large" (~ sqrt(q) scale) -- the additively-structured BAD case.  For n=2^mu, p odd,
    -1 mod n is in <p> iff ord of p in (Z/n)^* is even and the unique elt of order 2 in
    <p> equals -1... we just compute it directly.
  * RAMANUJAN target: B <= 2 sqrt(n-1).  Ask: which p achieve B ~ sqrt(n)?

We compute eta_b EXACTLY in the integer ring Z[zeta_p] is overkill; instead compute the
GAUSS PERIODS via the cyclotomic-number / coset structure:
  eta over coset c*mu_n  = sum_{y in mu_n} zeta_p^{c y}.
There are k=(p-1)/n distinct cosets; eta_b depends only on which coset b lies in.
So we only need k complex sums of length n  ->  cheap even for p ~ 10^6.

To get EXACT |eta|^2 (avoid float lies) we also compute it as an INTEGER:
  |eta_c|^2 = sum_{y,z in mu_n} zeta_p^{c(y-z)}.
  = sum over the multiset {c(y-z) mod p}.  Group equal residues; the sum is
  sum_r N_r zeta_p^r where N_r = #{(y,z): c(y-z)=r}.  Then
  |eta_c|^2 = n + sum_{r != 0} N_r cos(2 pi r/p) ... still float.
BUT: sum_c |eta_c|^2 over the k cosets, times n (each coset has n elts) = Parseval check:
  sum_{b!=0}|eta_b|^2 = (p-1) average... = q n - n^2? We verify Parseval to validate floats.

We accept float B with rounding; we cross-check via Parseval and via the algebraic
multiplicity of period values.
"""
import cmath, math
from collections import Counter

# ---------- pure-python number theory (no sympy) ----------
def is_prime(n):
    if n < 2: return False
    for p in (2,3,5,7,11,13,17,19,23,29,31,37):
        if n % p == 0: return n == p
    d = n-1; r=0
    while d%2==0: d//=2; r+=1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x=pow(a,d,n)
        if x==1 or x==n-1: continue
        for _ in range(r-1):
            x=x*x%n
            if x==n-1: break
        else: return False
    return True

def factorize(n):
    f={}; d=2
    while d*d<=n:
        while n%d==0: f[d]=f.get(d,0)+1; n//=d
        d+=1 if d==2 else 2
    if n>1: f[n]=f.get(n,0)+1
    return f

def primitive_root(p):
    if p==2: return 1
    phi=p-1; facs=list(factorize(phi).keys())
    for g in range(2,p):
        if all(pow(g,phi//q,p)!=1 for q in facs): return g
    raise RuntimeError("no primitive root")

def ord_mod(a,n):
    # multiplicative order of a mod n (gcd(a,n)=1)
    a%=n
    if math.gcd(a,n)!=1: return None
    o=1; x=a%n
    while x!=1:
        x=x*a%n; o+=1
    return o

# ---------- Gauss periods ----------
def gauss_periods(n,p):
    """Return list of |eta_c|^2 over the k=(p-1)/n cosets, plus diagnostics."""
    assert (p-1)%n==0
    g=primitive_root(p)
    k=(p-1)//n
    h=pow(g,k,p)                      # generator of mu_n  (order n)
    mu=[pow(h,j,p) for j in range(n)] # the subgroup mu_n
    # coset reps: g^0, g^1, ..., g^{k-1}  (these hit all k cosets of mu_n in F_p^*)
    w=2*math.pi/p
    absq=[]
    etas=[]
    for c_exp in range(k):
        c=pow(g,c_exp,p)
        s=0j
        for y in mu:
            s+=cmath.exp(1j*w*((c*y)%p))
        etas.append(s)
        absq.append(abs(s)**2)
    return absq, etas, k, g

def analyze(n,p):
    absq,etas,k,g=gauss_periods(n,p)
    B=math.sqrt(max(absq))
    # Parseval over nonzero b: each coset has n elements, all with same |eta|.
    parseval=sum(x for x in absq)*n          # = sum_{b!=0} |eta_b|^2  ; should = q*n - n^2? test
    # multiplicative order of p mod n (residue degree / splitting of p in Q(zeta_n))
    f=ord_mod(p%n,n)
    # is -1 in <p> mod n ?  (semiprimitive criterion)
    semiprim=False; tneg=None
    x=p%n
    for t in range(1,(f or 1)+1):
        if x==(n-1)%n: semiprim=True; tneg=t; break
        x=x*(p%n)%n
    # number of distinct period values (orbits)
    distinct=len(set(round(a,3) for a in absq))
    return dict(n=n,p=p,k=k,B=B,maxabsq=max(absq),minabsq=min(absq),
                f=f,pmodn=p%n,semiprim=semiprim,tneg=tneg,distinct=distinct,
                parseval=parseval, sqrtn=math.sqrt(n), sqrtq=math.sqrt(p),
                ramanujan_ratio=B/math.sqrt(n))

if __name__=="__main__":
    import sys
    n=int(sys.argv[1]) if len(sys.argv)>1 else 8
    # scan primes p = 1 mod n up to a limit
    LIM=int(sys.argv[2]) if len(sys.argv)>2 else 5000
    print(f"### n={n} (=2^{int(math.log2(n))}),  scanning primes p = 1 mod {n}, p<{LIM}")
    print(f"{'p':>7} {'p%n':>4} {'f=ord':>6} {'k':>6} {'#vals':>6} {'B':>8} {'B/sqrtn':>8} {'semiprim':>9} {'parsev/qn':>10}")
    rows=[]
    p=n+1
    while p<LIM:
        if is_prime(p):
            r=analyze(n,p)
            rows.append(r)
            qn=r['p']*r['n']
            print(f"{r['p']:>7} {r['pmodn']:>4} {str(r['f']):>6} {r['k']:>6} {r['distinct']:>6} "
                  f"{r['B']:>8.3f} {r['ramanujan_ratio']:>8.3f} {str(r['semiprim']):>9} "
                  f"{r['parseval']/qn:>10.4f}")
        p+=n
    # summary correlations
    print("\n### CORRELATION SUMMARY (group by f = ord_n(p)):")
    byf={}
    for r in rows: byf.setdefault(r['f'],[]).append(r['ramanujan_ratio'])
    for f in sorted(byf):
        v=byf[f]
        print(f"  f={f:>3}: count={len(v):>3}  B/sqrtn  min={min(v):.3f} mean={sum(v)/len(v):.3f} max={max(v):.3f}")
    print("\n### group by (semiprimitive y/n):")
    for sp in (False,True):
        v=[r['ramanujan_ratio'] for r in rows if r['semiprim']==sp]
        if v: print(f"  semiprim={sp}: count={len(v):>3}  B/sqrtn min={min(v):.3f} mean={sum(v)/len(v):.3f} max={max(v):.3f}")
    # the WINNERS (smallest B/sqrtn) and LOSERS
    rows.sort(key=lambda r:r['ramanujan_ratio'])
    print("\n### 8 SMALLEST B/sqrtn (most Ramanujan):")
    for r in rows[:8]:
        print(f"  p={r['p']:>7} p%n={r['pmodn']:>3} f={r['f']} B/sqrtn={r['ramanujan_ratio']:.3f} semiprim={r['semiprim']} #vals={r['distinct']}")
    print("### 8 LARGEST B/sqrtn (least Ramanujan):")
    for r in rows[-8:]:
        print(f"  p={r['p']:>7} p%n={r['pmodn']:>3} f={r['f']} B/sqrtn={r['ramanujan_ratio']:.3f} semiprim={r['semiprim']} #vals={r['distinct']} B/sqrtq={r['B']/r['sqrtq']:.3f}")
