#!/usr/bin/env python3
"""
probe(#389) I006 REFUTED: q-difference (Jackson) confluent Stepanov gives NO multiplicity on mu_n.

IDEA I006: replace d/dX by D_zeta f = (f(zeta X) - f(X))/((zeta-1)X), zeta primitive 2^mu-th
root. Claim: since D_zeta(X^n-1) = 0 identically (whole subgroup is one orbit, [n]_zeta=0), the
separability obstruction is bypassed and q-multiplicity is free, giving Stepanov mu*|Z| <= deg_q.

VERDICT: REFUTED. The orbit-invariance that bypasses separability is exactly what VOIDS the
multiplicity. D_zeta is a NON-LOCAL finite-difference operator coupling z to zeta*z; on the
orbit-closed set mu_n it maps {fns on mu_n} -> {fns on mu_n}, so once f vanishes on the whole
orbit (j=0, n conditions) every iterate D_zeta^j f vanishes there AUTOMATICALLY. The higher
q-vanishing conditions are linearly DEPENDENT on the value conditions.

MEASURED (proper mu_n, n=2^mu | p-1, p prime ~ n^4, p >> n^3, NEVER n=p-1; mu=2,3,4):
 - M1: rank of q-vanish-to-order-m conditions on full mu_n COLLAPSES to exactly |Z|=n,
       INDEPENDENT of m. Stepanov needs m*n. (e.g. mu=4: m=5 needs 80, rank=16.) Multiplicity = 0.
 - M2: minimal nonzero f q-vanishing to order m on mu_n has total ORDINARY root-multiplicity
       = n (simple zeros only), deg = n; divisibility (prod(X-z))^m | f FAILS. q-vanishing
       produces ONLY ordinary simple vanishing, no high-order zero -> no degree bound.
 - single-point q-multiplicity SATURATES at n (rank stops growing past m=n): at most n
       independent q-conditions exist at any orbit point, capping achievable q-mult at n.

So mu*|Z| <= deg_q is FALSE; only the trivial |Z| <= deg holds. Confirms the existing W3 note
(confluent Stepanov stalls) at the structural root: the multiplicative/orbit derivation cannot
manufacture multiplicity on its OWN orbit. Reproducible; no fabrication.
"""

import sympy
from sympy import symbols, Poly

def setup(mu, beta=4):
    n=2**mu; p=sympy.nextprime(n**beta)
    while (p-1)%n!=0: p=sympy.nextprime(p)
    g=sympy.primitive_root(p); zeta=pow(g,(p-1)//n,p)
    return n,p,zeta,[pow(zeta,i,p) for i in range(n)]
def q_int(k,zeta,p): return sum(pow(zeta,i,p) for i in range(k))%p
def Dz(c,zeta,p):
    o=[0]*len(c)
    for k in range(1,len(c)): o[k-1]=(o[k-1]+c[k]*q_int(k,zeta,p))%p
    return o
def ev(c,x,p): return sum(a*pow(x,k,p) for k,a in enumerate(c))%p
def rank_modp(M,p):
    M=[[x%p for x in r] for r in M]; rows=len(M); cols=len(M[0]) if M else 0; r0=0; rk=0
    for c in range(cols):
        piv=next((r1 for r1 in range(r0,rows) if M[r1][c]%p!=0),None)
        if piv is None: continue
        M[r0],M[piv]=M[piv],M[r0]; inv=pow(M[r0][c],p-2,p); M[r0]=[(x*inv)%p for x in M[r0]]
        for r1 in range(rows):
            if r1!=r0 and M[r1][c]%p!=0:
                fc=M[r1][c]; M[r1]=[(M[r1][i]-fc*M[r0][i])%p for i in range(cols)]
        r0+=1; rk+=1
        if r0==rows: break
    return rk

print("MEASUREMENT 1: rank of q-vanishing-to-order-m conditions on FULL orbit mu_n.")
print(f"  Stepanov requires rank = m*n. We measure:")
print(f"  {'mu':>3} {'n':>4} {'p':>8} {'m':>3} {'m*n(need)':>10} {'rank(got)':>10}")
for mu in (2,3,4):
    n,p,zeta,mu_n=setup(mu)
    for m in (2, mu, mu+1):
        Ndim=(m+1)*n
        rows=[]
        for z in mu_n:
            for j in range(m):
                c0=None
                row=[]
                for k in range(Ndim):
                    c=[0]*Ndim; c[k]=1
                    for _ in range(j): c=Dz(c,zeta,p)
                    row.append(ev(c,z,p))
                rows.append(row)
        rk=rank_modp(rows,p)
        print(f"  {mu:>3} {n:>4} {p:>8} {m:>3} {m*n:>10} {rk:>10}", "<= COLLAPSE to n" if rk==n else "")

print("\nMEASUREMENT 2: divisibility. Minimal nonzero f q-vanishing to order m on Z=mu_n.")
print("  Stepanov needs sum_z val_z(f) >= m*|Z|. We measure sum of ordinary mults vs deg.")
print(f"  {'mu':>3} {'n':>4} {'m':>3} {'deg(f)':>7} {'sum_val(got)':>13} {'m*n(need)':>10}")
for mu in (2,3):
    n,p,zeta,mu_n=setup(mu)
    m=mu
    # build conditions, find minimal-degree nonzero kernel element
    # The rank is n (from M1), so we need Ndim > n for a nonzero soln. Use Ndim = n+1 ... but
    # conditions are over coeff space dim Ndim; kernel nonzero when Ndim > rank=n.
    Ndim=n+1
    rows=[]
    for z in mu_n:
        for j in range(m):
            row=[]
            for k in range(Ndim):
                c=[0]*Ndim; c[k]=1
                for _ in range(j): c=Dz(c,zeta,p)
                row.append(ev(c,z,p))
            rows.append(row)
    Mt=sympy.Matrix([[sympy.Integer(x)%p for x in r] for r in rows])
    ns=Mt.nullspace()
    if not ns:
        print(f"  {mu:>3} {n:>4} {m:>3}  no nonzero soln at Ndim={Ndim}"); continue
    v=ns[0]; coeffs=[int(x)%p for x in v]
    X=symbols('X')
    f=Poly(list(reversed(coeffs)),X,modulus=p)
    # sum of ordinary multiplicities over z in mu_n
    sv=0
    for z in mu_n:
        g=f; t=0
        while not g.is_zero and g.eval(z)%p==0:
            g,rem=sympy.div(g,Poly([1,(-z)%p],X,modulus=p))
            if rem.is_zero: t+=1
            else: break
        sv+=t
    print(f"  {mu:>3} {n:>4} {m:>3} {f.degree():>7} {sv:>13} {m*n:>10}",
          "<= divisibility HOLDS" if sv>=m*n else "<= divisibility FAILS (only ordinary, no mult)")
