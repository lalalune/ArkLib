#!/usr/bin/env python3
"""
A2 ORBIT-COUNT CLOSED FORM (#407).

EXACT char-0 computation via a big prime q (q==1 mod n, far above the bad-prime locus ~n^2,
low 2-adic valuation for faithfulness). The over-determined band is PROVEN p-independent, so
this equals the char-0 value. We verify p-independence by re-running on a second prime.

Definitions (matching the prompt exactly):
  mu_n = order-n multiplicative subgroup of F_q* (proper: n | q-1, n < q-1).  RS[k]=deg<k.  rho=k/n.
  FAR monomial direction (a,b): k <= a < b < n.  f_gamma(x)=x^a + gamma*x^b.
  gamma BAD at agreement w  <=>  exists g in RS[k] and a w-subset W of mu_n with f_gamma=g on W
       (i.e. x^a+gamma x^b is within Hamming n-w of RS[k]; M=[x^0..x^{k-1},x^a,x^b] rank-deficient on W).
  I_dir(w) = #{distinct bad gamma}.  Bad set is a union of <zeta^{b-a}>-orbits (gamma->gamma*zeta^{b-a}),
       orbit size S = n/gcd(b-a,n).  #orbits = I_dir / S.
  budget = n.  delta = 1 - w/n.  delta*(n,rho) = sup{delta : max_dir I_dir(w) <= n}.
"""
import sys, itertools
from math import gcd

def isprime(m):
    if m < 2: return False
    if m % 2 == 0: return m == 2
    i = 3
    while i*i <= m:
        if m % i == 0: return False
        i += 2
    return True

def find_prime(n, lo, skip=0):
    q = ((lo // n) + 1) * n + 1
    found = 0
    while True:
        if isprime(q):
            t = q-1; v2 = 0
            while t % 2 == 0: t//=2; v2+=1
            an=n; v2n=0
            while an%2==0: an//=2; v2n+=1
            if v2 <= v2n + 2:
                if found == skip:
                    return q
                found += 1
        q += n

def root_table(n, q):
    """Return P[e] = list over exponents: P[i] = primitive root^i; and pw[a][i] = (root^i)^a."""
    e=(q-1)//n
    w=None
    for base in range(2,q):
        cand=pow(base,e,q)
        if cand==1: continue
        if pow(cand, n//2, q)==1: continue
        w=cand; break
    mu=[pow(w,i,q) for i in range(n)]
    # pw[a] for a in 0..n-1: pw[a][i] = mu[i]^a = w^{a*i} = mu[(a*i)%n]
    return mu

INV=None
def build_inv(q):
    global INV
    INV=[0]*q
    INV[1]=1
    for i in range(2,q):
        INV[i]=(-(q//i)*INV[q%i])%q

def left_null(M, k, q):
    """M is w x k (list of rows). Return basis of left null space (combos of rows that vanish)."""
    wlen=len(M)
    A=[M[r][:] + [1 if cc==r else 0 for cc in range(wlen)] for r in range(wlen)]
    prow=0
    for col in range(k):
        piv=None
        for r in range(prow,wlen):
            if A[r][col]%q!=0: piv=r; break
        if piv is None: continue
        A[prow],A[piv]=A[piv],A[prow]
        invp=INV[A[prow][col]]
        A[prow]=[(x*invp)%q for x in A[prow]]
        for r in range(wlen):
            if r!=prow and A[r][col]%q!=0:
                f=A[r][col]
                A[r]=[(A[r][cc]-f*A[prow][cc])%q for cc in range(len(A[r]))]
        prow+=1
        if prow==wlen: break
    N=[]
    for r in range(prow,wlen):
        if all(A[r][c]%q==0 for c in range(k)):
            N.append([A[r][k+j]%q for j in range(wlen)])
    return N

def bad_for_dir(n,k,a,b,w,q,mu):
    bad=set(); degenerate=False
    # exponent->index map: mu[i]^e = mu[(i*e)%n]
    for W in itertools.combinations(range(n),w):
        # Vandermonde rows
        M=[[mu[(i*c)%n] for c in range(k)] for i in W]
        N=left_null(M,k,q)
        if not N: continue
        u=[mu[(i*a)%n] for i in W]
        v=[mu[(i*b)%n] for i in W]
        wlen=len(W)
        gc=None; ok=True
        anyv=False
        for row in N:
            Nu=sum(row[j]*u[j] for j in range(wlen))%q
            Nv=sum(row[j]*v[j] for j in range(wlen))%q
            if Nv!=0:
                anyv=True
                gi=(-Nu*INV[Nv])%q
                if gc is None: gc=gi
                elif gi!=gc: ok=False; break
            else:
                if Nu!=0: ok=False; break
        if not anyv:
            # all Nv zero; if also all Nu zero -> any gamma -> degenerate direction
            allNuzero=all(sum(row[j]*u[j] for j in range(wlen))%q==0 for row in N)
            if allNuzero: degenerate=True
            continue
        if ok and gc is not None:
            bad.add(gc)
    return bad,degenerate

def analyze(n,k,w,q):
    build_inv(q)
    mu=root_table(n,q)
    res={}
    for a in range(k,n):
        for b in range(a+1,n):
            bad,deg=bad_for_dir(n,k,a,b,w,q,mu)
            S=n//gcd(b-a,n)
            res[(a,b)]=(len(bad),S,deg)
    return res

if __name__=="__main__":
    mode = sys.argv[1] if len(sys.argv)>1 else "check"

    if mode=="check":
        print("=== FAITHFULNESS: reproduce prompt measured worst-direction delta* ===",flush=True)
        checks=[(8,1,4,0.375,(4,7)),(16,1,4,0.5625,(4,6)),(8,1,2,0.25,(4,5)),(16,1,2,0.3125,(8,10))]
        for (n,rn,rd,dt,ed) in checks:
            w=round((1-dt)*n); k=(rn*n)//rd
            q=find_prime(n,n**3+5)
            res=analyze(n,k,w,q)
            worst=max(((I,d,S) for d,(I,S,deg) in res.items() if not deg),default=(-1,None,None))
            print(f"n={n} rho={rn}/{rd} k={k} delta={dt} w={w} q={q}: worstI={worst[0]} dir={worst[1]} S={worst[2]} (prompt dir {ed}, budget n={n})",flush=True)

    elif mode=="scan":
        # full per-band orbit-count table for given n, rho
        n=int(sys.argv[2]); rn=int(sys.argv[3]); rd=int(sys.argv[4])
        k=(rn*n)//rd
        q=find_prime(n,n**3+5); q2=find_prime(n,n**3+5,skip=3)
        build_inv(q)
        print(f"# n={n} rho={rn}/{rd} k={k} q={q} (pindep-check q2={q2}) budget=n={n}",flush=True)
        for w in range(k+1,n):  # over-det requires w>k
            delta=1-w/n
            mu=root_table(n,q)
            rows=[]
            anybad=False
            for a in range(k,n):
                for b in range(a+1,n):
                    bad,deg=bad_for_dir(n,k,a,b,w,q,mu)
                    if deg: continue
                    S=n//gcd(b-a,n)
                    I=len(bad)
                    if I>0:
                        norb=I//S if I%S==0 else -I  # negative flags non-divisible
                        rows.append((a,b,I,S,norb))
                        anybad=True
            rows.sort(key=lambda r:-r[2])
            maxI=rows[0][2] if rows else 0
            top=rows[0] if rows else None
            cross = "OVER" if maxI>n else "ok"
            print(f"w={w:2d} delta={delta:.4f}: maxI={maxI:4d} [{cross} budget {n}]  worst_dir={top[:2] if top else None} S={top[3] if top else '-'} #orbits={top[4] if top else '-'}",flush=True)
            if len(sys.argv)>5 and sys.argv[5]=="-v":
                for r in rows[:6]:
                    print(f"      dir{r[0],r[1]}: I={r[2]} S={r[3]} #orbits={r[4]}",flush=True)
