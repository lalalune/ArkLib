"""
wf407 / T28-autocorr : the BAND analysis.

Question (parts 2/3 of the thread):
  The trivial cross bound cross_r <= n(n-1) E_r gives E_{r+1} <= n^2 E_r, hence E_r <= n^{2r-1},
  which implies the DM target  E_r <= (2r-1)!! n^r  exactly when  n^r <= (2r-1)!!  i.e. r >~ 1.36 n.
  Can a SUB-TRIVIAL bound  cross_r <= c_r * E_r  with c_r < n(n-1) push that threshold down?

  If we had a uniform  E_{r+1} <= K * E_r  for some K = K(n) over the band, then E_r <= n * K^{r-1},
  and DM holds when  n * K^{r-1} <= (2r-1)!! n^r,  i.e.  K^{r-1} <= (2r-1)!! n^{r-1}.

  We MEASURE the actual ratio R_r := E_{r+1}/E_r and the actual cross/E, to see what the best
  achievable K is, and at what r the ACTUAL E_r first drops below the clean target (the true DM onset).
"""
import sys
from math import comb, log

def primitive_root(p):
    m=p-1; pf=set(); d=2
    while d*d<=m:
        while m%d==0: pf.add(d); m//=d
        d+=1
    if m>1: pf.add(m)
    for g in range(2,p):
        if all(pow(g,(p-1)//q,p)!=1 for q in pf): return g
    raise RuntimeError
def subgroup(p,n):
    g=primitive_root(p); h=pow(g,(p-1)//n,p); S=set(); x=1
    for _ in range(n): S.add(x); x=(x*h)%p
    return sorted(S)
def conv_ind(p,H):
    f=[0]*p
    for x in H: f[x]=1
    return f
def conv(p,f,H):
    g=[0]*p
    for z in range(p):
        s=0
        for u in H: s+=f[(z-u)%p]
        g[z]=s
    return g
def energy(p,f): return sum(v*v for v in f)
def dfact(r):  # (2r-1)!!
    x=1
    for k in range(1,2*r,2): x*=k
    return x

def analyze(p,n,rmax):
    H=subgroup(p,n); f=conv_ind(p,H)
    Es=[energy(p,f)]  # E_1
    fr=f
    for r in range(2,rmax+1):
        fr=conv(p,fr,H); Es.append(energy(p,fr))
    return Es

if __name__=="__main__":
    # Use the largest m (deepest, most char-0-like) cases enumerable.
    cases=[(193,8,9),(97,16,7),(257,16,8),(257,32,6),(257,64,5)]
    print("Question: at what r does ACTUAL E_r first satisfy E_r <= (2r-1)!! n^r  (true DM onset)?")
    print("And compare to the TRIVIAL-bound threshold r* >~ 1.36 n.\n")
    for p,n,rmax in cases:
        if (p-1)%n: continue
        Es=analyze(p,n,rmax)
        m=(p-1)//n
        triv = (1.359*n)
        print(f"--- p={p} n={n} (m={m})  trivial-bound DM threshold r*~1.36n = {triv:.1f} ---")
        print(f"{'r':>2} {'E_r':>16} {'(2r-1)!!n^r':>16} {'E_r/clean':>10} {'E_{r+1}/E_r':>12} {'n^2':>8} {'cross/E':>10}")
        for i,Er in enumerate(Es):
            r=i+1
            clean=dfact(r)*(n**r)
            ratio = (Es[i+1]/Er) if i+1<len(Es) else float('nan')
            crossE = ratio - n  # since E_{r+1}=n E_r + cross_r => cross/E = ratio - n
            print(f"{r:>2} {Er:>16} {clean:>16} {Er/clean:>10.3f} {ratio:>12.4f} {n*n:>8} {crossE:>10.3f}")
        print()
    print("Interpretation: 'true DM onset' = first r with E_r/clean <= 1.")
