"""
wf407 / T28-autocorr : the Fourier explanation of cross/E -> n(n-1).

Identity (Parseval):  E_r = (1/p) sum_{b in F_p} |eta_b|^{2r},   eta_b = sum_{x in mu_n} e_p(bx),
with eta_0 = n.  Hence  E_{r+1}/E_r = [ sum_b |eta_b|^{2(r+1)} ] / [ sum_b |eta_b|^{2r} ]  ->  n^2
as r->infty (the b=0 term n^{2r} dominates since |eta_b|<n for b!=0... in fact <= B < n unless
some |eta_b|=n which needs b*mu_n in a coset, impossible for b!=0).  And
   cross_r/E_r = E_{r+1}/E_r - n  ->  n^2 - n = n(n-1)  = the TRIVIAL bound, exactly.

So the trivial cross bound is ASYMPTOTICALLY TIGHT (saturated by the principal frequency),
and there is NO sub-trivial decay of cross_r in the deep tail.  We verify:
  (1) E_r = (1/p) sum_b |eta_b|^{2r} exactly (to machine precision).
  (2) E_{r+1}/E_r -> n^2, monotonically increasing.
  (3) The 'gap to trivial'  n(n-1) - cross_r/E_r  = n * (S_{r}/S_{r+1-principal})... measure it:
      it equals  n * [ sum_{b!=0}|eta_b|^{2r}(n^2-|eta_b|^2) ] / [ n^{2r} + sum_{b!=0}|eta_b|^{2r} ]...
      i.e. governed ENTIRELY by the SECOND-largest |eta_b| = B (the prize quantity).
"""
import cmath, math

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

def eta_abs2(p,S):
    w=2*math.pi/p
    out=[0.0]*p
    for b in range(p):
        z=sum(cmath.exp(1j*w*((b*x)%p)) for x in S)
        out[b]=abs(z)**2
    return out

def exact_energy(p,H,r):
    # direct convolution count for cross-check
    f=[0]*p
    for x in H: f[x]=1
    fr=f
    for _ in range(r-1):
        g=[0]*p
        for z in range(p):
            s=0
            for u in H: s+=fr[(z-u)%p]
            g[z]=s
        fr=g
    return sum(v*v for v in fr)

if __name__=="__main__":
    for p,n,rmax in [(97,8,7),(193,16,6),(257,32,5)]:
        if (p-1)%n: continue
        H=subgroup(p,n)
        a2=eta_abs2(p,H)
        B=max(a2[b] for b in range(1,p))**0.5
        print(f"\n===== p={p} n={n}  B=max_{{b!=0}}|eta_b|={B:.4f}  (sqrt(n)={n**0.5:.3f}, n={n}) =====")
        print(f"{'r':>2} {'E_r(direct)':>14} {'E_r(Parseval)':>16} {'match':>6} {'E_{r+1}/E_r':>12} "
              f"{'n^2':>6} {'n(n-1)-cross/E':>15}")
        Eprev=None
        for r in range(1,rmax+1):
            Edir=exact_energy(p,H,r)
            Epar=sum(a2[b]**r for b in range(p))/p
            match = abs(Edir-Epar)<1e-3*max(1,Edir)
            Enext=sum(a2[b]**(r+1) for b in range(p))/p
            ratio=Enext/Epar
            crossE=ratio-n
            gap=n*(n-1)-crossE
            print(f"{r:>2} {Edir:>14} {Epar:>16.1f} {str(match):>6} {ratio:>12.4f} {n*n:>6} {gap:>15.5f}")
