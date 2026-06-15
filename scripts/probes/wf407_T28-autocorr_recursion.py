"""
wf407 / T28-autocorr : EXACT char-p autocorrelation recursion E_{r+1}=n*E_r+cross_r.

Setting (exactly the Lean Sweep_A02 setting):
  G = Z/p,  H = mu_n  = order-n multiplicative subgroup of F_p^*.
  f_r = 1_H^{*r}  (r-fold additive convolution of the indicator), so
  f_r(z) = #{(x_1..x_r) in H^r : sum x_i = z (mod p)}.
  E_r = sum_z f_r(z)^2   (= 2r-fold additive energy).
  C_r(z) = sum_w f_r(w) f_r(w-z)   (autocorrelation; C_r(0)=E_r).
  cross_r = sum_{u != v in H} C_r(v-u).
  RECURSION:  E_{r+1} = n*E_r + cross_r.    [verify exactly]

Trivial bound: C_r(z) <= C_r(0)=E_r  =>  cross_r <= n(n-1) E_r  =>  E_{r+1} <= n^2 E_r.
We measure the ACTUAL ratio  rho_r := cross_r / E_r   and  E_{r+1}/E_r.
The question (parts 2/3): is rho_r << n(n-1) (sub-trivial), and does that push the
"DM_r free" threshold (where crude E_r <= n^{2r-1} already implies E_r <= (2r-1)!! n^{r-1})
DOWN from r ~ 1.36 n toward r ~ beta log n?
"""
import sys
from math import comb

def primitive_root(p):
    # small p only
    fac = []
    m = p-1
    d = 2
    pf = set()
    while d*d <= m:
        while m % d == 0:
            pf.add(d); m//=d
        d+=1
    if m>1: pf.add(m)
    for g in range(2,p):
        if all(pow(g,(p-1)//q,p)!=1 for q in pf):
            return g
    raise RuntimeError

def subgroup(p,n):
    assert (p-1)%n==0
    g=primitive_root(p); h=pow(g,(p-1)//n,p)
    S=set(); x=1
    for _ in range(n):
        S.add(x); x=(x*h)%p
    assert len(S)==n
    return sorted(S)

def conv_indicator(p, H):
    # f_1 = indicator of H as length-p vector of ints
    f=[0]*p
    for x in H: f[x]=1
    return f

def conv(p, f, H):
    # (f *conv 1_H)(z) = sum_{u in H} f(z-u)
    g=[0]*p
    for z in range(p):
        s=0
        for u in H:
            s+=f[(z-u)%p]
        g[z]=s
    return g

def energy(p,f):
    return sum(v*v for v in f)

def autocorr_at(p,f,z):
    return sum(f[w]*f[(w-z)%p] for w in range(p))

def cross_term(p,f,H):
    # sum over ordered pairs u!=v in H of C(v-u)
    # group by shift d=v-u; multiplicity = #{(u,v) in H^2 : v-u=d}
    from collections import Counter
    mult=Counter()
    for u in H:
        for v in H:
            if u!=v:
                mult[(v-u)%p]+=1
    s=0
    # cache autocorr per shift
    cache={}
    for d,c in mult.items():
        if d not in cache: cache[d]=autocorr_at(p,f,d)
        s+=c*cache[d]
    return s

def run(p,n,rmax):
    H=subgroup(p,n)
    f=conv_indicator(p,H)   # f_1
    Es=[]; rows=[]
    E1=energy(p,f); Es.append(E1)  # E_1 = sum 1_H^2 = n
    fr=f
    for r in range(1,rmax+1):
        Er=energy(p,fr)
        cr=cross_term(p,fr,H)
        fr1=conv(p,fr,H)
        Er1=energy(p,fr1)
        recur_ok = (Er1 == n*Er + cr)
        rho = cr/Er if Er else 0.0
        # clean char-0 reference value (2r-1)!! * n^r  (the DM target numerator form)
        dfact = 1
        for k in range(1,2*r):
            if k%2==1: dfact*=k
        clean = dfact * (n**r)
        # crude bound n^{2r-1}
        crude = n**(2*r-1)
        rows.append((r,Er,cr,rho,Er1,Er1/Er,recur_ok, clean, crude, Er<=clean))
        fr=fr1
    return rows

if __name__=="__main__":
    # pick primes with the needed subgroup and small enough p for exact full convolution
    cases=[(17,8,6),(41,8,6),(97,8,7),(193,8,8),
           (97,16,6),(193,16,7),(257,16,7),
           (97,32,5),(193,32,6),(257,32,6),
           (193,64,5),(257,64,5)]
    for p,n,rmax in cases:
        if (p-1)%n: continue
        print(f"\n===== p={p}  n={n}  (m=(p-1)/n={ (p-1)//n }) =====")
        print(f"{'r':>2} {'E_r':>12} {'cross_r':>14} {'cross/E':>10} {'E_{r+1}/E_r':>12} {'recur':>6} {'clean(2r-1)!!n^r':>16} {'Er<=clean':>9}")
        for (r,Er,cr,rho,Er1,ratio,ok,clean,crude,le) in run(p,n,rmax):
            print(f"{r:>2} {Er:>12} {cr:>14} {rho:>10.3f} {ratio:>12.4f} {str(ok):>6} {clean:>16} {str(le):>9}")
