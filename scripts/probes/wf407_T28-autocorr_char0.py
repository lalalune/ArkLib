"""
wf407 / T28-autocorr : char-0 clean energy E_r^(0) and the cross-term in char 0.

The DM_r condition the prize needs is the CHAR-0 clean bound  E_r^(0) <= (2r-1)!! n^{r-1}
transferred to char p.  E_r^(0) = #{(x,y) in (mu_n)^{2r} : sum x_i = sum y_i  in C}  (exact
complex roots of unity, NO prime).  Does the autocorrelation recursion ALSO hold in char 0,
and does the char-0 cross term decay (unlike char-p)?

In char 0 the convolution lives on the lattice L = Z[zeta_n] (rank phi(n)).  We compute
E_r^(0) exactly by representing f_r as a Counter over Z[zeta_n]-coordinates (additive group of
the cyclotomic integers), keyed by the integer coefficient vector in the power basis.

We then form cross_r^(0) = sum_{u != v in mu_n} C_r^(0)(v-u) and check the recursion
E_{r+1}^(0) = n*E_r^(0) + cross_r^(0), and measure cross^(0)/E^(0).
"""
from collections import Counter
from itertools import product
from math import comb

def cyclotomic_basis_reduce(n):
    # represent zeta_n^k for k in 0..n-1 in the power basis of Z[zeta_n] (degree phi(n)).
    # Use the minimal polynomial Phi_n to reduce. We'll just work in Z[x]/(x^n - 1) is WRONG
    # (that's not a domain). Use Z[x]/Phi_n(x). Build reduction table for x^k mod Phi_n.
    import sympy
    x=sympy.symbols('x')
    Phi=sympy.cyclotomic_poly(n,x)
    deg=sympy.degree(Phi,x)
    Phi_poly=sympy.Poly(Phi,x)
    table=[]  # table[k] = coeff vector (length deg) of x^k mod Phi_n, as tuple of ints
    for k in range(n):
        rem=sympy.rem(sympy.Poly(x**k,x),Phi_poly,x)
        coeffs=[int(rem.coeff_monomial(x**j)) for j in range(deg)]
        table.append(tuple(coeffs))
    return table, deg

def char0_energy_chain(n, rmax):
    table,deg=cyclotomic_basis_reduce(n)
    # f_1: each mu_n element zeta^k maps to coeff vector table[k] with multiplicity 1
    # f_r as Counter: key=coeff vector tuple, value = count of r-tuples summing to it
    f={}
    for k in range(n):
        f[table[k]]=f.get(table[k],0)+1
    Es=[]
    # roots as vectors
    roots=[table[k] for k in range(n)]
    def add(a,b): return tuple(ai+bi for ai,bi in zip(a,b))
    def sub(a,b): return tuple(ai-bi for ai,bi in zip(a,b))
    fr=f
    for r in range(1,rmax+1):
        Er=sum(c*c for c in fr.values())
        Es.append(Er)
        # cross_r = sum_{u!=v in mu_n} C_r(v-u), C_r(z)=sum_w f_r(w) f_r(w-z)
        # = sum_{u!=v} sum_w f_r(w) f_r(w-(v-u))
        # do it via: for each ordered pair (u,v), shift = v-u, autocorr at shift.
        # autocorr at shift d = sum over keys w of fr[w]*fr.get(w-d,0)
        cross=0
        # group shifts by multiplicity
        mult=Counter()
        for u in roots:
            for v in roots:
                if u!=v:
                    mult[sub(v,u)]+=1
        acache={}
        for d,cnt in mult.items():
            if d not in acache:
                s=0
                for w,fw in fr.items():
                    s+=fw*fr.get(sub(w,d),0)
                acache[d]=s
            cross+=cnt*acache[d]
        # next convolution
        fr1={}
        for w,fw in fr.items():
            for rt in roots:
                k=add(w,rt)
                fr1[k]=fr1.get(k,0)+fw
        Er1=sum(c*c for c in fr1.values())
        recur_ok=(Er1==n*Er+cross)
        crossE=cross/Er
        dfact=1
        for kk in range(1,2*r,2): dfact*=kk
        clean=dfact*(n**(r-1))   # the DM target form E_r <= (2r-1)!! n^{r-1}
        cleanR=dfact*(n**r)
        yield (r,Er,cross,crossE,Er1,Er1/Er,recur_ok, clean, Er<=clean, cleanR, Er<=cleanR)
        fr=fr1

if __name__=="__main__":
    for n,rmax in [(8,6),(16,5),(32,4)]:
        print(f"\n===== CHAR-0  mu_{n}  (phi={None}) =====")
        print(f"{'r':>2} {'E_r^(0)':>14} {'cross^(0)':>16} {'cross/E':>10} {'E_{r+1}/E_r':>12} {'recur':>6} "
              f"{'(2r-1)!!n^{r-1}':>15} {'<=DMnum?':>8} {'(2r-1)!!n^r':>14} {'<=clean?':>8}")
        for row in char0_energy_chain(n,rmax):
            (r,Er,cross,crossE,Er1,ratio,ok,clean,le,cleanR,leR)=row
            print(f"{r:>2} {Er:>14} {cross:>16} {crossE:>10.3f} {ratio:>12.4f} {str(ok):>6} "
                  f"{clean:>15} {str(le):>8} {cleanR:>14} {str(leR):>8}")
