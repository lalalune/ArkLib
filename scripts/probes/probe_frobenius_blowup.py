# Probe: the Frobenius word w(z)=z^p over F_{p^e} (full domain) realizes the
# sub-Johnson agreement blowup: every secant of the graph is p-rich;
# mass = n(n-1)/(p-1); explainable-p-subset supply = n(n-1)/(p(p-1)).
import itertools

def gf(p, e, modpoly):
    # elements as tuples of coeffs len e; modpoly = monic deg e, coeffs list len e (lower coeffs)
    els = list(itertools.product(range(p), repeat=e))
    def add(a,b): return tuple((x+y)%p for x,y in zip(a,b))
    def smul(c,a): return tuple((c*x)%p for x in a)
    def mul(a,b):
        # polynomial mult then reduce
        res=[0]*(2*e-1)
        for i,x in enumerate(a):
            for j,y in enumerate(b): res[i+j]=(res[i+j]+x*y)%p
        for d in range(2*e-2, e-1, -1):
            c=res[d]
            if c:
                res[d]=0
                for i in range(e):
                    res[d-e+i]=(res[d-e+i]-c*modpoly[i])%p
        return tuple(res[:e])
    return els, add, smul, mul

def run(p, e, modpoly):
    els, add, smul, mul = gf(p,e,modpoly)
    n = len(els)
    def pw(a,k):
        r=tuple([1]+[0]*(e-1))
        for _ in range(k): r=mul(r,a)
        return r
    w = {z: pw(z,p) for z in els}
    # agreement family: lines y=az+b with agreement >= p
    fam=[]
    for a in els:
        for b in els:
            agr=[z for z in els if w[z]==add(mul(a,z),b)]
            if len(agr)>=p: fam.append((a,b,tuple(sorted(agr))))
    L=len(fam); mass=sum(len(f[2]) for f in fam)
    sizes=sorted(set(len(f[2]) for f in fam))
    # pairwise intersections
    maxint=0
    for i in range(L):
        for j in range(i+1,L):
            s=len(set(fam[i][2])&set(fam[j][2])); maxint=max(maxint,s)
    # secant check: every pair on some rich line
    pairs_covered=all(any(z1 in f[2] and z2 in f[2] for f in fam)
                      for z1,z2 in itertools.combinations(els,2))
    supply=len(set(f[2] for f in fam))  # distinct agreement sets = explainable p-sets (sizes all p)
    print(f"p={p} e={e} n={n}: L={L} sizes={sizes} mass={mass} "
          f"pred_mass={n*(n-1)//(p-1)} supply={supply} pred_supply={n*(n-1)//(p*(p-1))} "
          f"maxpairint={maxint} all_secants_rich={pairs_covered} 2n={2*n} t2={p*p}")

run(3,2,[1,0])   # F_9 = F_3[x]/(x^2+1)? x^2 = -1 -> modpoly coeffs [1,0] means x^2 = -(1) - 0x = -1 ok irreducible mod 3
run(3,3,[1,2,0]) # F_27: x^3 = -(1+2x) = -1-2x = 2+x mod 3; check irreducibility: x^3+2x+1 mod 3: roots? 0:1,1:1+2+1=4=1,2:8+4+1=13=1 -> no roots, irreducible
run(5,2,[2,0])   # F_25: x^2 = -2 = 3; 3 a QR mod 5? squares mod5={0,1,4}; 3 not -> x^2-3 irred; modpoly x^2+2: x^2=-2=3 ✓
