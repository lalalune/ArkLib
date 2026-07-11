#!/usr/bin/env python3
"""
door-(iv) Lane-1 PROBE — cross-half phase relation of the index-2 coset split.

Structural identity (exact): with mu_n = mu_{n/2} ⊔ g·mu_{n/2} (g a generator of mu_n),
    eta_b = Σ_{y∈mu_n} e_p(b·y) = A_b + B_b,
    A_b = Σ_{z∈mu_{n/2}} e_p(b·z)              (= sub-period at frequency b)
    B_b = Σ_{z∈mu_{n/2}} e_p(b·g·z) = A_{b·g}  (= SAME sub-period at the DILATED frequency b·g).

So the half-mass H(n)=max_b(|A_b|+|B_b|) = max_b(|A_b|+|A_{bg}|): a sum of the sub-period magnitude
at TWO multiplicatively-shifted frequencies b and bg. The half-mass equivalence ([door-iv-halfmass-
equivalence]) makes this the EQUIVALENT prize target.

QUESTION (the un-probed structural lever): at the worst frequency b*, is B_{b*} a clean PHASE ROTATION
of A_{b*}, i.e. B = ω·A for a root of unity ω (so |A|=|B| automatically and η = (1+ω)A)?  If YES with a
FIXED ω, then |η_{b*}| = |1+ω|·|A_{b*}| and the worst-b half-mass is just 2·(worst sub-period magnitude
under the constraint b,bg both near-extremal) — a structural reduction. If NO (ω varies / is not a clean
root of unity), the cross-half phase is itself an unstructured object and this lever is b-blind/dead.

Probe-first, EXACT C, PROPER 2-power mu_n, p>>n^3, m=(p-1)/n>1, NEVER n=q-1. Full F_p* scan at n=16,
sampled larger. Multiple structured + generic primes.
"""
import cmath, math, random

def factor_small(x):
    f=[]; d=2
    while d*d<=x:
        while x%d==0: f.append(d); x//=d
        d+=1
    if x>1: f.append(x)
    return f

def primitive_root(p):
    fs=set(factor_small(p-1))
    for g in range(2,p):
        if all(pow(g,(p-1)//q,p)!=1 for q in fs): return g
    return None

def subgroup(p, n):
    # mu_n = unique subgroup of order n in F_p^* ; need n | p-1
    assert (p-1)%n==0
    g=primitive_root(p)
    h=pow(g,(p-1)//n,p)   # generator of mu_n, order n
    els=[]; cur=1
    for _ in range(n): els.append(cur); cur=cur*h%p
    return h, els

def ep(p):
    # on-demand factory (do NOT materialize p entries; p can be ~1e8)
    w=2*math.pi/p
    return lambda t: cmath.exp(1j*w*(t%p))

def halfsums(p, n, b, EP, gen_n):
    # mu_{n/2} = <gen_n^2>; coset rep = gen_n. A_b over mu_{n/2}, B_b over gen_n*mu_{n/2}
    half=n//2
    z=pow(gen_n,2,p)
    sub=[]; cur=1
    for _ in range(half): sub.append(cur); cur=cur*z%p
    A=0j; B=0j
    for s in sub:
        A+=EP((b*s)%p)
        B+=EP((b*gen_n*s)%p)
    return A,B

def run(p, n, full=False, samples=4000):
    EP=ep(p)
    gen_n,_=subgroup(p,n)
    m=(p-1)//n
    # iterate b over coset reps of mu_n in F_p^* : b = g^j, j=0..m-1, g primitive root
    g=primitive_root(p)
    reps=[]
    if full or m<=samples:
        cur=1
        for j in range(m): reps.append(cur); cur=cur*g%p
    else:
        seen=set()
        while len(reps)<samples:
            j=random.randrange(m); 
            if j in seen: continue
            seen.add(j); reps.append(pow(g,j,p))
    # find worst b (max |eta|)
    best=None
    rows=[]
    for b in reps:
        A,B=halfsums(p,n,b,EP,gen_n)
        eta=A+B
        rows.append((abs(eta),b,A,B))
    rows.sort(reverse=True)
    # examine top frequencies: is B a clean phase rotation of A?  omega = B/A
    out=[]
    for mag,b,A,B in rows[:5]:
        if abs(A)<1e-9:
            out.append((mag,b,None,None,None)); continue
        omega=B/A
        # is omega a root of unity?  |omega| should be 1 if |A|=|B|
        absom=abs(omega)
        ang=cmath.phase(omega)
        # nearest n-th root of unity angle?  k*2pi/n
        k=ang*n/(2*math.pi)
        nearest_k=round(k)
        defect=abs(k-nearest_k)   # 0 => omega is an n-th root of unity
        out.append((mag/math.sqrt(n),absom,ang,nearest_k%n,defect))
    return m, out

# p >> n^3 ; keep m=(p-1)/n modest so the FULL F_p* coset-rep scan is feasible.
# n=16: n^3=4096 ; n=32: 32768 ; n=64: 262144.
PRIMES_N = {
 16:[65537, 188417, 1179649],        # 65537=F4(structured) ; all p>>4096
 32:[163841, 1179649],               # 163841=5*2^15+1 (structured) ; m modest
 64:[401537, 786433],                # p>>262144 ; 786433 = 3*2^18+1 (structured 2-adic)
}
print("door-(iv) cross-half phase relation B/A at top frequencies")
print("absom=|B|/|A| (1=>balanced) ; ang=arg(B/A) ; near_k=nearest n-th-root index ; defect=|k-round(k)| (0=>exact n-th root of unity)")
for n in (16,32,64):
    for p in PRIMES_N[n]:
        if (p-1)%n!=0: continue
        full = (n==16)
        m,out = run(p,n,full=full)
        tag = "FULL" if full else "samp"
        print(f"\n n={n} p={p} m=(p-1)/n={m} [{tag}] (top-5 freqs)")
        for mag,absom,ang,nk,defect in out:
            if absom is None: print("   A~0"); continue
            print(f"   |eta|/√n={mag:.4f}  |B|/|A|={absom:.4f}  arg(B/A)={ang:+.4f}  near {nk}/n  defect={defect:.4f}")
