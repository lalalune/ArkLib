import itertools, math
# #distinct e_2(T) over |T|=w with e_1(T)=0, T subset of mu_n exponents.
# e_1=0 <=> (Lam-Leung) T = union of antipodal pairs => gamma ∝ sum of w/2 distinct (n/2)-roots.
# Verify directly + scaling.
def e1_e2_vec(A,n):
    h=n//2
    # e1 = sum zeta^a; e2 via p2: gamma readout = sum zeta^{2a} (=p2). represent in Z[mu_{n/2}] basis len n/4
    e1=[0]*h
    for a in A: e1[a%h]+= (1 if a<h else -1)
    return tuple(e1)
def p2_vec(A,n):
    h=n//2; q=h//2  # mu_{n/2} basis length n/4
    v=[0]*q
    for a in A:
        e=(2*a)%n  # zeta^{2a} in mu_{n/2}; reduce mod zeta^{n/2}=... actually 2a mod n, in mu_{n/2} basis (zeta^2 prim (n/2)-root), exponent (2a)/2=a mod (n/2); reduce zeta_{n/2}^{a} with zeta_{n/2}^{n/4}=-1
        idx=a%(h)  # exponent of zeta_{n/2}
        if idx<q: v[idx]+=1
        else: v[idx-q]-=1
    return tuple(v)
def count(n,w):
    e2s=set()
    for A in itertools.combinations(range(n),w):
        e1=e1_e2_vec(A,n)
        if any(e1): continue  # need e1=0
        e2s.add(p2_vec(A,n))
    return len(e2s)
print("#distinct e_2(T) over |T|=w, e_1(T)=0  (worst-dir dir(k,k+2) bad count at t=k+2):")
for n in [8,16]:
    for w in range(2,n,2):
        c=count(n,w)
        if c: print(f"  n={n} w={w}: #bad={c}  (C(n/2,w/2)={math.comb(n//2,w//2)})", flush=True)
