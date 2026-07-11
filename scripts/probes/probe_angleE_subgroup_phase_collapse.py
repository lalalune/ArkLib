#!/usr/bin/env python3
"""
ANGLE E, MECHANISM VERIFICATION: why the EXACT Jacobi tower does NOT give an explicit subgroup
shift sum.  The subgroup-restriction identity is

  S_quad = sum_{x in mu_n} leg(x+1)
         = sum_x [x in mu_n] leg(x+1)
         = (n/(p-1)) sum_{j=0}^{n-1} sum_{x in F_p^*} chi_n^{j}(x) leg(x+1)      [indicator average]
         = (n/(p-1)) sum_{j=0}^{n-1} J_j ,   J_j := sum_x chi_n^j(x) leg(x+1).

Each |J_j| = sqrt(p) EXACTLY (classical Jacobi sum, modulus sqrt p) for j not in {0, n/2}.
The Salie HOPE: the sqrt(p) exactness of each level transfers to S_quad.
The REALITY (this probe): S_quad is a sum of n terms each of size ~ (n/(p-1)) sqrt p ~ n/sqrt p,
                          but with p-DEPENDENT PHASES; the net is governed by those phases =
                          exactly the BGK/Weil argument the subgroup restriction reintroduces.

T1: verify the average identity S_quad == (n/(p-1)) sum_j J_j EXACTLY (sanity).
T2: show the PHASES arg(J_j) are p-dependent and NOT pinned (Salie pins them; here they wander)
    => the subgroup sum cannot be read off the (exact) magnitudes.
T3: the comparison that matters for the PRIZE: the floor object is the ADDITIVE period
    eta_b = sum_{x in mu_n} e_p(bx), NOT the shift sum. Confirm eta_b's max ~ sqrt(n log(p/n))
    (the open BGK floor) while the multiplicative shift S_quad stays O(sqrt n). So even a perfect
    explicit S_quad would NOT touch the prize floor: wrong object.
"""
import cmath, math

def is_prime(n):
    if n<2: return False
    for p in (2,3,5,7,11,13,17,19,23,29,31,37):
        if n%p==0: return n==p
    d=n-1;r=0
    while d%2==0: d//=2;r+=1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x=pow(a,d,n)
        if x==1 or x==n-1: continue
        for _ in range(r-1):
            x=x*x%n
            if x==n-1: break
        else: return False
    return True
def factorize(n):
    f={};d=2
    while d*d<=n:
        while n%d==0: f[d]=f.get(d,0)+1;n//=d
        d+=1 if d==2 else 2
    if n>1: f[n]=f.get(n,0)+1
    return f
def primitive_root(p):
    phi=p-1;facs=list(factorize(phi).keys())
    for g in range(2,p):
        if all(pow(g,phi//q,p)!=1 for q in facs): return g
def find_prime(n,beta,skip=0):
    t=int(n**beta);c=t-(t%n)+1
    if c<=t: c+=n
    f=0
    while True:
        if is_prime(c) and (c-1)%n==0 and (c-1)//n>1:
            if f==skip: return c
            f+=1
        c+=n
def leg(t,p):
    t%=p
    if t==0: return 0
    return 1 if pow(t,(p-1)//2,p)==1 else -1
def banner(t): print("="*84); print(t); print("="*84)

def setup(n,p):
    g=primitive_root(p)
    dl=[0]*p; x=1
    for a in range(p-1): dl[x]=a; x=x*g%p
    h=pow(g,(p-1)//n,p); sub=[]; y=1
    for _ in range(n): sub.append(y); y=y*h%p
    return g,dl,sub

def J_j(n,p,dl,j):
    # CORRECT DUALITY.  mu_n = {x : x^n = 1} = n-torsion = { x : dl[x] = 0 mod (p-1)/n }.
    # Its indicator is the AVERAGE over the ORDER-N characters psi_j(x)=exp(2 pi i j dl[x]/n)
    # WHOSE KERNEL is the index-n subgroup -- WRONG group. To pick out mu_n (n-torsion) we need
    # the DUAL group of size (p-1)/n.  Equivalently:  [x in mu_n] = (1/N) sum_{t=0}^{N-1}
    #   exp(2 pi i t * dl[x] / (p-1)) ... summed over the N=(p-1)/n characters that are trivial
    # on mu_n.  Concretely psi_t(x)=exp(2 pi i (n*t) dl[x]/(p-1)), t=0..N-1, kills mu_n's complement.
    # So S_quad = (1/N) sum_{t=0}^{N-1} sum_{x!=0,-1} psi_t(x) leg(x+1),  N=(p-1)/n.
    # Each inner sum is a Jacobi sum J(psi_t, leg) with |.|=sqrt p (for psi_t nontrivial & != leg).
    N=(p-1)//n; w=2*math.pi/(p-1)
    s=0j
    for x in range(1,p):
        xp1=(x+1)%p
        if xp1==0: continue
        s += leg(xp1,p)*cmath.exp(1j*w*((n*j*dl[x])%(p-1)))
    return s  # = J(psi_j, leg)

def T1_identity():
    banner("T1: verify S_quad == (1/N) sum_{t=0}^{N-1} J(psi_t,leg)  (N=(p-1)/n) -- EXACT?")
    print("   mu_n = n-torsion; its DUAL has size N=(p-1)/n (LARGE), NOT n. Each J has |.|=sqrt p.")
    print("   This already shows the 'n-term Jacobi tower' is the WRONG dual: the real average is")
    print("   over (p-1)/n ~ p/n Jacobi sums of size sqrt p each => the cancellation IS the BGK sum.")
    for n in (8,):  # n=8 only: n=16 has N=4096 Jacobi sums x 65537 terms (too slow in pure py)
        p=find_prime(n,4.0); g,dl,sub=setup(n,p)
        N=(p-1)//n
        S_direct=sum(leg(x+1,p) for x in sub)
        # verify on a SMALL slice that the average reconstructs (full N-sum is p-sized; do it for n=8)
        if N<=2000:
            Jsum=sum(J_j(n,p,dl,t) for t in range(N))
            S_via=Jsum/N
            ok = abs(S_via.real-S_direct)<1e-6 and abs(S_via.imag)<1e-6
            print(f" n={n} p={p} N=(p-1)/n={N}: S_quad(direct)={S_direct:+d}   (1/N)sum_t J = "
                  f"{S_via.real:+.4f}{S_via.imag:+.4f}i   match={'YES' if ok else 'NO'}")
        else:
            print(f" n={n} p={p} N=(p-1)/n={N}: (N too large to sum all Jacobi terms; identity is classical)")

def T2_phases_wander():
    banner("T2: each Jacobi term has |.|=sqrt p (pinned) but PHASES wander w/ p (=> BGK, not Salie)")
    print("   Salie: phase = EXPLICIT root of unity (pinned). Here arg(J(psi_t,leg)) depends on p,")
    print("   and there are N=(p-1)/n ~ p/n of them -> the average IS the BGK incomplete sum.\n")
    for n in (8,):
        for skip in range(3):
            p=find_prime(n,4.0,skip); g,dl,sub=setup(n,p); sqp=math.sqrt(p)
            ts=[1,2,3,4,5]  # first few nontrivial dual characters
            mags=[round(abs(J_j(n,p,dl,t))/sqp,3) for t in ts]
            args=[round(cmath.phase(J_j(n,p,dl,t))/math.pi,3) for t in ts]
            print(f" n={n} p={p} (N=(p-1)/n={(p-1)//n}): for t={ts}")
            print(f"            |J|/sqrt p ={mags}  (all ~1 => each Jacobi term full size)")
            print(f"            arg(J)/pi  ={args}   <- MOVE across p (Weil-spread, not pinned)")

def T3_wrong_object():
    banner("T3: PRIZE object is the ADDITIVE period, NOT the multiplicative shift S_quad")
    print("   eta_b = sum_{x in mu_n} e_p(bx); M(n)=max_b|eta_b| ~ sqrt(n log(p/n)) (open floor).")
    print("   S_quad ~ O(sqrt n). Even an EXACT S_quad is the WRONG object for the prize floor.\n")
    for n in (8,16,32,64):
        p=find_prime(n,4.0); g,dl,sub=setup(n,p)
        # coset reps
        h=pow(g,(p-1)//n,p); seen=set(); reps=[]
        for b in range(1,p):
            if b in seen: continue
            reps.append(b); c=b
            for _ in range(n): seen.add(c); c=c*h%p
        w=2*math.pi/p
        M=0
        for b in reps:
            e=abs(sum(cmath.exp(1j*w*((b*x)%p)) for x in sub))
            if e>M: M=e
        Sq=abs(sum(leg(x+1,p) for x in sub))
        sqn=math.sqrt(n); floor=math.sqrt(n*math.log(p/n))
        print(f" n={n} p={p}: max|eta_b|={M:.2f} ({M/sqn:.2f} sqrt n, {M/floor:.2f}x floor) | "
              f"|S_quad|={Sq:.0f} ({Sq/sqn:.2f} sqrt n) | floor sqrt(n log(p/n))={floor:.2f}")

if __name__=='__main__':
    T1_identity(); T2_phases_wander(); T3_wrong_object()
