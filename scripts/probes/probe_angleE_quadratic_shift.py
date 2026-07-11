#!/usr/bin/env python3
"""
ANGLE E, focused follow-up: the QUADRATIC-character shift sum over mu_n is the ACTUAL
Salie-eligible object.  k = m/2 makes chi^{m/2} = Legendre symbol leg.  Then
   S_quad := sum_{x in mu_n} leg(x + 1)
is a quadratic-character sum over the dyadic subgroup -- the legitimate Salie analogue.

T_A : is |S_quad| EXACTLY explicit (small integer, p-STABLE, ~ O(1) or ~sqrt(n))?
      Test across many primes per n.  Salie => p-stable discrete value.
T_B : decompose S_quad via leg(x+1) = leg(x) leg(1 + x^{-1}) and Jacobi sums -- is there a
      genuine sqrt(n) cancellation or is |S_quad| = O(1) (i.e. it's a Jacobi-sum-controlled
      object that is TINY, NOT a sqrt(n) floor)?
T_C : the FULL Gauss/Jacobi exact value: sum_{x in F_p} leg(x+1) chi_n(x) where chi_n cuts
      out mu_n -- is THAT a Jacobi sum J(leg, chi_n) of modulus sqrt(p)?  This is the exact
      classical identity; we check whether the SUBGROUP restriction inherits it.
T_D : compare to additive floor and to the MCA prize budget. Does ANY explicit quadratic
      shift value reach the window/floor, or is it strictly below Johnson (prize-inert)?

HONESTY: stdlib only, exact mod-p, cmath magnitudes. p prime, n=2^mu, n|p-1, p>>n^3 thin.
"""
import cmath, math

def is_prime(n):
    if n < 2: return False
    for p in (2,3,5,7,11,13,17,19,23,29,31,37):
        if n % p == 0: return n == p
    d=n-1; r=0
    while d%2==0: d//=2; r+=1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x=pow(a,d,n)
        if x==1 or x==n-1: continue
        for _ in range(r-1):
            x=x*x%n
            if x==n-1: break
        else: return False
    return True

def factorize(n):
    f={}; d=2
    while d*d<=n:
        while n%d==0: f[d]=f.get(d,0)+1; n//=d
        d+=1 if d==2 else 2
    if n>1: f[n]=f.get(n,0)+1
    return f

def primitive_root(p):
    phi=p-1; facs=list(factorize(phi).keys())
    for g in range(2,p):
        if all(pow(g,phi//q,p)!=1 for q in facs): return g
    raise RuntimeError

def find_prime(n, beta, skip=0):
    target=int(n**beta); cand=target-(target%n)+1
    if cand<=target: cand+=n
    found=0
    while True:
        if is_prime(cand) and (cand-1)%n==0 and (cand-1)//n>1:
            if found==skip: return cand
            found+=1
        cand+=n

def mu_n(n,p,g=None):
    if g is None: g=primitive_root(p)
    h=pow(g,(p-1)//n,p); sub=[];x=1
    for _ in range(n): sub.append(x); x=x*h%p
    return sub

def leg(t,p):
    t%=p
    if t==0: return 0
    return 1 if pow(t,(p-1)//2,p)==1 else -1

def S_quad(sub,p):
    return sum(leg(x+1,p) for x in sub)

def banner(t): print("="*84); print(t); print("="*84)

def T_A():
    banner("T_A: S_quad = sum_{x in mu_n} leg(x+1)  -- explicit & p-stable? (Salie test, exact int)")
    for n in (8,16,32,64):
        print(f"\n n={n}:  sqrt(n)={math.sqrt(n):.3f}")
        for skip in range(5):
            p=find_prime(n,4.0,skip); sub=mu_n(n,p)
            S=S_quad(sub,p)
            print(f"   p={p:>10}  S_quad = {S:+3d}   |S|/sqrt(n)={abs(S)/math.sqrt(n):.4f}")

def T_C_jacobi():
    banner("T_C: FULL-FIELD identity  sum_{x in F_p^*} leg(x+1) chi_n^j(x)  = Jacobi-type, |.|=sqrt p?")
    print("   chi_n = order-n character cutting out mu_n. The subgroup sum is the chi_n-AVERAGE:")
    print("   sum_{x in mu_n} f(x) = (n/(p-1)) sum_{j: chi^{(p-1)/n * ...}} ... we directly test the")
    print("   classical full-field Jacobi sum J_j := sum_x leg(x+1) chi^{j(p-1)/n}(x).\n")
    for n in (8,16):
        p=find_prime(n,4.0); g=primitive_root(p)
        # discrete log
        dl=[0]*p; x=1
        for a in range(p-1): dl[x]=a; x=x*g%p
        sqp=math.sqrt(p)
        print(f" n={n} p={p} sqrt p={sqp:.2f}:")
        # chi_n(x) = exp(2pi i * (dl[x] mod n)/n)
        for j in range(1,n):
            s=0j; w=2*math.pi/n
            for x in range(1,p):
                xp1=(x+1)%p
                if xp1==0: continue
                s += leg(xp1,p)*cmath.exp(1j*w*((dl[x]*j)%n))
            print(f"   j={j:2d}: |J_j|/sqrt p = {abs(s)/sqp:.4f}  (J_j={s.real:+.2f}{s.imag:+.2f}i)")

def T_D_floor_compare():
    banner("T_D: does explicit quadratic shift reach the prize window/Johnson, or stay prize-inert?")
    print("   Johnson radius proxy ~ 1 - sqrt(rho); floor object scale ~ sqrt(n log(p/n)).")
    print("   |S_quad| ~ O(1)/O(sqrt n) means it is FAR BELOW the BGK floor M(n) ~ sqrt(n log(p/n)).\n")
    for n in (8,16,32,64):
        p=find_prime(n,4.0); sub=mu_n(n,p)
        S=abs(S_quad(sub,p))
        floor=math.sqrt(n*math.log(p/n))
        print(f" n={n} p={p}: |S_quad|={S:.0f}  vs sqrt(n log(p/n))={floor:.2f}  "
              f"ratio={S/floor:.3f}  -> {'BELOW floor (inert)' if S<floor else 'reaches floor'}")

if __name__=='__main__':
    T_A(); T_C_jacobi(); T_D_floor_compare()
