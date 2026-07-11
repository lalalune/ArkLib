#!/usr/bin/env python3
"""#444 §7.8: does the EXACT-Bessel cosh-MGF CORE bound BEAT THE FLOOR at LARGE n, or is
"beats at n=8" an artifact?  + rule-3 thinness gate.

Object (axiom-clean in-tree, Frontier/CoshMGFIdentity.lean):
  Σ_b cosh(‖η_b‖ y) = Σ_r (q·E_r/(2r)!) y^{2r},  and per-b domination gives
    M(n) = max_b‖η_b‖ ≤ B(y) := arccosh( Σ_b cosh(‖η_b‖y) ) / y     (∀y>0).
For G=μ_n (n=2^μ) the CHAR-0 even-moment GF is the Bessel law (DyadicEnergyK1.lean):
    Σ_r E_r y^{2r}/(2r)! = I₀(2y)^{n/2}      (E_r^inf, char-0).
So the CHAR-0-IDEALIZED cosh-MGF bound (the BEST this mechanism can give IF the char-0
energies transferred to char-p) is
    B_char0(n,p) = min_{y>0} arccosh( p · I₀(2y)^{n/2} ) / y.
Floor (proven lower bound the prize must beat to reach CORE):  √(2 n log m), m=(p-1)/n.

THIS PROBE measures B_char0 vs floor as n GROWS along the prize regime (β≈4, m=p/n),
AND vs the TRUE char-p value (FFT periods) at the small n where both are computable,
AND the SADDLE y*(n) scaling, AND a rule-3 THINNESS gate (does the same bound on a RANDOM
neg-closed energy profile behave differently?).

Honesty: B_char0 is an IDEALIZED bound (uses char-0 E_r which §2 says are FALSE at prize via
the DC term n^{2r}/q).  The question is whether the MECHANISM ITSELF (even granted char-0
energies) has any asymptotic hope, or caps at/above the floor regardless.  Pure analytic +
exact-FFT cross-check.  Proper subgroups, multi-prime, never n=q-1.
"""
import math, numpy as np

def i0(z):
    # modified Bessel I0(z), series
    s = 0.0; term = 1.0; k = 0
    while True:
        s += term; k += 1
        term = (z/2.0)**(2*k) / (math.factorial(k)**2)
        if term < 1e-18*max(s,1.0) and k > 5: break
        if k > 2000: break
    return s

def log_i0(z):
    # large-z asymptotic log I0(z)=z-0.5log(2*pi*z)+log(1+1/(8z)+9/(128z^2)+...)
    if z > 40:
        return z - 0.5*math.log(2*math.pi*z) + math.log(1 + 1/(8*z) + 9/(128*z*z))
    return math.log(i0(z))

def bessel_saddle_bound(n, p):
    """min_{y>0} arccosh( p * I0(2y)^{n/2} ) / y.  RHS = exp(log p + (n/2) log I0(2y)).
    arccosh(X) = log(X + sqrt(X^2-1)) ~ log(2X) for large X, exact here."""
    def B(y):
        L = math.log(p) + (n/2.0)*log_i0(2*y)      # = log RHS
        # arccosh(e^L) = log(e^L + sqrt(e^{2L}-1)); for L large ~ L + log2; exact:
        # = L + log(1 + sqrt(1 - e^{-2L})) ; e^{-2L} tiny here
        ach = L + math.log(1.0 + math.sqrt(max(0.0, 1.0 - math.exp(-2*L))))
        return ach / y
    # 1-D minimize over y by wide geometric grid + golden-section refine (saddle can be y>>4 or <<0.02)
    ys = np.geomspace(1e-4, 60.0, 6000)
    vals = [B(y) for y in ys]
    i = int(np.argmin(vals))
    ylo, yhi = ys[max(0,i-1)], ys[min(len(ys)-1,i+1)]
    for _ in range(80):
        m1 = ylo + (yhi-ylo)/3; m2 = yhi - (yhi-ylo)/3
        if B(m1) < B(m2): yhi = m2
        else: ylo = m1
    ystar = 0.5*(ylo+yhi)
    return B(ystar), ystar

def isprime(x):
    if x < 2: return False
    for q in [2,3,5,7,11,13,17,19,23,29,31,37]:
        if x % q == 0: return x == q
    d = x-1; s = 0
    while d % 2 == 0: d//=2; s+=1
    for a in [2,3,5,7,11,13,17,19,23,29,31,37]:
        y = pow(a,d,x)
        if y in (1,x-1): continue
        ok=False
        for _ in range(s-1):
            y=y*y%x
            if y==x-1: ok=True; break
        if not ok: return False
    return True

def fac(x):
    f=set(); d=2
    while d*d<=x:
        while x%d==0: f.add(d); x//=d
        d+=1
    if x>1: f.add(x)
    return f

def proot(p):
    for g in range(2,p):
        if all(pow(g,(p-1)//q,p)!=1 for q in fac(p-1)): return g

def true_periods(p, n):
    g = proot(p); h = pow(g,(p-1)//n,p)
    ind = np.zeros(p); x = 1
    for _ in range(n): ind[int(x)] = 1.0; x = x*h % p
    eta = np.fft.fft(ind)
    return np.abs(eta)

def true_cosh_bound(p, n):
    """min_y arccosh(Σ_b cosh(|η_b|y))/y using the REAL char-p periods."""
    absb = true_periods(p, n)
    def B(y):
        S = float(np.sum(np.cosh(absb*y)))
        return math.acosh(S)/y
    ys = np.linspace(0.02, 3.5, 1200)
    vals=[B(y) for y in ys]; i=int(np.argmin(vals))
    return vals[i], ys[i], float(absb[1:].max())

# ---- prize-band primes p ≡ 1 (mod n), β≈4 (p ~ n^4), proper subgroup, never n=q-1 ----
def find_prime(n, target):
    p = target - (target % n) + 1
    for _ in range(200000):
        if p > n+1 and isprime(p) and (p-1) % n == 0: return p
        p += n
    return None

print("="*100)
print("PART A: CHAR-0-IDEALIZED Bessel-saddle CORE bound vs floor √(2n log m), prize regime β≈4 (p~n^4)")
print("  (the BEST the cosh-MGF mechanism could give if char-0 energies held in char-p)")
print("="*100)
print(f"{'n':>6} {'p~n^4':>16} {'m~n^3':>16} {'floor':>9} {'B_char0':>9} {'y*':>7} {'B/floor':>8}  verdict")
rows=[]
for mu in range(3, 21):           # n = 8 .. 2^20 (prize n~2^30)
    n = 2**mu
    p = n**4                      # nominal prize prime p~n^4 (bound needs only log p, m)
    m = n**3                      # m=(p-1)/n ~ n^3 at beta=4
    floor = math.sqrt(2*n*math.log(m))
    B0, ystar = bessel_saddle_bound(n, p)
    ratio = B0/floor
    verdict = "BEATS" if ratio < 1 else "WORSE"
    rows.append((n,ratio))
    print(f"{n:>6} {p:>16} {m:>16} {floor:>9.3f} {B0:>9.3f} {ystar:>7.4f} {ratio:>8.4f}  {verdict}")

print()
print("PART A2: FIXED prize index m=2^128 (the ACTUAL prize: q=n·2^128, p~2^160), n=2^3..2^30")
print(f"{'n':>10} {'log2 m':>7} {'floor':>9} {'B_char0':>9} {'y*':>7} {'B/floor':>8}  verdict")
M_PRIZE = 2**128
for mu in list(range(3,11)) + [15, 20, 25, 30]:
    n = 2**mu
    p_eff = n * M_PRIZE          # q ≈ n·m ; use as the 'p' in the bound (p≈q)
    floor = math.sqrt(2*n*math.log(M_PRIZE))
    B0, ystar = bessel_saddle_bound(n, p_eff)
    ratio = B0/floor
    verdict = "BEATS" if ratio < 1 else "WORSE"
    print(f"{n:>10} {128:>7} {floor:>9.3f} {B0:>9.3f} {ystar:>7.4f} {ratio:>8.4f}  {verdict}")

print()
print("="*100)
print("PART B: CHAR-0-idealized vs TRUE char-p (FFT periods), small n, multi-prime — is char-0 bound a valid UPPER bound on M?")
print("="*100)
print(f"{'n':>5} {'p':>10} {'m':>9} {'M_true':>8} {'floor':>9} {'B_true':>9} {'B_char0':>9}  B0>=Mtrue? B0 vs floor")
for n in [8, 16]:
    cands=[find_prime(n, n**4), find_prime(n, n**4*7), find_prime(n, max(n**4*40, 2*10**6))]
    seen=set()
    for p in cands:
        if p is None or (p-1)%n or p in seen or p>4*10**6: continue
        seen.add(p)
        m=(p-1)//n
        floor=math.sqrt(2*n*math.log(m))
        Btrue, yt, Mtrue = true_cosh_bound(p, n)
        B0, ys = bessel_saddle_bound(n, p)
        ok = "Y" if B0 >= Mtrue-1e-6 else "N(!)"
        vf = "BEATS" if B0<floor else "WORSE"
        print(f"{n:>5} {p:>10} {m:>9} {Mtrue:>8.3f} {floor:>9.3f} {Btrue:>9.3f} {B0:>9.3f}    {ok:>5}   {vf}")
# n=32 at one moderate prime (FFT size ~1.05M, fine)
for n in [32]:
    p=find_prime(n, n**4)
    if p and (p-1)%n==0 and p<3*10**6:
        m=(p-1)//n; floor=math.sqrt(2*n*math.log(m))
        Btrue, yt, Mtrue = true_cosh_bound(p,n); B0,ys=bessel_saddle_bound(n,p)
        ok="Y" if B0>=Mtrue-1e-6 else "N(!)"; vf="BEATS" if B0<floor else "WORSE"
        print(f"{n:>5} {p:>10} {m:>9} {Mtrue:>8.3f} {floor:>9.3f} {Btrue:>9.3f} {B0:>9.3f}    {ok:>5}   {vf}")

print()
print("="*100)
print("PART C (rule-3 THINNESS GATE): is B_char0's behavior SPECIFIC to the thin 2-power μ_n,")
print("  or identical for a RANDOM neg-closed energy profile of the same Σ=p-n?  (thickness test)")
print("="*100)
print("  Compare the EXACT Bessel I0(2y)^{n/2} GF (thin 2-power) vs a Gaussian-energy profile")
print("  E_r=(2r-1)!!n^r (the generic/random Wick value) feeding the SAME cosh-MGF bound.")
print(f"{'n':>6} {'p~n^4':>13} {'floor':>9} {'B_thin(Bessel)':>15} {'B_gauss(Wick)':>15}  thin<gauss? (thin helps?)")
for mu in range(3, 13):
    n=2**mu; p=find_prime(n,n**4)
    if p is None: continue
    floor=math.sqrt(2*n*math.log((p-1)//n))
    Bthin,_=bessel_saddle_bound(n,p)
    # Gaussian-energy cosh-MGF: Σ_b cosh = p*exp(n y^2/2) (Wick GF), bound = min_y arccosh(p e^{ny^2/2})/y
    def Bg(y):
        L=math.log(p)+n*y*y/2.0
        return (L+math.log(1+math.sqrt(max(0,1-math.exp(-2*L)))))/y
    ys=np.linspace(0.02,4,2000); vg=[Bg(y) for y in ys]; Bgauss=min(vg)
    rel = "THIN-BEATS-GAUSS" if Bthin<Bgauss-1e-9 else "thin≥gauss"
    print(f"{n:>6} {p:>13} {floor:>9.3f} {Bthin:>15.3f} {Bgauss:>15.3f}  {rel}")

print()
print("="*100)
print("PART D: ANALYTIC asymptote — the cosh-MGF saddle REDUCES to the Gaussian/Wick leading term")
print("="*100)
print("  At small y, log I0(2y)=y^2-(1/4)y^4+...  so (n/2)log I0(2y)~(n/2)y^2 (the WICK term).")
print("  => saddle B* ~ min_y [log p+(n/2)y^2]/y = sqrt(2 n log p) at y*=sqrt(2 log p/n).")
print("  floor=sqrt(2 n log m).  ratio -> sqrt(log p/log m) = sqrt(beta/(beta-1)) (m~n^{beta-1}, p~n^beta).")
print(f"{'beta':>6} {'sqrt(beta/(beta-1))':>20}")
for beta in [4, 4.5, 5]:
    print(f"{beta:>6} {math.sqrt(beta/(beta-1)):>20.4f}")
print("  Numeric B_char0 vs sqrt(2 n log p) (beta=4): they MATCH -> the Bessel curvature is lower-order,")
print("  the bound caps at sqrt(beta/(beta-1))*floor ~ 1.155*floor at beta=4, NEVER reaching the floor.")
print(f"{'n':>10} {'B_char0':>11} {'sqrt(2n logp)':>14} {'floor':>11} {'B/floor':>9}")
for mu in [8, 12, 16, 20, 24]:
    n = 2**mu; p = n**4; m = n**3
    B0, _ = bessel_saddle_bound(n, p)
    glead = math.sqrt(2*n*math.log(p)); fl = math.sqrt(2*n*math.log(m))
    print(f"{n:>10} {B0:>11.3f} {glead:>14.3f} {fl:>11.3f} {B0/fl:>9.4f}")
print()
print("VERDICT: cosh-MGF/exact-Bessel-saddle caps at sqrt(beta/(beta-1))*floor (>floor), even granting")
print("char-0 energies. 'Beats floor at n=8' is a small-n artifact (BEATS only n<=16 at beta=4). The")
print("saddle collapses the exact Bessel to its Wick leading term => this IS the sec4 meta-theorem at")
print("the MGF level, now QUANTIFIED as a sqrt(beta/(beta-1)) gap. Thin-beats-Gauss (PART C) is real but")
print("lower-order: the I0 curvature cannot close the log p/log m ratio. CORE not closed, not faked.")
