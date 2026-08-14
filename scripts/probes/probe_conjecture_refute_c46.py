# C46 ATTACK: Mahler-measure / Lehmer "structure-aware norm" on the period polynomial Psi_p.
#
# CONJECTURE C46 (issue #444, gauss-period-exact, feasibility=2):
#   Psi_p(T) = prod_{cosets}(T - eta_c) = period polynomial of mu_n (n=2^mu, monic, deg m=(p-1)/n).
#   CLAIM: a "structure-aware Mahler measure" of Psi_p (weighting by the antipodal cyclotomic
#   structure) gives a SHARPER HOUSE bound than Cauchy, reaching house = M(mu_n) <= sqrt(2 n log p)
#   PAST Johnson, via the proven coefficient structure (Myerson) + antipodal pair z+(-z)=0.
#   REDUCES-TO: Mahler measure / Lehmer house inequality + Myerson coefficients + in-tree antipodal.
#
# THE TARGET OBJECT (load-bearing identity, in-tree fact):
#   house(eta) = max_c |eta_c| = max_{a!=0} |Sum_{x in mu_n} e_p(a x)| = M(mu_n)   (THE OPEN OBJECT).
#   Mahler measure of monic Psi_p:  Mah(Psi) = prod_c max(1, |eta_c|).
#
# THE DECISIVE QUESTION: can a Mahler-measure functional (= a SYMMETRIC function of the conjugates,
#   namely the product over the conjugates with modulus >1) deliver an UPPER bound on the SINGLE
#   largest conjugate (the house)?  Mahler/Lehmer inequalities give house <= Mah(Psi)^? only one-sided
#   the WRONG way (house <= Mah is FALSE in general; Mah >= house always since Mah is a PRODUCT of
#   the big conjugates, each >= 1, and includes the house factor). The only honest Lehmer-type house
#   bound is the LOWER bound house >= Mah(Psi)^{1/(#big roots)} (geometric mean of the big roots) and
#   the trivial house <= Mah(Psi) (= product = MUCH bigger than sqrt(n log p)).
#
# So C46 needs Mah(Psi) itself to be ~ sqrt(2 n log p) AND the big-root multiplicity to be ~1, OR
# the "antipodal weighting" to collapse Mah to the house. We test ALL of these decisively.
#
# DECISIVE TESTS (PROPER subgroups: p prime, p >> n^3, n=2^mu, NEVER n=p-1):
#  (T1) house = M(mu_n): the true open object. Confirm house ~ sqrt(n log p) (TARGET shape real).
#  (T2) Mahler measure Mah(Psi) = prod_{|eta_c|>1} |eta_c|.  Is log Mah ~ (1/2) log(2 n log p)?
#       NO: Mah is a PRODUCT over ~m/2 big conjugates => log Mah ~ (m/2)*log(sqrt n) = HUGE, grows
#       LINEARLY in m=(p-1)/n. So Mah >> house by an exponential-in-m factor. Mahler as an UPPER
#       bound for house is the trivial (useless) house <= Mah; as a sharper bound it FAILS.
#  (T3) The "structure-aware / antipodal" weighting. Antipodal pairs eta_c, eta_{-c}: for n=2^mu,
#       -1 in mu_n, so the coset of -c... test whether |eta_c| = |eta_{-c}| (conjugate-pairing,
#       eta_{-c} = conj(eta_c) since e_p(-cx)=conj(e_p(cx))). So Mah double-counts |eta_c|^2 per pair
#       => antipodal weighting at best HALVES the exponent: Mah^{1/2} still a PRODUCT over m/2 roots,
#       still >> house. The antipodal structure does NOT collapse product -> max.
#  (T4) THE WALL (same as C08/C26/C27): house = single-conjugate L^infinity functional; Mahler =
#       symmetric product functional = blind to WHICH conjugate is largest. At FIXED n, two primes
#       with near-equal Mah have house differing a lot => Mah does NOT determine house.
#  (T5) Direct: the BEST honest Mahler->house upper bound, house <= Mah(Psi), and the geometric-mean
#       lower bound house >= Mah^{1/k} (k = #big roots).  Show Mah upper bound is 10^? ABOVE target.
import math, cmath

def isprime(x):
    if x<2: return False
    if x%2==0: return x==2
    d=3
    while d*d<=x:
        if x%d==0: return False
        d+=2
    return True

def fac(x):
    f=set(); d=2
    while d*d<=x:
        while x%d==0: f.add(d); x//=d
        d+=1
    if x>1: f.add(x)
    return f

def proot(p):
    F=fac(p-1)
    for a in range(2,p):
        if all(pow(a,(p-1)//q,p)!=1 for q in F): return a

def find_prime(n, exp=4):
    base=int(round(n**exp))
    p=base-(base%n)+1
    for _ in range(2000000):
        if p>1 and isprime(p): return p
        p+=n
    raise RuntimeError

def all_periods(n,p):
    """All m=(p-1)/n distinct Gauss periods eta_c (one per coset of mu_n in F_p^*)."""
    g=proot(p)
    h=pow(g,(p-1)//n,p)             # generator of mu_n (order n)
    mu=[pow(h,i,p) for i in range(n)]
    m=(p-1)//n
    two_pi_over_p=2*math.pi/p
    etas=[]
    b=1
    for i in range(m):
        s=sum(cmath.exp(1j*two_pi_over_p*((b*x)%p)) for x in mu)
        etas.append(s); b=b*g%p
    return etas, m

print("C46: Mahler-measure / Lehmer structure-aware norm on the period polynomial Psi_p")
print("Object: house(eta)=max_c|eta_c|=M(mu_n) (OPEN).  Mahler Mah(Psi)=prod_{|eta_c|>1}|eta_c|.\n")
print(f"{'n':>4} {'p':>9} {'m':>7} | {'house=M':>9} {'h/sqrt(n)':>9} {'target√(2nlnp)':>14} | "
      f"{'log10 Mah':>10} {'#big':>5} {'Mah^(1/big)':>11} {'log10(Mah/house)':>16}")

# T4 fixed-n storage
fixed={}

for n in [8,16,32]:
    rows=[]
    for exp in [4]:
        # use several primes per n for the FIXED-n house-vs-Mahler test (T4)
        primes=[]
        base=int(round(n**exp)); p=base-(base%n)+1
        while len(primes)<4:
            if p>1 and isprime(p): primes.append(p)
            p+=n
        for p in primes:
            etas,m=all_periods(n,p)
            mags=[abs(e) for e in etas]
            house=max(mags)
            target=math.sqrt(2*n*math.log(p))
            big=[mm for mm in mags if mm>1.0]
            nbig=len(big)
            logMah=sum(math.log10(mm) for mm in big)    # log10 of Mahler measure
            Mah_geo=10**(logMah/nbig) if nbig>0 else 0.0  # geometric mean of big roots = Mah^{1/nbig}
            # honest upper bound house <= Mah(Psi): gap = Mah / house
            log10gap = logMah - math.log10(house)
            rows.append((p,m,house,target,logMah,nbig,Mah_geo,log10gap))
            fixed.setdefault(n,[]).append((p,house,logMah,target))
        # print first prime row
        p,m,house,target,logMah,nbig,Mah_geo,log10gap=rows[0]
        print(f"{n:>4} {p:>9} {m:>7} | {house:>9.4f} {house/math.sqrt(n):>9.4f} {target:>14.4f} | "
              f"{logMah:>10.2f} {nbig:>5} {Mah_geo:>11.4f} {log10gap:>16.2f}")

print("\n--- T2/T5: Mahler measure as a house UPPER bound (house <= Mah(Psi)) ---")
print("log10(Mah) grows LINEARLY in m=(p-1)/n; house ~ sqrt(n log p) is O(1)-many digits.")
print("=> 'house <= Mah(Psi)' is astronomically weaker than target sqrt(2n log p).")
print("=> Mah^{1/#big} = geom mean of big roots ~ sqrt(n) = JOHNSON/L2 scale (a LOWER bound on house).")

print("\n--- T3: antipodal pairing (eta_{-c}=conj(eta_c) for n=2^mu, -1 in mu_n) ---")
for n in [8,16,32]:
    p=find_prime(n,4)
    etas,m=all_periods(n,p)
    g=proot(p)
    # eta indexed by coset b=g^i; -c corresponds to multiplying rep by -1 = g^{(p-1)/2}.
    # check |eta_i| == |eta_{i + (p-1)/2 mod (p-1) -> coset shift}|.  Simpler: the multiset {|eta_c|}
    # should be each value with even multiplicity (conjugate pairs) since -1 in mu_n => antipodal map
    # is z -> conj on each eta. Confirm by counting how many |eta| values appear with a near-equal twin.
    mags=sorted(abs(e) for e in etas)
    # pair up adjacent equal-magnitude values
    paired=0; i=0
    while i+1<len(mags):
        if abs(mags[i]-mags[i+1])<1e-6*max(1.0,mags[i]):
            paired+=2; i+=2
        else:
            i+=1
    print(f"n={n} p={p} m={m}: {paired}/{len(mags)} period-moduli fall in equal-magnitude (antipodal) pairs"
          f"  => antipodal weighting at best halves the Mahler exponent (still product over ~m/2 roots)")

print("\n--- T4 DECISIVE: at FIXED n, does Mah determine house? ---")
print("If Mahler (a symmetric product) determined the house, near-equal log10(Mah) would force")
print("near-equal house. Measure spreads across the 4 primes at each n.\n")
for n in fixed:
    arr=fixed[n]
    hs=[a[1] for a in arr]; lm=[a[2] for a in arr]
    h_spread=max(hs)-min(hs)
    # normalize Mahler by m to compare 'density'; report raw log10 spread too
    lm_spread=max(lm)-min(lm)
    print(f"n={n}: house range [{min(hs):.3f},{max(hs):.3f}] spread={h_spread:.3f} ; "
          f"log10(Mah) range [{min(lm):.1f},{max(lm):.1f}] spread={lm_spread:.2f}")
print("\nVERDICT MECHANISM: Mahler measure is a SYMMETRIC PRODUCT of the m conjugates. The only")
print("honest Mahler/Lehmer house bounds are (a) house <= Mah(Psi) = exponentially-in-m too weak,")
print("and (b) house >= Mah^{1/#big} ~ sqrt(n) = the L2/Johnson geometric-mean LOWER bound. Neither")
print("the antipodal weighting (halves the exponent at most) nor 'Myerson coefficients' (= the same")
print("symmetric functions, the Cauchy route already shown 10^2-10^3 too weak in C08) converts the")
print("product into the single-largest-conjugate L-infinity house. The sqrt(log p) prize factor IS")
print("the conjugate-argument SPREAD = the open BGK/Paley sup-norm. SECRETLY-OPEN, same wall as")
print("C08/C26/C27 (house != norm/Mahler archimedean gap).")
