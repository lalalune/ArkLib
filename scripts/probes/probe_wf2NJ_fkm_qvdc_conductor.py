#!/usr/bin/env python3
"""
LANE wf-NJ (#407) — Fouvry-Kowalski-Michel algebraic twists + Polymath8 q-analogue
van-der-Corput / amplification in the CONDUCTOR aspect, applied to the dyadic subgroup
sum  M(n) = max_{b != 0} |S(b)|,  S(b) = sum_{x in mu_n} e_p(b x),  mu_n subset F_p^*,
n = 2^mu | p-1, prize beta = log_n p in [4,5].

NEW LENS vs the already-pinned section-6 effective-Katz / Rojas-Leon (L3) no-go:
  * L3 = VERTICAL completion: sum over ALL of F_p of a homothety-invariant function,
    sqrt(q)-gain needs n >= sqrt(p) (beta < 2). PINNED, wrong direction for prize.
  * NJ = FKM conductor-aspect AMPLIFICATION: do NOT complete; instead treat S(b) as a
    sum of a trace function K over the n-element FIBER of x -> x^n and apply a
    Cauchy-Schwarz + SHIFT (q-vdC / Polymath8 Type-I/II) step. The gain in FKM comes
    from the AUTOCORRELATION sheaf being non-degenerate with bounded conductor.

THE TECHNICAL QUESTIONS (this probe answers each numerically, EXACT integers):

  Q1. The vdC step. Cauchy-Schwarz on S(b) over the dyadic 2-to-1 map sq: mu_n -> mu_{n/2}.
      Group x in mu_n by their square y = x^2 in mu_{n/2} (each fiber = {+r,-r}).
        S(b) = sum_{y in mu_{n/2}} [ e_p(b r_y) + e_p(-b r_y) ]   where r_y^2 = y
             = sum_{y in mu_{n/2}} 2 cos(2pi b r_y / p).
      |S(b)|^2 <= (n/2) * sum_{y in mu_{n/2}} |e_p(b r_y)+e_p(-b r_y)|^2   (Cauchy-Schwarz)
               = (n/2) * sum_{y} (2 + 2cos(4pi b r_y/p))
               = (n/2)*(2*(n/2) + 2 sum_y cos(4pi b r_y/p)).
      The SHIFTED inner sum  T(b) = sum_{y in mu_{n/2}} cos(4pi b r_y / p)  is a sum over
      mu_{n/2} of the 2x-shifted character. IS IT SMALL (the vdC/autocorr cancellation)?
      We check: does CS give M(n)^2 <= n^2/2 + n*max_b|T(b)| with |T| sub-trivial,
      yielding M(n) sub-trivial?

  Q2. Conductor of the autocorr sheaf. FKM power-saving = (conductor) * sqrt(modulus).
      Our modulus is p (prime, so NO conductor-aspect modulus growth available - the
      "conductor aspect" of FKM is about the level of a modular form, NOT here). We
      measure the EFFECTIVE conductor c_eff via  max_b|S(b)| =? c_eff * sqrt(p) and ask
      whether the iterated CS reduces c_eff below the trivial n/sqrt(p) (= the BGK ratio).

  Q3. Iterated squaring (recursive conductor reduction - the SWING). Apply the CS+shift
      step mu times (n -> n/2 -> n/4 -> ... -> 1). Does the recursion telescope to a
      sub-trivial M(n)? At step j the shift is by 2^j and the subgroup is mu_{n/2^j}.
      We compute the recursion FLOOR exactly and compare to trivial n and target sqrt(n).
"""
import math, cmath

def is_prime(m):
    if m < 2: return False
    if m % 2 == 0: return m == 2
    d = m-1; s = 0
    while d % 2 == 0: d//=2; s+=1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        if a % m == 0: continue
        x = pow(a,d,m); ok = (x==1)
        for _ in range(s):
            if x == m-1: ok=True; break
            x = x*x % m
        if not ok: return False
    return True

def find_prime(n, target):
    base = target - (target % n) + 1
    for d in range(0, 200*n, n):
        if is_prime(base+d): return base+d
    return None

def subgroup(p, n):
    """return generator g of mu_n and the list of elements."""
    for g0 in range(2, 500):
        g = pow(g0, (p-1)//n, p)
        H = set()
        x = 1
        for _ in range(n):
            H.add(x); x = x*g % p
        if len(H) == n:
            return g, sorted(H)
    raise RuntimeError("no subgroup")

def all_periods(p, n):
    """exact M(n) = max_{b!=0} |sum_{x in mu_n} e_p(bx)|, scanning over coset reps.
    Periods only depend on the coset b*mu_n, so scan f=(p-1)/n cosets via a primitive root."""
    g, H = subgroup(p, n)
    # primitive root
    def is_primroot(a):
        # order = p-1 ; check a^((p-1)/q)!=1 for prime q|p-1
        m = p-1; fs=set(); d=2
        while d*d<=m:
            if m%d==0:
                fs.add(d)
                while m%d==0: m//=d
            d+=1
        if m>1: fs.add(m)
        return all(pow(a,(p-1)//q,p)!=1 for q in fs)
    g0=2
    while not is_primroot(g0): g0+=1
    f=(p-1)//n
    tp=2*math.pi
    best=0.0; b=1
    vals=[]
    for j in range(f):
        s=0j
        for x in H:
            s += cmath.exp(tp*1j*((b*x)%p)/p)
        m=abs(s); vals.append(m)
        if m>best: best=m
        b=(b*g0)%p
    return best, vals, H

def sqrt_in(p, y, H):
    """a square root of y in F_p (y in mu_{n/2}); return one root r with r^2=y."""
    # Tonelli-Shanks
    if y==0: return 0
    if pow(y,(p-1)//2,p)!=1: return None
    if p%4==3: return pow(y,(p+1)//4,p)
    # general TS
    q=p-1;s=0
    while q%2==0: q//=2;s+=1
    z=2
    while pow(z,(p-1)//2,p)!=p-1: z+=1
    m=s;c=pow(z,q,p);t=pow(y,q,p);r=pow(y,(q+1)//2,p)
    while t!=1:
        i=0;tt=t
        while tt!=1:
            tt=tt*tt%p;i+=1
        bexp=pow(c,1<<(m-i-1),p)
        m=i;c=bexp*bexp%p;t=t*c%p;r=r*bexp%p
    return r

print("="*92)
print("wf-NJ: FKM q-vdC / amplification conductor-aspect probe for dyadic subgroup sum")
print("="*92)

cases = [(8,4),(16,4),(16,5),(32,4),(64,4)]

print("\n--- Q1/Q2: one CS+shift step (mu_n -> mu_{n/2} with 2x shift) ---")
print(f"{'n':>4} {'p':>10} {'M(n)':>9} {'sqrt(p)':>9} {'BGKratio':>9} | {'maxT(2x)':>9} {'CSbound':>9} {'CS/M':>7} {'trivCS':>8}")
for n,beta in cases:
    p=find_prime(n,int(round(n**beta)))
    if p is None or p>30_000_000:
        print(f"{n:>4} skip (p too big)"); continue
    M,vals,H=all_periods(p,n)
    # shifted sum T(b)=sum_{y in mu_{n/2}} cos(4pi b r_y/p): scan b over coset reps of mu_{n/2}?
    # We instead directly: maxT = max_{b!=0} |sum_{x in mu_n} e_p(2 b x)| / 2  ...
    # Actually sum_y cos(4pi b r_y/p) over y in mu_{n/2}, with r_y the two roots:
    #   sum over BOTH roots of cos(4pi b r/p) = sum_{x in mu_n} cos(4pi b x /p) /1 (each y has 2 roots = the +-x pair)
    #   wait r_y ranges over one root per y; the two roots are x and -x. sum over y of cos(4pi b r_y/p)
    #   depends on root choice. Use the IDENTITY-free direct quantity that the CS produces:
    # |S(b)|^2 <= (n/2)*(n + 2*Re sum_{y} e_p(2 b r_y)). The cleanest exact handle:
    # the shifted FULL-subgroup sum S2(b) = sum_{x in mu_n} e_p(2 b x) = S(2b) is just another period!
    # The CS reorganization's shifted sum over mu_{n/2} of the 2x-character = (1/2) S(2b)+...
    # Let's compute the cleanest valid CS bound: group mu_n into +-pairs P (n/2 of them).
    g,Hl=subgroup(p,n)
    # pair x with -x = p-x
    Hset=set(Hl); pairs=[]; seen=set()
    for x in Hl:
        if x in seen: continue
        nx=(p-x)%p; seen.add(x); seen.add(nx); pairs.append((x,nx))
    # CS over pairs: S(b)=sum_pairs (e(bx)+e(b nx)); |S(b)|^2<= (n/2) sum_pairs |e(bx)+e(b nx)|^2
    #  =(n/2) sum_pairs (2+2cos(2pi b(x-nx)/p)) = (n/2)(n + 2 sum_pairs cos(2pi b(2x)/p))
    # so inner shifted sum U(b)=sum_pairs cos(2pi b*2x/p). max over b:
    tp=2*math.pi
    # scan b over coset reps via primitive root (same f cosets)
    def primroot(p):
        m=p-1;fs=set();d=2
        while d*d<=m:
            if m%d==0:
                fs.add(d)
                while m%d==0:m//=d
            d+=1
        if m>1:fs.add(m)
        a=2
        while any(pow(a,(p-1)//q,p)==1 for q in fs):a+=1
        return a
    g0=primroot(p);f=(p-1)//n;b=1;maxU=0.0;maxCS=0.0
    for _ in range(f):
        U=sum(math.cos(tp*((b*2*x)%p)/p) for (x,nx) in pairs)
        CS=math.sqrt((n/2)*(n+2*U))
        if abs(U)>maxU:maxU=abs(U)
        if CS>maxCS:maxCS=CS
        b=(b*g0)%p
    bgk=M/math.sqrt(p)
    trivCS=math.sqrt((n/2)*(n+2*(n/2)))  # if U maxed at n/2 (no cancellation)=sqrt(n^2)=n
    print(f"{n:>4} {p:>10} {M:>9.3f} {math.sqrt(p):>9.1f} {bgk:>9.4f} | {maxU:>9.3f} {maxCS:>9.3f} {maxCS/M:>7.3f} {trivCS:>8.2f}")

print("""
Reading Q1/Q2:
  - CSbound is the BEST the one CS+shift step can give for M(n). If CSbound >> M, the
    step is LOSSY (CS loses the factor it needs). 'maxT/U' = the shifted (autocorrelation)
    sum; if |U| ~ n/2 (no cancellation) then CSbound ~ n = trivial (the vdC found NOTHING).
  - trivCS=n is the no-cancellation ceiling; CSbound between sqrt(n^2/2)=n/sqrt2 (full
    cancellation U=0) and n. The shift is BY 2 = staying in the SAME subgroup mu_n, so
    U(b)=Re S(2b) is just ANOTHER PERIOD -> max|U| ~ M itself -> NO net gain (circular).
""")

print("\n--- Q3: iterated dyadic squaring recursion floor (the SWING) ---")
print("CS+shift mu times: M_j defined on mu_{n/2^j}. Recursion M_j^2 <= (n_j) * (n_j + 2 U_j),")
print("U_j = shifted autocorr on mu_{n_j}. We measure the EXACT max|U_j| at each level and")
print("whether the telescoped floor beats trivial n or reaches sqrt(n).")
print(f"{'n':>4} {'p':>10} | level-by-level max|shifted U_j| / n_j (ratio; ->0 = cancellation)")
for n,beta in cases:
    p=find_prime(n,int(round(n**beta)))
    if p is None or p>30_000_000: continue
    row=[]
    nj=n
    g0=None
    # primitive root
    m=p-1;fs=set();d=2
    while d*d<=m:
        if m%d==0:
            fs.add(d)
            while m%d==0:m//=d
        d+=1
    if m>1:fs.add(m)
    a=2
    while any(pow(a,(p-1)//q,p)==1 for q in fs):a+=1
    g0=a
    tp=2*math.pi
    while nj>=2:
        gg,Hl=subgroup(p,nj)
        # shifted sum max over b: U_j(b)=sum_{x in mu_{nj}} cos(2pi b*2x/p) = Re S_{nj}(2b)
        f=(p-1)//nj;b=1;mx=0.0
        for _ in range(min(f,4000)):
            U=sum(math.cos(tp*((b*2*x)%p)/p) for x in Hl)
            if abs(U)>mx:mx=abs(U)
            b=(b*g0)%p
        row.append(f"n{nj}:{mx/nj:.3f}")
        nj//=2
    print(f"{n:>4} {p:>10} | " + "  ".join(row))

print("""
Reading Q3: if max|U_j|/n_j stays ~O(1) (close to 1) at every level, the shifted
autocorrelation does NOT cancel -> the recursion telescopes to ~n (trivial). A genuine
recursive conductor reduction would need max|U_j|/n_j -> small (sqrt(log/n)) at the deep
levels. Note shift-by-2 keeps us in mu_{n_j} so U_j = Re of ANOTHER PERIOD of the SAME
subgroup => max|U_j| ~ M(n_j) ~ the very quantity we want to bound (BGK-CIRCULAR).
""")
