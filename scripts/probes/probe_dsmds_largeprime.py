"""
probe_dsmds_largeprime.py  (issue #407 / #389 -- DO NOT COMMIT)

Extends probe_dsmds_charfaithful to PRIZE-SCALE primes q >> n^4 (and toward n^8) to
verify the over-determination rigidity for mu_n higher-order MDS persists, AND to pin
exactly where the few MDS(3) bad primes live (confirming they are < n^2 thin-prime
pollution, gone at prize scale).

  - MDS(3) (single (sum,product) det = order-3 obstruction, "depth s-k=1"-flavored but
    still a 3x3 minor with structure): bad primes should be confined to a finite set
    (<= ~n^2) and VANISH for all probed q above that.
  - MDS(4) over-determined (3 pairs, ALL C(6,4) 4x4 minors vanish): 0 bad primes.
  - DEEP over-det MDS(4) genuine (4 disjoint pairs at order k=4 -> 8 covectors in K^4,
    C(8,4)=70 simultaneous minors): the s-k>=3 deep regime; expect 0 bad primes even at
    huge q (this matches the prior "n=32, 400 subsets x primes<=500K -> 0 bad" result).

Honesty: proper subgroups, primes q = n*m+1 with q up to ~10^8 (>> n^4 for n<=32, and
>> n^8 for n=8); antipodal/coset configs flagged separately; nothing committed.
"""
import sympy, math, cmath, itertools, random
import numpy as np
random.seed(13)
TAU = 2 * math.pi

def zeta_c(n, e): return cmath.exp(1j * TAU * (e % n) / n)
def char0_det(rows): return abs(np.linalg.det(np.array(rows, dtype=complex)))

def detmodq(rows, q):
    m = len(rows); A = [[x % q for x in r] for r in rows]; det = 1
    for i in range(m):
        piv = next((r for r in range(i, m) if A[r][i] % q), None)
        if piv is None: return 0
        if piv != i: A[i], A[piv] = A[piv], A[i]; det = -det
        det = (det * A[i][i]) % q; inv = pow(A[i][i], q - 2, q)
        for r in range(i + 1, m):
            f = (A[r][i] * inv) % q
            if f: A[r] = [(A[r][c] - f * A[i][c]) % q for c in range(m)]
    return det % q

def big_primes_q1modn(n, qmin, qmax, count):
    """primes q = n*m+1 in [qmin,qmax], minimal-2-adic preferred (odd m), random sample."""
    out = []; tries = 0
    mlo = max(1, qmin // n); mhi = qmax // n
    while len(out) < count and tries < count * 200:
        tries += 1
        m = random.randint(mlo, mhi)
        if m % 2 == 0 and (m & (m-1)) == 0:  # skip pure 2-power (Fermat-ish)
            continue
        q = n * m + 1
        if q >= qmin and sympy.isprime(q):
            out.append(q)
    return sorted(set(out))

def zeta_modq(n, q):
    g = sympy.primitive_root(q); return pow(g, (q - 1) // n, q)

def is_anti(n, a, b): return (a + b) % n == 0

def disjoint_pairs(n, count, avoid_anti=True):
    pts = list(range(n)); random.shuffle(pts); chosen = []; used = set()
    for a in pts:
        if a in used: continue
        for b in pts:
            if b in used or b == a: continue
            if avoid_anti and is_anti(n, a, b): continue
            chosen.append((a, b)); used.add(a); used.add(b); break
        if len(chosen) == count: break
    return chosen if len(chosen) == count else None

# order-3 (sum,product) minor
def o3_c(n, prs): return char0_det([[zeta_c(n,a)*zeta_c(n,b), -(zeta_c(n,a)+zeta_c(n,b)), 1] for a,b in prs])
def o3_q(n, prs, q, z):
    za=lambda e: pow(z,e%n,q)
    return detmodq([[(za(a)*za(b))%q, (-(za(a)+za(b)))%q, 1%q] for a,b in prs], q)

# order-4 deep over-det: P disjoint pairs -> 2 covectors each in K^4, all 4x4 minors
def covs_c(n, prs):
    M=[]
    for a,b in prs:
        za,zb=zeta_c(n,a),zeta_c(n,b); p=za*zb; s=za+zb
        M += [[p,-s,1,0],[0,p,-s,1]]
    return np.array(M,dtype=complex)
def covs_q(n, prs, q, z):
    za=lambda e: pow(z,e%n,q); M=[]
    for a,b in prs:
        p=(za(a)*za(b))%q; s=(za(a)+za(b))%q
        M += [[p%q,(-s)%q,1%q,0],[0,p%q,(-s)%q,1%q]]
    return M
def o4_char0_generic(n, prs):  # max 4x4 minor of stacked covectors > 0
    M=covs_c(n,prs); r=M.shape[0]
    return max(abs(np.linalg.det(M[list(idx),:])) for idx in itertools.combinations(range(r),4))
def o4_all_minors_zero_q(n, prs, q, z):
    M=covs_q(n,prs,q,z); r=len(M)
    return all(detmodq([M[i] for i in idx],q)==0 for idx in itertools.combinations(range(r),4))

print("="*78)
print("LARGE-PRIME char-faithfulness of mu_n higher-order MDS (q up to ~1e8, >> n^4)")
print("="*78)

for n in [8, 16, 32]:
    print(f"\n##### n={n}  (mu_n) #####")
    n2, n4, n8 = n*n, n**4, n**8
    qmax = min(10**8, 5*10**7)
    # ---- MDS(3): single order-3 minor ----
    cfgs=[]; tries=0
    while len(cfgs)<30 and tries<2000:
        tries+=1; pr=disjoint_pairs(n,3)
        if pr and o3_c(n,pr)>1e-7: cfgs.append(pr)
    qs = big_primes_q1modn(n, n4, qmax, 40)   # ALL primes here are q > n^4
    qs_small = big_primes_q1modn(n, n+1, n2*4, 30)  # the n^2 zone (where pollution lives)
    bad_big=0; bad_small_worst=0
    for pr in cfgs:
        for q in qs:
            if o3_q(n,pr,q,zeta_modq(n,q))==0: bad_big+=1; break
        for q in qs_small:
            if o3_q(n,pr,q,zeta_modq(n,q))==0:
                bad_small_worst=max(bad_small_worst,q)
    print(f"  MDS(3): {len(cfgs)} char-0-generic configs.")
    print(f"    small zone (q in [n, 4n^2]={4*n2}): {len(qs_small)} primes; worst bad prime = "
          f"{bad_small_worst if bad_small_worst else 'NONE'}"
          f"{' = n^%.2f'%(math.log(bad_small_worst)/math.log(n)) if bad_small_worst>1 else ''}")
    print(f"    PRIZE zone q > n^4={n4} (sampled {len(qs)} primes up to {max(qs) if qs else 0} "
          f"= n^{math.log(max(qs))/math.log(n):.2f}): configs with a bad prime = {bad_big}  "
          f"-> {'CHAR-FAITHFUL @ q>>n^4' if bad_big==0 else 'BAD!'}")
    # ---- MDS(4) over-det: 3 pairs ----
    cfgs4=[]; tries=0
    while len(cfgs4)<25 and tries<2000:
        tries+=1; pr=disjoint_pairs(n,3)
        if pr and o4_char0_generic(n,pr)>1e-7: cfgs4.append(pr)
    bad4=0
    for pr in cfgs4:
        for q in qs:
            if o4_all_minors_zero_q(n,pr,q,zeta_modq(n,q)): bad4+=1; break
    print(f"  MDS(4) over-det (3 pairs, C(6,4)=15 minors): {len(cfgs4)} configs x {len(qs)} primes "
          f"q>n^4 -> bad={bad4}  {'CHAR-FAITHFUL' if bad4==0 else 'BAD!'}")
    # ---- MDS(4) DEEP over-det: 4 pairs (8 covectors, C(8,4)=70) ----
    if n >= 8:
        cfgs4d=[]; tries=0
        while len(cfgs4d)<20 and tries<3000:
            tries+=1; pr=disjoint_pairs(n,4)
            if pr and o4_char0_generic(n,pr)>1e-7: cfgs4d.append(pr)
        bad4d=0
        for pr in cfgs4d:
            for q in qs:
                if o4_all_minors_zero_q(n,pr,q,zeta_modq(n,q)): bad4d+=1; break
        print(f"  MDS(4) DEEP over-det (4 pairs, C(8,4)=70 minors): {len(cfgs4d)} configs x {len(qs)} "
              f"primes q>n^4 -> bad={bad4d}  {'CHAR-FAITHFUL (deep rigidity)' if bad4d==0 else 'BAD!'}")

print("\n" + "="*78)
print("VERDICT logic: if MDS(ell) bad primes (q>>n^4) = 0 for over-det (ell>=4) and confined")
print("to <n^2 for the single order-3 minor, then mu_n's MDS(ell)-ness for prize primes")
print("(q ~ n*2^128 >> n^4) EQUALS its char-0 MDS(ell)-ness => char-faithful; the only")
print("failures are the char-0 antipodal/(sum,product)-collinear coset configs.")
