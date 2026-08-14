#!/usr/bin/env python3
# Probe: residualRatio is PERMUTATION-INVARIANT in the (k+1)-tuple t
# => ratioImage factors through (k+1)-element SUBSETS => #ratioImage <= C(n, k+1)
# (vs the crude falling-factorial #injTuples = n!/(n-k-1)!).
# Probe-first per rule 2: PROPER thin 2-power mu_n, p >> n^3, p == 1 mod n, NEVER n=q-1.
import itertools, math, random

def is_prime(m):
    if m < 2: return False
    for q in range(2, int(m**0.5)+1):
        if m % q == 0: return False
    return True

def find_prime(n, beta):
    target = int(n**beta)
    p = ((target // n) + 1) * n + 1
    while not is_prime(p):
        p += n
    return p

def det_mod(M, p):
    M = [row[:] for row in M]
    nn = len(M); det = 1
    for i in range(nn):
        piv = None
        for r in range(i, nn):
            if M[r][i] % p != 0: piv = r; break
        if piv is None: return 0
        if piv != i:
            M[i], M[piv] = M[piv], M[i]; det = (-det) % p
        inv = pow(M[i][i], p-2, p)
        det = (det * M[i][i]) % p
        for r in range(i+1, nn):
            f = (M[r][i] * inv) % p
            for c in range(i, nn):
                M[r][c] = (M[r][c] - f*M[i][c]) % p
    return det % p

def bordered_det(dom, t, y, k, p):
    M = []
    for a in range(k+1):
        row = []
        for b in range(k+1):
            if b < k: row.append(pow(dom[t[a]], b, p))
            else:     row.append(y[t[a]] % p)
        M.append(row)
    return det_mod(M, p)

def residual_ratio(dom, t, u0, u1, k, p):
    R0 = bordered_det(dom, t, u0, k, p)
    R1 = bordered_det(dom, t, u1, k, p)
    if R1 == 0: return None
    return (-R0 * pow(R1, p-2, p)) % p

random.seed(1)
hdr = "{:>4} {:>3} {:>10} {:>5} {:>8} {:>8} {:>8} {:>9} {:>9}".format(
    'n','k','p','beta','permInv','#imgTup','#imgSet','C(n,k+1)','falling')
print(hdr)
all_inv = True
all_le = True
for n, beta in [(8,4),(8,5),(16,4),(16,4.5),(32,4)]:
    p = find_prime(n, beta)
    mu = sorted({pow(x, (p-1)//n, p) for x in range(1,p)})
    assert len(mu) == n, (len(mu), n)
    assert all(pow(x,n,p)==1 for x in mu)
    dom = mu
    for k in [1,2,3]:
        if k+1 > n: continue
        coeffs0 = [random.randrange(p) for _ in range(k)]
        coeffs1 = [random.randrange(p) for _ in range(k)]
        u0 = {}; u1 = {}
        for idx, xv in enumerate(dom):
            base0 = sum(c*pow(xv,j,p) for j,c in enumerate(coeffs0))
            base1 = sum(c*pow(xv,j,p) for j,c in enumerate(coeffs1))
            u0[idx] = (base0 + random.randrange(p)) % p   # OFF-code
            u1[idx] = (base1 + random.randrange(p)) % p   # OFF-code
        idxs = list(range(n))
        tuples = []
        if math.comb(n,k+1) <= 4000:
            for comb in itertools.combinations(idxs, k+1):
                for perm in itertools.permutations(comb):
                    tuples.append(perm)
        else:
            seen=set()
            while len(seen) < 300:
                comb = tuple(sorted(random.sample(idxs,k+1)))
                seen.add(comb)
            for comb in seen:
                for perm in itertools.permutations(comb):
                    tuples.append(perm)
        perm_inv = True
        img_tup = set()
        set_ratio = {}
        for t in tuples:
            r = residual_ratio(dom, t, u0, u1, k, p)
            if r is None: continue
            img_tup.add(r)
            s = tuple(sorted(t))
            if s in set_ratio:
                if set_ratio[s] != r: perm_inv = False
            else:
                set_ratio[s] = r
        img_set = set(set_ratio.values())
        falling = 1
        for j in range(k+1): falling *= (n-j)
        cnk = math.comb(n,k+1)
        le_ok = (len(img_set) <= cnk) and (len(img_tup) <= cnk)
        all_inv = all_inv and perm_inv
        all_le = all_le and le_ok
        print("{:>4} {:>3} {:>10} {:>5} {:>8} {:>8} {:>8} {:>9} {:>9}".format(
            n,k,p,beta,str(perm_inv),len(img_tup),len(img_set),cnk,falling))
print("VERDICT perm-invariant ALL:", all_inv, " | #img <= C(n,k+1) ALL:", all_le)
