import math

def fp_subgroup(p, n):
    assert (p - 1) % n == 0
    g = None
    for cand in range(2, p):
        order = 1
        y = cand % p
        while y != 1:
            y = (y * cand) % p
            order += 1
            if order > p:
                break
        if order == p - 1:
            g = cand
            break
    h = pow(g, (p - 1) // n, p)
    S = []
    x = 1
    for _ in range(n):
        S.append(x)
        x = (x * h) % p
    return sorted(set(S))

# CONCENTRATION law for the binomial window: for gap d, the incidence inc(c) = #{x in mu_n : x^d = c}
# is EITHER 0 or EXACTLY gcd(d,n), and the number of c with nonzero incidence is EXACTLY n/gcd(d,n).
# i.e. the image of x->x^d is the subgroup mu_{n/gcd(d,n)}, hit uniformly with multiplicity gcd(d,n).
# => window total = (n/g)*g = n (consistent w/ the proven brick), but this is the SHARPER
# "0-or-g, supported on n/g scalars" structure.
def test(p, n):
    S = fp_subgroup(p, n)
    out = []
    for d in range(1, n):
        g = math.gcd(d, n)
        nz_count = 0
        all_ok = True
        for c in S:
            inc = sum(1 for x in S if pow(x, d, p) == c)
            if inc != 0:
                nz_count += 1
                if inc != g:
                    all_ok = False
        out.append((d, g, nz_count, all_ok, nz_count == n // g))
    return out

cases = [(17,4),(41,4),(521,4),(73,8),(97,8),(193,8),(337,8),(257,8),(257,16),(4129,8)]
allpass = True
for p, n in cases:
    if (p-1)%n!=0 or (p-1)//n<2: continue
    for d, g, nz, all_g, supp_ok in test(p, n):
        ok = all_g and supp_ok
        if not ok: allpass = False
        flag = "" if ok else "  <<< FAIL"
        print(f"p={p:5d} n={n:3d} d={d:3d}: gcd={g} support={nz} (==n/g={n//g}? {supp_ok}) all-inc-eq-g={all_g}{flag}")
    print()
print("ALL PASS (inc in {0,g}, support == n/g):", allpass)
