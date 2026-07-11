import cmath, itertools
def roots(n):
    return [cmath.exp(2j*cmath.pi*k/n) for k in range(n)]
def is_zero(z, tol=1e-9):
    return abs(z) < tol
for n in [4,6,8,10,12]:
    R = roots(n)
    half = n//2
    pairs = [(k, k+half) for k in range(half)]
    ok = True
    cnt_pair_unions = 0
    for mask in range(1<<half):
        chosen = []
        for i in range(half):
            if mask & (1<<i):
                a,b = pairs[i]
                chosen += [R[a], R[b]]
        s = sum(chosen) if chosen else 0+0j
        if not is_zero(s):
            ok=False; break
        cnt_pair_unions += 1
    V1 = 0
    for r in range(n+1):
        for comb in itertools.combinations(range(n), r):
            s = sum(R[i] for i in comb) if comb else 0+0j
            if is_zero(s): V1 += 1
    print(f"n={n}: all pair-unions vanish={ok}, #pair-unions=2^{half}={cnt_pair_unions}, V_1(brute)={V1}, lower_bound_holds={V1>=cnt_pair_unions}")
