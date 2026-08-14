import cmath, itertools, math
def roots(n):
    return [cmath.exp(2j*cmath.pi*k/n) for k in range(n)]
def is_zero(z, tol=1e-9):
    return abs(z) < tol
for n in [4,6,8,10,12]:
    R = roots(n)
    half = n//2
    pairs = [(k, k+half) for k in range(half)]
    # graded vanishing count by size
    Vsize = {}
    for r in range(n+1):
        c = 0
        for comb in itertools.combinations(range(n), r):
            s = sum(R[i] for i in comb) if comb else 0+0j
            if is_zero(s): c += 1
        Vsize[r] = c
    # pair-union graded: choosing j pairs -> size 2j, count C(half, j)
    ok = True
    rows = []
    for j in range(half+1):
        pu = math.comb(half, j)
        actual = Vsize.get(2*j, 0)
        holds = actual >= pu
        if not holds: ok=False
        rows.append((2*j, pu, actual, holds))
    print(f"n={n} half={half}: lower-bound C(half,j) <= V_size(2j) holds_all={ok}")
    for sz,pu,ac,h in rows:
        tight = "TIGHT" if pu==ac else ""
        print(f"   size={sz}: C={pu}  V={ac}  {('OK' if h else 'FAIL')} {tight}")
