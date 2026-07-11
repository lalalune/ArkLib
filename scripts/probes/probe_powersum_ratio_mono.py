import numpy as np
rng = np.random.default_rng(0)
# Claim: for nonneg a, S_t = sum a_i^t. The ratio R_t = S_{t+1}/S_t is monotone increasing in t,
# and R_t <= max a_i, and R_t -> max a_i. (power-sum ratio / Chebyshev-sum / log-convexity)
fails = 0
tot = 0
for trial in range(5000):
    k = int(rng.integers(2, 8))
    a = rng.random(k) * int(rng.integers(1, 10))
    a = a.astype(float)
    def S(t):
        return float(np.sum(a ** t))
    mx = float(a.max())
    for t in range(1, 12):
        Rt = S(t + 1) / S(t)
        Rt1 = S(t + 2) / S(t + 1)
        tot += 1
        ok = (Rt <= Rt1 + 1e-9) and (Rt <= mx + 1e-9)
        if not ok:
            fails += 1
            if fails < 5:
                print("FAIL", a, t, Rt, Rt1, mx)
print("monotone-increasing power-sum ratio + bounded by max: %d fails / %d" % (fails, tot))
