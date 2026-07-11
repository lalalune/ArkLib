import random
# Probe general log-convexity spacing: S_{t} * S_{t+2k} >= (S_{t+k})^2 for all k>=0?
# (generalizes adjacent powerSum_sq_le_mul which is the k=1 case)
# Also: ratio over a gap S_{t+k}/S_t is monotone in t (wider bracket).
fails_spacing = 0
fails_gapmono = 0
N = 0
for trial in range(60000):
    n = random.randint(1, 8)
    a = [random.random() * random.choice([0.5, 1, 3, 10]) for _ in range(n)]
    if random.random() < 0.3:
        for i in range(n):
            if random.random() < 0.3:
                a[i] = 0.0
    if sum(a) == 0:
        continue

    def S(t):
        return sum(x ** t for x in a)

    for t in range(0, 5):
        for k in range(0, 4):
            lhs = S(t) * S(t + 2 * k)
            rhs = S(t + k) ** 2
            if lhs < rhs - 1e-7 * (1 + abs(rhs)):
                fails_spacing += 1
    # gap-ratio monotone: S_{t+1+k}/S_{t+k}... already covered. test S_{t+k}/S_t monotone in t for fixed k
    for k in range(1, 4):
        for t in range(0, 4):
            if S(t) <= 0 or S(t + 1) <= 0:
                continue
            r1 = S(t + k) / S(t)
            r2 = S(t + 1 + k) / S(t + 1)
            if r1 > r2 + 1e-7 * (1 + abs(r2)):
                fails_gapmono += 1
    N += 1
print("trials=%d fails_logconvex_spacing(S_t*S_{t+2k}>=S_{t+k}^2)=%d fails_gap_ratio_mono=%d" % (N, fails_spacing, fails_gapmono))
