import random
# Probe: monotone single-step iterates to S_{t+1}/S_t >= S_1/S_0 (= mean) for all t?
# And min_support(a) <= S_{t+1}/S_t <= max(a) two-sided envelope.
fails_iter = 0
fails_env = 0
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

    M = max(a)
    sup = [x for x in a if x > 0]
    mn = min(sup)
    for t in range(0, 7):
        if S(t) <= 0 or S(t + 1) <= 0:
            continue
        r = S(t + 1) / S(t)
        if not (mn - 1e-9 <= r <= M + 1e-9):
            fails_env += 1
        r0 = S(1) / S(0)
        if r < r0 - 1e-9:
            fails_iter += 1
    N += 1
print("trials=%d fails_iterate(r_t>=mean)=%d fails_envelope(min<=r<=max)=%d" % (N, fails_iter, fails_env))
