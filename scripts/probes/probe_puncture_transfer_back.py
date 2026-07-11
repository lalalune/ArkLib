import itertools, random

def agreement(w, c):
    return sum(1 for a, b in zip(w, c) if a == b)

def list_at(C, w, t):
    return sum(1 for c in C if agreement(w, c) >= t)

def puncture(C, D):
    keep = [i for i in range(len(C[0])) if i not in D]
    return [tuple(c[i] for i in keep) for c in C]

def is_block_injective(C, D):
    Cp = puncture(C, D)
    return len(set(Cp)) == len(set(C))

def max_list_full(C, t, Fsize, n):
    F = list(range(Fsize)); m = 0
    for w in itertools.product(F, repeat=n):
        m = max(m, list_at(C, w, t))
    return m

def max_list_punct(C, D, t, Fsize):
    Cp = puncture(C, D); npr = len(Cp[0]); F = list(range(Fsize)); m = 0
    for w in itertools.product(F, repeat=npr):
        m = max(m, list_at(Cp, w, t))
    return m

# Transfer-back claim (to formalize): if the BLOCK puncture is injective on C, and the punctured
# code is list-decodable at threshold t with list L, then C is list-decodable at threshold t+|S|
# with the SAME list L (no |F| blow-up).
# We verify: max_list_full(C, t+|S|) <= max_list_punct(C, D, t) whenever block-injective.
random.seed(3); viol = 0; tests = 0; skipped_noninj = 0
for _ in range(600):
    Fsize = random.choice([2, 3]); n = random.choice([4, 5, 6])
    ncw = random.choice([2, 3, 4, 5, 6]); F = list(range(Fsize))
    C = set()
    while len(C) < ncw: C.add(tuple(random.choice(F) for _ in range(n)))
    C = list(C); k = random.choice([1, 2, 3])
    if k >= n: continue
    D = set(random.sample(range(n), k))
    if not is_block_injective(C, D):
        skipped_noninj += 1; continue
    t = random.choice(range(0, n - k + 1))
    Lp = max_list_punct(C, D, t, Fsize)         # punctured list at t
    Lf = max_list_full(C, t + k, Fsize, n)       # full list at t+k
    tests += 1
    if Lf > Lp:
        viol += 1
        if viol <= 5:
            print(f"VIOLATION F={Fsize} n={n} D={sorted(D)} t={t} k={k} Lpunct={Lp} Lfull(t+k)={Lf}")
print(f"block-injective tests={tests} violations={viol} (skipped non-injective={skipped_noninj})")

# Counterpoint: WITHOUT injectivity, does the same-list transfer-back FAIL? (justifies the hypothesis)
random.seed(9); inj_needed = 0; checked = 0
for _ in range(600):
    Fsize = random.choice([2, 3]); n = random.choice([4, 5]); ncw = random.choice([3, 4, 5, 6])
    F = list(range(Fsize)); C = set()
    while len(C) < ncw: C.add(tuple(random.choice(F) for _ in range(n)))
    C = list(C); k = random.choice([1, 2])
    if k >= n: continue
    D = set(random.sample(range(n), k))
    if is_block_injective(C, D): continue
    t = random.choice(range(0, n - k + 1))
    Lp = max_list_punct(C, D, t, Fsize); Lf = max_list_full(C, t + k, Fsize, n)
    checked += 1
    if Lf > Lp: inj_needed += 1
print(f"non-injective cases where same-list transfer-back FAILS (=> injectivity needed): {inj_needed}/{checked}")
