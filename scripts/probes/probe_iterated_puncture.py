# Probe: iterated multi-point puncture pigeonhole for absolute list-decodability.
# Claim (to formalize): if C is list-decodable at absolute threshold (t+k) with list L on
# the FULL index set, then deleting any k coordinates (the puncture), C' is list-decodable
# at threshold t with list |F|^k * L.
#
# We DIRECTLY measure the worst-case punctured list size after deleting a set D of k coords,
# at threshold t, and compare to |F|^k * L_full(t+k). Honest: small explicit codes + random.
import itertools, random

def agreement(w, c):
    return sum(1 for a,b in zip(w,c) if a==b)

def list_at(C, w, t):
    # absolute: # codewords agreeing with w on >= t coords
    return sum(1 for c in C if agreement(w,c) >= t)

def max_list_full(C, t, Fsize, n):
    # worst over all words in F^n
    F = list(range(Fsize))
    m = 0
    for w in itertools.product(F, repeat=n):
        m = max(m, list_at(C, w, t))
    return m

def puncture(C, D):
    keep = [i for i in range(len(C[0])) if i not in D]
    return [tuple(c[i] for i in keep) for c in C]

def max_list_punct(C, D, t, Fsize):
    Cp = puncture(C, D)
    npr = len(Cp[0])
    F = list(range(Fsize))
    m = 0
    for w in itertools.product(F, repeat=npr):
        m = max(m, list_at(Cp, w, t))
    return m

random.seed(7)
viol = 0
tests = 0
for trial in range(400):
    Fsize = random.choice([2,3])
    n = random.choice([4,5,6])
    ncw = random.choice([2,3,4,5])
    F = list(range(Fsize))
    C = set()
    while len(C) < ncw:
        C.add(tuple(random.choice(F) for _ in range(n)))
    C = list(C)
    k = random.choice([1,2,3])
    if k >= n: continue
    D = set(random.sample(range(n), k))
    t = random.choice(range(0, n-k+1))
    Lfull = max_list_full(C, t+k, Fsize, n)
    bound = (Fsize**k) * Lfull
    actual = max_list_punct(C, D, t, Fsize)
    tests += 1
    if actual > bound:
        viol += 1
        if viol <= 5:
            print(f"VIOLATION F={Fsize} n={n} D={sorted(D)} t={t} k={k} Lfull(t+k)={Lfull} bound={bound} actual={actual}")
print(f"\ntests={tests} violations={viol}")
# also check tightness: does |F|^k factor actually get used? report max actual/Lfull ratio when Lfull>0
