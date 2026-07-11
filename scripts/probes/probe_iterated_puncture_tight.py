import itertools, random

def agreement(w, c):
    return sum(1 for a,b in zip(w,c) if a==b)

def list_at(C, w, t):
    return sum(1 for c in C if agreement(w,c) >= t)

def max_list_full(C, t, Fsize, n):
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

# Tightness: rep code, k=2.
def rep_code(n):
    return [tuple([0]*n), tuple([1]*n)]

C = rep_code(6); Fsize = 2
tk = 4
Lf = max_list_full(C, tk, Fsize, 6)
k = 2; t = tk - k; D = {4,5}
act = max_list_punct(C, D, t, Fsize)
print(f"rep6: t+k={tk} Lfull={Lf} k={k} t={t} bound(|F|^k*L)={(Fsize**k)*Lf} actual={act}")

# Does the weaker |F|^(k-1) bound ever FAIL (proving full |F|^k is needed)?
random.seed(11); need_full = 0; checked = 0
for _ in range(400):
    Fsize = random.choice([2,3]); n = random.choice([4,5]); ncw = random.choice([3,4,5,6])
    F = list(range(Fsize)); C = set()
    while len(C) < ncw: C.add(tuple(random.choice(F) for _ in range(n)))
    C = list(C); k = random.choice([1,2])
    if k >= n: continue
    D = set(random.sample(range(n), k)); t = random.choice(range(0, n-k+1))
    Lf = max_list_full(C, t+k, Fsize, n); act = max_list_punct(C, D, t, Fsize)
    checked += 1
    if Lf > 0 and act > (Fsize**(k-1))*Lf:
        need_full += 1
print(f"cases where weaker |F|^(k-1) bound FAILS (full |F|^k needed): {need_full}/{checked}")
