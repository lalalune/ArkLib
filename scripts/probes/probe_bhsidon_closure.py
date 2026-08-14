#!/usr/bin/env python3
"""
probe_bhsidon_closure.py

Probe-first validation for the B_h-Sidon (general-h) STRUCTURAL closure bricks
that generalize the landed B_2 (IsSidonSet) closure family.

B_h-Sidon predicate on a set S in an additive abelian group:
  every h-fold sum a_1+...+a_h = b_1+...+b_h (a_i,b_j in S) forces the
  MULTISETS {a_1..a_h} = {b_1..b_h}. (h=2 is the plain Sidon set.)

Structural facts we intend to formalize (and MUST hold universally, char-free,
thin or thick — these are EASY structural closure lemmas, NOT the CORE wall):
  (C1) hereditary: T subset S, S is B_h-Sidon  =>  T is B_h-Sidon.
  (C2) translation invariance: S is B_h-Sidon  =>  (x + S) is B_h-Sidon.
  (C3) monotone in h DOWNWARD on the *representation-triviality*? NO -- check:
       is B_h-Sidon => B_{h-1}-Sidon? (a known subtlety; probe it, do NOT assume)
  (C4) base cases: empty, singleton are B_h-Sidon for all h>=1.

We ALSO probe the prize-regime thin subgroup mu_n to see at what depth h the
multiplicative subgroup mu_n itself STOPS being B_h-Sidon (the depth-ell where
W_r first turns on) -- this is the §0 datum, reported but NOT formalized as a
clean general-h statement. We do NOT claim to prove the bootstrap (that's the wall);
we only want the EASY closure lemmas (C1,C2,C4) verified before formalizing,
and an honest read on (C3).

NEVER validate structural triviality on n=q-1 (full group). Use PROPER mu_n.
"""

import itertools
from itertools import combinations_with_replacement as cwr

def is_bh_sidon_bruteforce(S, h):
    """Brute force: does every h-fold sum have a unique multiset representation?
    S: list of group elements (ints mod m via the caller). Returns True/False.
    We map each h-multiset to its sum; B_h-Sidon iff sum -> multiset is injective
    on the multisets (i.e. no two distinct h-multisets share a sum)."""
    seen = {}
    for combo in cwr(range(len(S)), h):
        s = sum(S[i] for i in combo)
        key = tuple(sorted(S[i] for i in combo))
        if s in seen:
            if seen[s] != key:
                return False
        else:
            seen[s] = key
    return True

def mu_n(n, p):
    """multiplicative subgroup of order n in F_p^*  (requires n | p-1)."""
    assert (p - 1) % n == 0, f"n={n} does not divide p-1={p-1}"
    g = primitive_root(p)
    step = pow(g, (p - 1) // n, p)
    out, x = [], 1
    for _ in range(n):
        out.append(x)
        x = (x * step) % p
    return sorted(set(out))

def primitive_root(p):
    if p == 2:
        return 1
    factors = set()
    phi = p - 1
    d = 2
    m = phi
    while d * d <= m:
        while m % d == 0:
            factors.add(d); m //= d
        d += 1
    if m > 1:
        factors.add(m)
    for g in range(2, p):
        if all(pow(g, phi // f, p) != 1 for f in factors):
            return g
    raise RuntimeError("no primitive root")

# ----- (C1) hereditary, (C2) translate, (C4) base cases -----
import random
random.seed(1)

def test_closure(group_mod, trials=4000):
    c1_fail = c2_fail = c3_examples = 0
    c3_total = 0
    for _ in range(trials):
        m = group_mod
        k = random.randint(0, 6)
        S = random.sample(range(m), min(k, m))
        h = random.randint(2, 4)
        sid = is_bh_sidon_bruteforce(S, h)
        if not sid:
            continue
        # C1 hereditary: drop a random element
        if S:
            T = S[:]
            T.pop(random.randrange(len(T)))
            if not is_bh_sidon_bruteforce(T, h):
                c1_fail += 1
        # C2 translate
        x = random.randint(0, m - 1)
        St = [(a + x) % m for a in S]
        if not is_bh_sidon_bruteforce(St, h):
            c2_fail += 1
        # C3 downward in h: B_h => B_{h-1}?  (probe, do not assume)
        if h >= 3:
            c3_total += 1
            if not is_bh_sidon_bruteforce(S, h - 1):
                c3_examples += 1
    return c1_fail, c2_fail, c3_examples, c3_total

print("=== (C1) hereditary / (C2) translate / (C3) downward-in-h ===")
for m in (17, 23, 31, 41, 97):
    c1, c2, c3, c3t = test_closure(m)
    print(f"  Z_{m}: C1(hereditary) fails={c1}  C2(translate) fails={c2}  "
          f"C3(B_h=>B_(h-1)) counterexamples={c3}/{c3t}")

print("\n=== base cases (C4): empty + singleton B_h-Sidon for h=2..5 ===")
ok = True
for h in range(2, 6):
    if not is_bh_sidon_bruteforce([], h): ok = False
    if not is_bh_sidon_bruteforce([7], h): ok = False
print(f"  empty + singleton B_h-Sidon all h in 2..5: {ok}")

print("\n=== §0 datum: depth ell where PROPER mu_n stops being B_h-Sidon ===")
# prize-regime-ish: n=2^a, p = 1 mod n, p >> n. NEVER n=q-1.
cases = [
    (4, 13), (4, 41), (8, 41), (8, 73), (8, 97), (16, 97), (16, 193),
]
for n, p in cases:
    if (p - 1) % n != 0:
        continue
    G = mu_n(n, p)
    if len(G) == p - 1:
        print(f"  n={n} p={p}: SKIP (full group)")
        continue
    depth = None
    for h in range(2, 7):
        if not is_bh_sidon_bruteforce(G, h):
            depth = h
            break
    print(f"  mu_{n} in F_{p} (|G|={len(G)}, proper): first h NOT B_h-Sidon = {depth}")
