#!/usr/bin/env python3
"""Pre-registered probe (#389): the G³-scaling ASSEMBLY for the zero-sum triple count.

Verifies the exact decomposition that turns qr_shift_count (N = #consecutive nonzero-square
pairs) into the unordered zero-sum triple count = cubic list size, for a multiplicative
subgroup G of order n in F_q. This is the structural identity the next Lean brick must prove:

  6 * #{unordered {a,b,c} ⊆ G distinct : a+b+c=0}  =  n * M  -  3 * n * [-2 ∈ G]
  where M = #{y ∈ G : -(1+y) ∈ G},  and  T_ord = #{(a,b,c) ∈ G³ : a+b+c=0} = n*M.

Steps verified independently:
  (1) scaling bijection:  T_ord = n * M.
  (2) diagonal correction: ordered-with-distinct = T_ord - 3*n*[-2∈G]   (a=b ⟺ -2a=c∈G).
  (3) div by 6:           unordered = ordered-distinct / 6.
  (4) for G = QR (q≡1 mod4):  M = N = (q-5)/4  and  [-2∈G] ⟺ q≡1 mod 8,
      giving n(q-5)/24 (q≡5 mod8) / n(q-17)/24 (q≡1 mod8).
Also checks general subgroups (order n | q-1, not just QR).
"""
import itertools

def factor(m):
    fs, d = [], 2
    while d * d <= m:
        while m % d == 0:
            fs.append(d); m //= d
        d += 1
    if m > 1:
        fs.append(m)
    return fs

def primitive_root(q):
    fs = set(factor(q - 1))
    for g in range(2, q):
        if all(pow(g, (q - 1) // p, q) != 1 for p in fs):
            return g
    raise RuntimeError

def subgroup(q, n):
    assert (q - 1) % n == 0
    g = primitive_root(q)
    w = pow(g, (q - 1) // n, q)
    return set(pow(w, i, q) for i in range(n))

def check(q, n):
    G = subgroup(q, n)
    Gl = sorted(G)
    # direct unordered zero-sum triple count
    unordered = sum(1 for T in itertools.combinations(Gl, 3) if sum(T) % q == 0)
    # (1) T_ord
    T_ord = sum(1 for a in Gl for b in Gl for c in Gl if (a + b + c) % q == 0)
    M = sum(1 for y in Gl if (-(1 + y)) % q in G)
    ok_scale = (T_ord == n * M)
    # (2) diagonal: -2 in G?
    neg2_in = ((-2) % q) in G
    ordered_distinct = sum(1 for a in Gl for b in Gl for c in Gl
                           if (a + b + c) % q == 0 and a != b and a != c and b != c)
    ok_diag = (ordered_distinct == T_ord - 3 * n * (1 if neg2_in else 0))
    # (3) div 6
    ok_div6 = (ordered_distinct == 6 * unordered)
    return unordered, T_ord, M, neg2_in, ok_scale, ok_diag, ok_div6

if __name__ == "__main__":
    print("== QR domains (q≡1 mod4): closed form n(q-5)/24 or n(q-17)/24 ==")
    for q in [29, 37, 41, 53, 61, 73, 89, 97, 101, 109, 113, 137, 149]:
        if (q - 1) % 2: continue
        n = (q - 1) // 2
        u, T, M, neg2, s, d, v = check(q, n)
        cf = n * (q - 17) // 24 if q % 8 == 1 else n * (q - 5) // 24
        Npred = (q - 5) // 4
        print(f"q={q} n={n}: triples={u} cf={cf} {'OK' if u==cf else 'FAIL'} | "
              f"M={M}(=N={Npred}:{M==Npred}) -2inG={neg2}(q%8={q%8}) | "
              f"scale={s} diag={d} div6={v}")
    print("\n== general subgroups (order n | q-1, not QR) ==")
    for q, ns in [(61, [5, 6, 10, 12, 15, 20, 30]),
                  (73, [8, 9, 12, 18, 24, 36]),
                  (41, [5, 8, 10, 20])]:
        for n in ns:
            u, T, M, neg2, s, d, v = check(q, n)
            # general homogeneous prediction: (n*M - 3n[-2inG])/6
            pred = (n * M - 3 * n * (1 if neg2 else 0)) // 6
            print(f"q={q} n={n}: triples={u} pred=(nM-3n[-2])/6={pred} "
                  f"{'OK' if u==pred else 'FAIL'} | scale={s} diag={d} div6={v}")
