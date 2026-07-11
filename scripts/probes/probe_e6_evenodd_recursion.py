import itertools

# E6 2-adic tower recursion probe (for ArkLib _E6OddGradeVanish.lean, issue #444).
#
# bad-count object: distinct nonzero grade-m antipodal-folded freq vectors over (k+m)-subsets
# A subseteq Z/n, folded to length h=n/2 with sign by half-plane, with ALL LOWER grades
# j=1..m-1 folding to 0 (the "gate").
#
# IMPORTANT (matches the formal theorem's hypotheses):
#   * The gate j=1..m-1 is what forces antipodal closure. At grade m=1 the gate is EMPTY
#     (range(1,1) = empty), so cf(n,k,1) just counts grade-1 vectors of ARBITRARY subsets and
#     is naturally NONZERO. m=1 is the ungated SEED of the tower, NOT part of the "odd vanishes"
#     claim. The Lean theorem signedFold_odd_eq_zero assumes ANTIPODAL CLOSURE explicitly.
#   * The "odd half" claim of E6 is about GATED odd grades m>=3 (or m>=2 generally): the gate
#     includes j=1, which forces grade-1 fold = 0 <=> antipodal closure, and then every ODD-grade
#     fold of an antipodally-closed set vanishes (the sign-cancellation proven in Lean).
# So we test: EVEN recursion #bad_{2n}(k,2m') = #bad_n(k/2,m'); GATED ODD #bad_{2n}(k,m)=0 for odd m>=3.

def fhat(A, jj, n, h):
    v = [0]*h
    for a in A:
        e = (jj*a) % n
        v[e % h] += (1 if e < h else -1)
    return tuple(v)

def cf(n, k, m):
    h = n//2; w = k+m; vals = set(); Z = tuple([0]*h)
    if w > n or w < 0 or k < 0: return None
    for A in itertools.combinations(range(n), w):
        if all(fhat(A, j, n, h) == Z for j in range(1, m)):
            vals.add(fhat(A, m, n, h))
    vals.discard(Z); return len(vals)

print("=== EVEN recursion #bad_{2n}(k,2m') == #bad_n(k/2,m') (n in {4,8}) ===")
ok = True
for n in [4, 8]:
    for k in range(0, 2*n, 2):
        for mp in range(1, 4):
            m = 2*mp
            a = cf(2*n, k, m); b = cf(n, k//2, mp)
            if a is None or b is None: continue
            tag = "ok" if a == b else "MISMATCH"
            if a != b: ok = False
            print(f"  2n={2*n} k={k} m={m}: {a} vs n={n}(k/2={k//2},m'={mp})->{b}  {tag}")
print("EVEN: ALL HOLD" if ok else "EVEN: MISMATCHES")

# GATED odd grades m >= 3 (the gate j=1..m-1 includes grade 1, forcing antipodal closure).
print("\n=== GATED ODD #bad_{2n}(k,m)==0 for ODD m>=3 (gate forces antipodal closure) (n in {4,8}) ===")
ok2 = True
for n in [4, 8]:
    for k in range(0, 2*n):
        for m in [3, 5, 7]:
            a = cf(2*n, k, m)
            if a is None: continue
            if a != 0:
                ok2 = False; print(f"  2n={2*n} k={k} m={m}: {a} NONZERO (gated odd should vanish)")
print("GATED ODD: ALL ZERO" if ok2 else "GATED ODD: NONZERO FOUND")

# m=1 is the ungated seed: NOT part of the odd-vanishing claim (printed for transparency only).
print("\n=== m=1 (UNGATED SEED, NOT an odd-vanishing case; naturally nonzero) ===")
for n in [4, 8]:
    row = [cf(2*n, k, 1) for k in range(0, 2*n)]
    print(f"  2n={2*n} grade-1 counts (ungated seed): {row}")
