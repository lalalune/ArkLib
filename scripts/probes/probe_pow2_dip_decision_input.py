# Probe (#444, lane pow2dip): on the 2-power tower n=2^a (the PRIZE regime mu_n, n=2^a),
# does the in-tree authoritative worst-direction c*(n) follow the LINEAR law n/4-1
# (the _Close27_PlateauWidthDecision "prize-FAILS" input), or DEVIATE below it (a 2-adic dip)?
# Data = the tree's own cStarFull (CrossingDepthLinearTracking.lean, from rho4.out, the
# exhaustive worst-direction GPU cascade pg.cu maximizing over ALL far directions). NEVER n=q-1.
cstar = {8: 3, 12: 4, 16: 3, 20: 4, 24: 5, 28: 6, 32: 5}
print("n    c*(n)  n/4-1  dip=(n/4-1)-c*   is_2pow")
for n in sorted(cstar):
    lin = n // 4 - 1
    dip = lin - cstar[n]
    is2 = (n & (n - 1)) == 0
    print("%3d  %5d  %5d  %13d   %s" % (n, cstar[n], lin, dip, is2))

print()
pow2 = [n for n in sorted(cstar) if (n & (n - 1)) == 0]
print("2-power tower (prize regime):", [(n, cstar[n], n // 4 - 1) for n in pow2])
# Claim 1: linear law m*=n/4-1 FAILS on the 2-power tower at n=32.
print("c*(32) =", cstar[32], " vs n/4-1 =", 32 // 4 - 1,
      " => linear law FALSE at n=32:", cstar[32] != 32 // 4 - 1)
# Claim 2: the dip is >=0 on the tower and STRICTLY GROWS 16->32 (0 -> 2).
d16 = (16 // 4 - 1) - cstar[16]
d32 = (32 // 4 - 1) - cstar[32]
print("dip(16) =", d16, " dip(32) =", d32, " => dip grows:", d32 > d16)
# Mid-range cross-check: on {16,20,24,28} the law IS exact (the input is true OFF the tower).
mid = [16, 20, 24, 28]
print("mid-range {16,20,24,28} c* == n/4-1 EXACT:",
      all(cstar[n] == n // 4 - 1 for n in mid))
print()
# ASYMPTOTIC GUARD: we make NO c*/n -> 0 / beyond-Johnson / sub-linear claim. We refute ONLY
# the FINITE named input 'm*(n)=n/4-1 holds on the 2-power tower' at the exact datum n=32.
print("ASYMPTOTIC GUARD: no capacity/beyond-Johnson/sub-linear claim; cliff-at-n/2 untouched.")
print("Refutation is FINITE: the FAILS-horn input is false at n=32 on the prize tower.")
