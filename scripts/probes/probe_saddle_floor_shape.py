import math

# Probe for the saddle-floor SHAPE extraction (#444 §6.2 MGF lane).
# Chain proven (CoshMGFSaddleAssembled.period_le_saddle_closedForm):
#   ||eta|| <= log(2 q^2) / y*,  with y*^2 = 2 log q / n, q = |F|, n = |G|.
# UNDISCHARGED PROSE: "this is Theta(sqrt(n log q)) up to absolute constant C".
# Goal: pin an EXPLICIT absolute constant C with  log(2q^2)/y* <= C * sqrt(n log q).
#
# Algebra: log(2q^2) = log2 + 2 logq ; y* = sqrt(2 logq/n).
#   bound = (log2 + 2 logq) / sqrt(2 logq/n) = (log2 + 2 logq) * sqrt(n/(2 logq))
#   bound / sqrt(n logq) = (log2 + 2 logq)/(sqrt(2 logq) * sqrt(logq))
#                        = (log2 + 2 logq)/(sqrt(2) * logq)
#                        = log2/(sqrt2 * logq) + sqrt2.
# Monotone DECREASING in logq, so its sup over q>=2 (logq>=log2) is at q=2:
#   log2/(sqrt2*log2) + sqrt2 = 1/sqrt2 + sqrt2 = 3/sqrt2 = 2.12132...

def ratio(q):
    logq = math.log(q)
    ystar = math.sqrt(2*logq/q**0)  # placeholder, recompute properly below
    return None

print("=== empirical bound/sqrt(n logq) across prize regime (n=2^a, q=n^beta) ===")
for beta in [4,5]:
    for a in [4,5,6,7,8]:
        n = 2**a; q = n**beta
        logq = math.log(q)
        ystar = math.sqrt(2*logq/n)
        bound = math.log(2*q**2)/ystar
        target = math.sqrt(n*logq)
        print(f"n={n:4d} q=n^{beta} bound/sqrt(n logq)={bound/target:.5f}")

print(f"\nasymptotic leading constant sqrt(2) = {math.sqrt(2):.5f}")
print(f"proposed uniform C = 3/sqrt(2)   = {3/math.sqrt(2):.5f}")

print("\n=== uniform claim: bound/sqrt(n logq) <= 3/sqrt2 for ALL q>=2 (any n>0) ===")
C = 3/math.sqrt(2)
ok = True
for q in [2,3,5,10,100,1000,10**6,10**12,10**18]:
    logq = math.log(q)
    r = math.log(2)/(math.sqrt(2)*logq) + math.sqrt(2)
    good = r <= C + 1e-12
    ok = ok and good
    print(f"q={q:>20} ratio={r:.6f} <= {C:.6f} ? {good}")
print("UNIFORM C=3/sqrt2 holds for all q>=2:", ok)

# Cross-check directly on bound vs C*sqrt(n logq) for many (n,q) incl. non-prize n
print("\n=== direct: log(2q^2)/y* <= (3/sqrt2)*sqrt(n logq) for many (n,q), q>=2, n>=1 ===")
viol = 0; total = 0
for n in [1,2,3,4,8,16,32,64,128,256,1000]:
    for q in [2,3,5,16,256,n**4 if n>=2 else 16, n**5 if n>=2 else 32, 10**6]:
        if q < 2: continue
        logq = math.log(q)
        ystar = math.sqrt(2*logq/n)
        lhs = math.log(2*q*q)/ystar
        rhs = C*math.sqrt(n*logq)
        total += 1
        if lhs > rhs + 1e-9:
            viol += 1
            print(f"  VIOL n={n} q={q} lhs={lhs:.4f} rhs={rhs:.4f}")
print(f"violations {viol}/{total}")
