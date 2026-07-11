import math
import random

# Establish the kernel-provable intermediate: normSq(phaseSum) <= M^2 - 2(M-k)D ?
# where D = sum d_i, d_i = 1 - cos_i.  If true, then
#   |phaseSum| <= sqrt(M^2 - 2(M-k)D) <= M - (M-k)D/M  (concavity chord, M>=k so RHS>=0 when D small)
# giving the floor. Probe the normSq inequality + the per-term decomposition.
#
# normSq = (M-D)^2 + (sum sin_i)^2
#        = M^2 - 2MD + D^2 + (sum sin_i)^2.
# Want <= M^2 - 2(M-k)D, i.e.  D^2 + (sum sin)^2 <= 2MD - 2(M-k)D = 2kD.
# i.e.  D^2 + (sum sin_i)^2 <= 2kD.
# Since D = sum d_i and per term d_i in [0,2], sin_i^2 = 1-(1-d_i)^2 = 2d_i - d_i^2.
# (sum sin_i)^2 <= k * sum sin_i^2  (Cauchy-Schwarz) = k*(2D - sum d_i^2) = 2kD - k*sum d_i^2.
# D^2 = (sum d_i)^2 <= k * sum d_i^2 (Cauchy-Schwarz).
# So D^2 + (sum sin)^2 <= k*sum d_i^2 + 2kD - k*sum d_i^2 = 2kD.  EXACT chain. 

random.seed(2)
fail_ns = 0
fail_cs1 = 0
fail_cs2 = 0
for M in [4, 8, 16, 64, 256]:
    for k in range(1, min(M, 8) + 1):
        for _ in range(300):
            ds = []
            sins = []
            for _ in range(k):
                th = random.uniform(0.0001, 2 * math.pi - 0.0001)
                ds.append(1 - math.cos(th))
                sins.append(math.sin(th))
            D = sum(ds)
            re = M - D
            im = sum(sins)
            normSq = re * re + im * im
            if normSq > M * M - 2 * (M - k) * D + 1e-7:
                fail_ns += 1
            # CS check 1: (sum sin)^2 <= k sum sin^2
            if im * im > k * sum(s * s for s in sins) + 1e-7:
                fail_cs1 += 1
            # CS check 2: D^2 <= k sum d^2
            if D * D > k * sum(d * d for d in ds) + 1e-7:
                fail_cs2 += 1

print("normSq <= M^2 - 2(M-k)D fails =", fail_ns)
print("(sum sin)^2 <= k*sum sin^2 fails =", fail_cs1)
print("D^2 <= k*sum d^2 fails =", fail_cs2)
