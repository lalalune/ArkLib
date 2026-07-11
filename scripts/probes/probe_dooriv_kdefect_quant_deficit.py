import math
import random

# Door-(iv) probe: GENERAL k-defect deficit lower bound.
# phaseSum = (M-k) + sum_{i in S} w_i, |S|=k, each w_i unit != 1.
# Conjecture: deficit = M - |phaseSum| >= (M-k) * sum_i (1 - Re w_i) / M,  for M >= k.
# Derivation idea (to formalize):
#   normSq = ((M-k)+sum cos_i)^2 + (sum sin_i)^2.
#   Re(phaseSum) = (M-k)+sum cos_i = M - (k - sum cos_i) = M - (sum d_i)   [d_i=1-cos_i]
#   So Re(phaseSum) = M - D, D = sum d_i.  |phaseSum| <= ... but we need a LOWER bound on deficit.
#   |phaseSum| <= sqrt(Re^2 + Im^2). Hmm we need |phaseSum| <= M - (M-k)D/M.
#   Use |z| <= M  and  |z| >= Re z = M - D when Re z >= 0. That gives deficit <= D, an UPPER bound.
#   For the LOWER bound on deficit we need |phaseSum| <= sqrt(M^2 - 2(M-k)D + ...). Probe to confirm
#   the (M-k)D/M floor empirically over random configs; derive the exact chord in Lean.

random.seed(1)
worst = 99.0
fails = 0
for M in [4, 6, 8, 16, 32, 64, 128, 256]:
    for k in range(1, min(M, 10) + 1):
        for _ in range(400):
            cosines = []
            sines = []
            for _ in range(k):
                th = random.uniform(0.0001, 2 * math.pi - 0.0001)
                cosines.append(math.cos(th))
                sines.append(math.sin(th))
            D = sum(1 - c for c in cosines)
            re = (M - k) + sum(cosines)
            im = sum(sines)
            norm = math.sqrt(re * re + im * im)
            deficit = M - norm
            lb = (M - k) * D / M
            if deficit + 1e-9 < lb:
                fails += 1
            elif lb > 1e-12:
                worst = min(worst, deficit / lb)

print("k-defect floor deficit >= (M-k)*sum(1-Re w_i)/M : fails =", fails,
      " tightness =", round(worst, 4))
