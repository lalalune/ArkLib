import math

# Door-(iv) probe: TWO-defect deficit lower bound.
# phaseSum = (M-2) + w1 + w2, w1,w2 unit, != 1.
# Re(phaseSum) = (M-2) + cos1 + cos2, Im = sin1 + sin2.
# Let d1 = 1-cos1, d2 = 1-cos2 in (0,2].
# normSq = ((M-2)+cos1+cos2)^2 + (sin1+sin2)^2.
# Candidate floors to test for deficit = M - |phaseSum|:
#   (A)  >= (M-2)(d1+d2)/M
#   (B)  >= ((M-1)d1 + (M-1)d2)/(2M)? etc.
# We hunt the cleanest TRUE additive-in-defect floor.

steps = 240
worstA = 99.0
failA = 0
worstReM = 99.0
for M in [3, 4, 5, 8, 16, 32, 64, 128]:
    for a in range(1, steps):
        for b in range(1, steps, 7):
            t1 = 2.0 * math.pi * a / steps
            t2 = 2.0 * math.pi * b / steps
            c1, s1 = math.cos(t1), math.sin(t1)
            c2, s2 = math.cos(t2), math.sin(t2)
            d1, d2 = 1 - c1, 1 - c2
            re = (M - 2) + c1 + c2
            im = s1 + s2
            norm = math.sqrt(re * re + im * im)
            deficit = M - norm
            lbA = (M - 2) * (d1 + d2) / M
            if deficit + 1e-9 < lbA:
                failA += 1
            elif lbA > 1e-12:
                worstA = min(worstA, deficit / lbA)

print("two-defect candidate (A) deficit >= (M-2)(d1+d2)/M : fails =", failA,
      " tightness =", round(worstA, 4))
