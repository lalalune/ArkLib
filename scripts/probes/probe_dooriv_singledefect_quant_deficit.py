import math

# Door-(iv) probe: quantitative single-defect deficit.
# phaseSum = (M-1) + w, w = exp(i*theta) unimodular, w != 1.
# With d = 1 - cos(theta) = 1 - Re w in (0,2]:
#   |phaseSum|^2 = (M-1)^2 + 2(M-1)cos(theta) + 1 = M^2 - 2(M-1)d.
# Candidate kernel-clean lower bound on deficit M - |phaseSum|:
#   sqrt(M^2 - t) <= M - t/(2M)  =>  deficit >= t/(2M) = (M-1)d/M.

worst = 99.0
steps = 4000
for M in [2, 3, 5, 8, 16, 32, 64, 128, 256]:
    for k in range(1, steps):
        theta = 2.0 * math.pi * k / steps
        c = math.cos(theta)
        s = math.sin(theta)
        if abs(c - 1.0) < 1e-9 and abs(s) < 1e-9:
            continue
        d = 1.0 - c
        re = (M - 1) + c
        im = s
        norm = math.sqrt(re * re + im * im)
        deficit = M - norm
        # identity check
        assert abs((re * re + im * im) - (M * M - 2 * (M - 1) * d)) < 1e-7, M
        lb = (M - 1) * d / M
        assert deficit + 1e-9 >= lb, (M, theta, deficit, lb)
        if lb > 1e-12:
            worst = min(worst, deficit / lb)

print("normSq identity M^2 - 2(M-1)(1-cos)  HOLDS")
print("LB  deficit >= (M-1)(1-Re w)/M  HOLDS over M up to 256")
print("tightness min(deficit/lb) =", round(worst, 4))
