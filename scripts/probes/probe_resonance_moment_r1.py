import cmath, math, random
# phaseSum u 1 c = sum over X: Fin1->ZMod m with X0!=0 and X0=c of u(X0)
#   = u(c) if c!=0 else 0
# resonanceMoment u 1 = sum_c |phaseSum u 1 c|^2 = sum_{c!=0} |u(c)|^2
# For UNIT-phase u (|u(l)|=1): T_1 = (m-1)  (independent of u(0))
def phaseSum1(u, m, c):
    tot = 0+0j
    for x in range(m):
        if x != 0 and (x % m) == (c % m):
            tot += u[x]
    return tot
def T1(u, m):
    return sum(abs(phaseSum1(u, m, c))**2 for c in range(m))

ok = True
for m in [3, 5, 7, 15, 17, 31, 63, 127, 255]:
    u = [cmath.exp(2j*math.pi*random.random()) for _ in range(m)]
    t1 = T1(u, m)
    exp = m - 1
    pcheck = all(abs(phaseSum1(u, m, c) - (u[c] if c != 0 else 0)) < 1e-9 for c in range(m))
    good = abs(t1 - exp) < 1e-9 and pcheck
    print("m=%4d: T_1=%.6f expected=%d phaseSumOK=%s %s" % (m, t1, exp, pcheck, "PASS" if good else "FAIL"))
    ok = ok and good
print("\nALL PASS" if ok else "\nSOME FAIL")
