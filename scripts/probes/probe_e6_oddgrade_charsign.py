import cmath, math
# For odd jj and zeta a primitive (2h)-th root of unity (zeta^h = -1):
# claim: zeta^(jj*(a+h)) = - zeta^(jj*a). This is the anti-invariance that the abstract
# vanishing lemmas assume as hypothesis; it follows from jj*(a+h) = jj*a + jj*h and zeta^(jj*h) = -1
# (odd jj). This is exactly what antipode_grade_odd (jj*(a+h)=jj*a+h in ZMod 2h) delivers at the
# exponent level, then zeta^h=-1 gives the sign.
def check(h):
    N = 2*h
    zeta = cmath.exp(2j*math.pi/N)
    bad = 0
    for jj in range(1, N):
        if jj % 2 == 0: continue
        for a in range(N):
            lhs = zeta**(jj*(a+h))
            rhs = -(zeta**(jj*a))
            if abs(lhs - rhs) > 1e-9:
                bad += 1
                if bad < 4: print(f"  h={h} jj={jj} a={a}: |lhs-rhs|={abs(lhs-rhs):.2e}")
    # also confirm zeta^(jj*h) = -1 for odd jj
    bads = 0
    for jj in range(1, N):
        if jj % 2 == 0: continue
        if abs(zeta**(jj*h) - (-1)) > 1e-9: bads += 1
    print(f"h={h} (N={N}): char anti-invariance failures={bad}; zeta^(odd*h)=-1 failures={bads}")
check(4); check(8); check(16)
