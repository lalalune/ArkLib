import cmath, math, random
# Companion to the EXISTING anti-invariant theorem (sum_eq_zero_of_antiInvariant).
# That one: f(sigma x) = -f(x), weight anti-invariant => sum f = 0.
# NEW dual: the ROOTS antipodally negate: root(sigma x) = -root(x).
# So for ANY weight c that is INVARIANT under sigma (c(sigma x)=c(x)),
#   sum_{x in T} c(x)*root(x) = 0,
# because c(x)root(x) + c(sigma x)root(sigma x) = c(x)root(x) - c(x)root(x) = 0.
# This is the kernel of the weighted character-sum map restricted to invariant weights.
for k in range(1,7):
    n = 2**(k+1)
    zeta = cmath.exp(2j*math.pi/n)
    roots = [zeta**a for a in range(n)]
    half = 2**k
    assert abs(roots[half] - (-1)) < 1e-9
    # antipodal involution on exponents a -> a+half mod n; root(a+half) = -root(a)
    for a in range(n):
        assert abs(roots[(a+half)%n] - (-roots[a])) < 1e-9
    # invariant-weight signed sum vanishes
    for _ in range(300):
        c={}
        for a in range(n):
            b=(a+half)%n
            if a not in c:
                v=random.randint(-7,7); c[a]=v; c[b]=v   # invariant: c(a)=c(a+half)
        s=sum(c[a]*roots[a] for a in range(n))
        assert abs(s)<1e-7, (k,s)
    print(f"k={k} n={n}: root(sigma x)=-root(x) OK; invariant-weight weighted sum=0 (300 random) OK")
print("ALL PASS: invariant-weight antipodal kernel confirmed (dual of anti-invariant)")
