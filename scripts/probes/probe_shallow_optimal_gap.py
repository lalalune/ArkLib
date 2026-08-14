import math
# Unconditional shallow-tail ceiling: M(n) <= n^{1 - 1/(r+1)} * (q-n)^{1/(2(r+1))}
# Minimize over r >= 0. Compare to prize sqrt(n*ln(q/n)) and to trivial n.
def shallow_ceiling(n, q, r):
    return n**(1 - 1.0/(r+1)) * (q-n)**(1.0/(2*(r+1)))

def prize(n,q):
    return math.sqrt(n*math.log(q/n))

print(f"{'n':>8} {'beta':>5} {'q':>14} {'r*':>4} {'min_shallow':>14} {'prize':>10} {'trivial_n':>10} {'shallow/prize':>13} {'shallow/n':>9}")
fails_below_n = 0
for a in [4,6,8,12,16,20,24,30]:
    n = 2**a
    for beta in [4.0,4.5,5.0]:
        q = n**beta
        # find optimal r over a wide range
        best=None; bestr=None
        for r in range(0, 200):
            v = shallow_ceiling(n,q,r)
            if best is None or v<best:
                best=v; bestr=r
        pr = prize(n,q)
        print(f"{n:>8} {beta:>5} {q:>14.3e} {bestr:>4} {best:>14.4e} {pr:>10.3e} {n:>10} {best/pr:>13.3e} {best/n:>9.4f}")
        if best < n*0.999:
            fails_below_n += 1
print()
print(f"cases where optimal unconditional shallow ceiling beats trivial n (by >0.1%): {fails_below_n}")
# Also: what's the optimal r as a function? and shallow/sqrt(n) ratio
print()
print("optimal r* vs n (beta=4): is r* growing? and min_shallow / sqrt(n):")
for a in [4,8,12,16,20,24,30]:
    n=2**a; q=n**4.0
    best=None;bestr=None
    for r in range(0,400):
        v=shallow_ceiling(n,q,r)
        if best is None or v<best: best=v;bestr=r
    print(f"  n=2^{a:<2} r*={bestr:<4} min={best:.4e} min/sqrt(n)={best/math.sqrt(n):.3f} min/n={best/n:.4f}")
