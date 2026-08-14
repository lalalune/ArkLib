from math import comb

def chooseCH(s, r):
    return comb(s + r - 1, r) if s + r - 1 >= 0 else 0

# Conjecture: for s>=2 and r>=1, C(s,r) < chooseCH(s,r) = C(s+r-1,r)?
# Note C(s,r)=0 when r>s, while chooseCH(s,r)>0 always (s>=1). So strict holds trivially there.
# Real content: r in [1..s], s>=2.
fail_strict = 0
checks = 0
boundary = []
for s in range(2, 40):
    for r in range(1, s + 1):
        a = comb(s, r)
        b = chooseCH(s, r)
        checks += 1
        if not (a < b):
            fail_strict += 1
            boundary.append((s, r, a, b))
print("strict C(s,r) < chooseCH(s,r) for s>=2,1<=r<=s: %d fails / %d" % (fail_strict, checks))
if boundary:
    print("  boundary cases where NOT strict:", boundary[:10])

# Also check r=1 edge: C(s,1)=s, chooseCH(s,1)=s -> EQUAL, not strict!
print("r=1 check: C(5,1)=%d chooseCH(5,1)=%d (equal => strict needs r>=2)" % (comb(5,1), chooseCH(5,1)))

# refine: for s>=1, r>=2: strict?
fail2 = 0; checks2 = 0
for s in range(1, 40):
    for r in range(2, 2*s + 3):
        a = comb(s, r); b = chooseCH(s, r)
        checks2 += 1
        if not (a < b):
            fail2 += 1
            if fail2 <= 12:
                print("  NOTstrict s=%d r=%d: C=%d CH=%d" % (s, r, a, b))
print("strict for s>=1, r>=2 (all r): %d fails / %d" % (fail2, checks2))
