from math import comb
from itertools import combinations_with_replacement as cwr

def chooseCH(s, r):
    return comb(s + r - 1, r) if s + r - 1 >= 0 else 0

fails = 0
checks = 0
for s in range(0, 12):
    for r in range(0, 10):
        ms = len(list(cwr(range(s), r)))
        ch = chooseCH(s, r)
        checks += 1
        if ms != ch:
            fails += 1
            print("FAIL s=%d r=%d: multisets=%d chooseCH=%d" % (s, r, ms, ch))
print("chooseCH(s,r) == #multisets(size r over s): %d fails / %d checks" % (fails, checks))
print("concrete: chooseCH(8,3)=%d  C(8,3)=%d" % (chooseCH(8,3), comb(8,3)))

# dominance C(s,r) <= chooseCH(s,r)
dfail = 0
for s in range(0, 20):
    for r in range(0, 20):
        if comb(s, r) > chooseCH(s, r):
            dfail += 1
print("dominance C(s,r) <= chooseCH(s,r): %d fails" % dfail)
