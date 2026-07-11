#!/usr/bin/env python3
"""
Probe: when is the swap floor SHARP, i.e. rEnergy(G,r) = 2|G|^r - |G|^{r-1} exactly?
For r=2, E_2(G) = 2n^2 - n  <=>  G is a SIDON set (B_2: all pairwise sums a+b, a<=b, distinct
except forced). This is the well-known characterization. Question: does the swap floor stay
sharp at higher r for Sidon sets, or does r>=3 acquire genuine excess even for Sidon G?

(If r=2 sharpness <=> Sidon is the ONLY clean equality, that's the brick: rEnergy G 2 =
2n^2-n <=> Sidon. The r>=3 floor is NOT sharp for Sidon, because B_2 controls only PAIR sums.)

We test on:
 - Sidon sets (e.g. {1,2,5,11,22,33,...} Mian-Chowla; perfect difference sets)
 - generic / arithmetic-progression (NOT Sidon) sets
"""
import itertools
from collections import Counter

def rEnergy(G, r):
    cnt = Counter()
    for v in itertools.product(G, repeat=r):
        cnt[sum(v)] += 1
    return sum(c*c for c in cnt.values())

def is_sidon(G):
    sums = {}
    for a in G:
        for b in G:
            s = a+b
            sums.setdefault(s, 0)
            sums[s]+=1
    # additive energy E2 = sum c^2; Sidon iff E2 = 2n^2 - n
    n=len(G)
    e2 = sum(c*c for c in sums.values())
    return e2 == 2*n*n - n

# Mian-Chowla Sidon sequence
def mian_chowla(k):
    seq=[1]; sums={2}
    c=2
    while len(seq)<k:
        ok=True
        for a in seq:
            if a+c in sums:
                ok=False; break
        if ok:
            for a in seq+[c]:
                sums.add(a+c)
            seq.append(c)
        c+=1
    return seq

if __name__ == "__main__":
    print("=== Sidon sets (Mian-Chowla): is swap floor sharp at each r? ===")
    for n in [2,3,4,5]:
        G = mian_chowla(n)
        assert is_sidon(G), G
        print(f" Sidon G(n={n})={G}")
        for r in [2,3,4]:
            re = rEnergy(G,r)
            fl = 2*n**r - n**(r-1)
            print(f"   r={r}: rEnergy={re}, swapFloor={fl}, SHARP={re==fl}")
    print()
    print("=== r=2: rEnergy G 2 == 2n^2-n  <=>  Sidon  (verify both directions) ===")
    import random
    for _ in range(8):
        n = random.randint(2,5)
        G = random.sample(range(0,40), n)
        re2 = rEnergy(G,2); fl2 = 2*n*n-n
        print(f"  G={sorted(G)}: E2={re2}, 2n^2-n={fl2}, eq={re2==fl2}, isSidon={is_sidon(G)}, MATCH={(re2==fl2)==is_sidon(G)}")
