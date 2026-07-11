# probe_407_close_countlane_Gr_height_fast.py
#
# EXACT heights of the sumset polynomial  G_r(gamma) = prod_J (gamma - sigma_J)  over mu_s
# (s a power of 2), via fast integer convolution in R = Z[x]/(x^h+1), h=s/2 (zeta^h=-1).
# G_r is integer & monic, deg = |Sigma_r| = the bad-scalar count N_0.
# log2 height(G_r) is the candidate "single-integer D" height for the floor pigeonhole.
#
# RESULT (load-bearing): log2 height(G_r) is NOT O(n log n) -- at n=32,r=3 it is 301.66 >>
# n log n = 160, and grows with r (deg=|Sigma_r| ~ 2^{Theta(s)}). So G_r is the WRONG single
# integer for "#bad primes <= log2 D = O(n log n)".
from itertools import combinations
import math

def mulmod(a, b, h):
    res = [0]*(2*h)
    for i, ai in enumerate(a):
        if ai == 0: continue
        for j, bj in enumerate(b):
            if bj == 0: continue
            res[i+j] += ai*bj
    out = [0]*h
    for i in range(2*h):
        if res[i]:
            if i < h: out[i] += res[i]
            else:     out[i-h] -= res[i]
    return out

def powmod(a, t, h):
    res = [0]*h; res[0] = 1
    base = a[:]
    while t > 0:
        if t & 1: res = mulmod(res, base, h)
        base = mulmod(base, base, h)
        t >>= 1
    return res

def sigma_coord(J, s, h):
    v = [0]*h
    for j in J:
        j %= s
        if j < h: v[j] += 1
        else:     v[j-h] -= 1
    return v

def Gr_height(s, r):
    h = s//2
    sigmas = [sigma_coord(J, s, h) for J in combinations(range(s), r)]
    deg = len(sigmas)
    psums = []
    for t in range(1, deg+1):
        acc = [0]*h
        for sj in sigmas:
            pt = powmod(sj, t, h)
            for i in range(h): acc[i] += pt[i]
        psums.append(acc[0])
    e = [1]
    for k in range(1, deg+1):
        sm = 0
        for i in range(1, k+1):
            sm += (-1)**(i-1) * e[k-i] * psums[i-1]
        e.append(sm // k)
    height = max(abs(ek) for ek in e)
    return deg, height, (math.log2(height) if height > 1 else 0.0)

if __name__ == '__main__':
    for (lab, s, r) in [("mu_4 r=2",4,2),("mu_8 r=2",8,2),("mu_8 r=3",8,3),
                        ("mu_8 r=4",8,4),("mu_16 r=2",16,2),("mu_16 r=3",16,3)]:
        deg, ht, l2 = Gr_height(s, r)
        n = 2*s
        print(f"{lab}: deg=|Sigma_r|={deg}, log2 height={l2:.2f}  "
              f"(n=2s={n}, n log n={n*math.log2(n):.1f}, "
              f"(n/2)log2(n^2+n)={(n//2)*math.log2(n*n+n):.1f})")
    print("\n=> G_r height exceeds n log n at n=32 r=3 (301.66 >> 160); NOT a valid single-D.")
