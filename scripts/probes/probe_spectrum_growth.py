#!/usr/bin/env python3
# probe_spectrum_growth.py (#444, lane `spectgrowth`)
# OBJECT: the in-tree spectrumCount m r = sum_{k=r(2), k<=min(r,2m-r)} C(m,k)*2^k.
# QUESTION (sec VIII-C distinct-gamma growth law): is N_r = spectrumCount m r strictly
# increasing for 0<=r<=m (unimodal, peak at r=m, palindrome to 2m)? This is the SHAPE of
# the deep-band distinct-gamma count -- the decay-mechanism input. ONE sweep, thin tower.
from math import comb


def spectrumCount(m, r):
    s = 0
    hi = min(r, 2 * m - r)
    k = r % 2
    while k <= hi:
        s += comb(m, k) * (2 ** k)
        k += 2
    return s


allmono = True
allpeak = True
allpalin = True
for m in [4, 5, 6, 7, 8, 9, 10, 11, 12]:
    vals = [spectrumCount(m, r) for r in range(0, 2 * m + 1)]
    mono = all(vals[r] < vals[r + 1] for r in range(0, m))
    peak = (vals[m] == max(vals)) and all(vals[m] > vals[r] for r in range(0, m))
    palin = all(vals[r] == vals[2 * m - r] for r in range(0, 2 * m + 1))
    allmono &= mono
    allpeak &= peak
    allpalin &= palin
    ratio_mid = vals[m] / vals[m - 1] if vals[m - 1] else 0
    print("m=%2d  peak N_m=%8d  strict-up(0..m)=%s  peakUnique=%s  palindrome=%s  N_m/N_(m-1)=%.4f"
          % (m, vals[m], mono, peak, palin, ratio_mid))

print()
print("ALL m: strict-increasing 0..m = %s" % allmono)
print("ALL m: unique peak at r=m     = %s" % allpeak)
print("ALL m: palindrome r<->2m-r    = %s" % allpalin)
for m in [4, 8, 12]:
    nm = spectrumCount(m, m)
    print("m=%d: N_m=%d  3^m=%d  C(2m,m)=%d  N_m/3^m=%.4f"
          % (m, nm, 3 ** m, comb(2 * m, m), nm / 3 ** m))
