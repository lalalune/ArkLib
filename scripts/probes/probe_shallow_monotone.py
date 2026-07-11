import math
# Claim: in prize regime q > n^2 + n, shallow_ceiling(n,q,r) is STRICTLY DECREASING in r,
# with infimum = n (at r->inf). So inf over r is n, never attained, bound > n for all finite r.
# ln shallow = ln n + (1/(r+1))*(1/2)*ln((q-n)/n^2);  (q-n)/n^2 > 1 in prize regime => term>0
print("Analytic: ln shallow = ln n + (1/(r+1))*(1/2)*ln((q-n)/n^2), (q-n)/n^2 > 1 in prize regime")
print("=> term > 0, decreasing in r, infimum = n. shallow(r) > n for ALL finite r when q-n>n^2.\n")
for (n, beta) in [(16, 4.0), (256, 5.0), (2**20, 4.0)]:
    q = n**beta
    C = 0.5 * math.log((q - n) / n**2)
    print("n=%d beta=%s: (q-n)/n^2=%.3e  C=%.3f>0? %s" % (n, beta, (q-n)/n**2, C, C > 0))
    prev = None
    for r in [0, 1, 2, 5, 20, 100, 1000]:
        direct = n**(1 - 1.0/(r+1)) * (q - n)**(1.0/(2*(r+1)))
        viaC = math.exp(math.log(n) + C/(r+1))
        mono = "" if prev is None else ("DEC" if direct < prev else "INC!!")
        print("   r=%-5d shallow=%.6e match=%s %s" % (r, direct, abs(direct-viaC) < 1e-6*direct, mono))
        prev = direct
