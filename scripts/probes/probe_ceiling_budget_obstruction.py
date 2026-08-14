# probe_ceiling_budget_obstruction.py (#334/#444) — the s=128 ceiling at the FIXED prize point.
# FINDING (2026-06-21, independent arithmetic): at q=n*2^128=2^158, n=2^30, the KKH26 bad-prime
# union-bound budget (#pairs * log(s^{s/2})/log q vs good-prime supply q/(phi(n) log q)) gives:
#   s=32: q>s^{s/2}=2^80 => Dirichlet super-poly route (closed).
#   s=64,128: q<s^{s/2} => budget route. s=128: rho=1/16 (r=9) budget 2^89 << supply 2^122 (CLOSEABLE);
#   rho=1/8 (r=17) 2^136 and rho=1/4 (r=33) 2^189 EXCEED supply 2^122 (budget FAILS).
# KEY: the obstruction is the COLLISION-PAIR count #pairs~(2^r C(64,r))^2~2^188, NOT the prime supply.
# So Linnik/Xylouris (abundant supply) does NOT close high-rate s=128; need a better bound on #DISTINCT
# bad primes (resultants must share factors / be smooth). Sharper than the dossier's "s=128 needs TZ24".
from math import log2, log, comb
n=2**30; q=n*2**128
for mu in (5,6,7):
    s=2**mu; lr=mu*(s//2)
    print(f"s={s}: log2(s^s/2)={lr}, q=2^{log2(q):.0f}, route={'Dirichlet' if log2(q)>lr else 'budget'}")
good=log2(q)-29-log2(log(q))
for rho,r in [(1/16,9),(1/8,17),(1/4,33)]:
    pl=2*(r+log2(comb(64,r))); bl=pl+log2((7*64)/log2(q))
    print(f"  s=128 rho={rho}: log2(bad budget)~{bl:.0f} vs good 2^{good:.0f} -> {'CLOSEABLE' if bl<good else 'budget FAILS (#pairs explosion)'}")
