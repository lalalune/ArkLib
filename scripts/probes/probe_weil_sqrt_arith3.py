#!/usr/bin/env python3
# Tight abstract check: M=sqrt q gives q < (M+1)^2 = M^2+2M+1, so q <= M^2+2M, a:=q-1 <= M^2+2M-1.
# Does (a//2)*d + a <= (d+2)*M^2 hold at worst a = M^2+2M-1 (M>=1), all d>=1?
fails = []
for M in range(1, 401):
    S = M * M
    a = S + 2 * M - 1           # = q-1 worst when q = M^2+2M (largest q with isqrt=M minus... q<= M^2+2M)
    for d in range(1, 80):
        lhs = (a // 2) * d + a
        if lhs > (d + 2) * S:
            fails.append((M, a, d, lhs, (d + 2) * S))
print("(a//2)*d + a <= (d+2)*M^2  at a=M^2+2M-1, M in [1,400], d<80:",
      len(fails) == 0, "| fails:", fails[:5])
# slack at the tightest corner:
mn = 10**18; arg = None
for M in range(1, 401):
    S = M * M; a = S + 2*M - 1
    for d in range(1, 80):
        sl = (d+2)*S - ((a//2)*d + a)
        if sl < mn: mn = sl; arg = (M, a, d)
print("min slack:", mn, "at (M,a,d)=", arg)
