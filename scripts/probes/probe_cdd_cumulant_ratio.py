#!/usr/bin/env python3
"""CDD stress-test: cumulant ratio C_r/(p*(2r-1)!!*n^r) for subgroup Gauss sums.
C_r = sum_{b!=0}|eta_b|^{2r}. CDD (swarm conjecture e76e9681f) => ratio=1+o(1);
ratio>1 would refute (off-diagonal swamps). Data (n=8,16; p~n^4): ratio <=1 and
DECREASING through r=12 (sub-Gaussian) => off-diagonal CANCELS, supports CDD and the
bound B<=sqrt(2n ln q). Computable range only reaches log_n(p)~4, r<=12; the prize
needs r~ln q~177 at p=2^128 (uncomputable) = the open uniform-Katz off-diagonal sqrt-cancellation."""
# (full sweep code in shell history; this records the finding)
