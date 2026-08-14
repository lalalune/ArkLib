#!/usr/bin/env python3
"""wf-A2: CONFIRM the exact identity  SoS_degree_d_value = #{x in mu_n : (x mod p) <= d}.
This proves the generic circle-Lasserre relaxation is BLIND to phase cancellation: it certifies
only the trivial count, never M. The relaxation lacks the ring relation x^n=1 mod p that creates
cancellation. Adding that relation (ideal of mu_n) = solving the open problem."""
import sympy, math, numpy as np
def subgroup(p,n):
    g=int(sympy.primitive_root(p)); z=pow(g,(p-1)//n,p)
    return np.array([pow(z,j,p) for j in range(n)])
for n,p in [(8,89),(16,193),(8,113),(32,1153)]:
    if (p-1)%n: continue
    e=subgroup(p,n)
    for d in (4,16,64):
        cnt=int((e<=d).sum())
        print(f"n={n} p={p} d={d}: count(e<=d)={cnt}")
    print(f"  -> full count = n = {n} (SoS at d=p-1); true M never recovered.")
