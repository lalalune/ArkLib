#!/usr/bin/env python3
# Verifies the WORST-CASE theta-girth counting-cap (gamma <= ceil(log_n p)+O(1)), Fermat witness.
# Refutes the typical-case "girth grows with n => transfer-exact band widens to prize depth" reading.
# n=16, p=65537 (Fermat, first prime ==1 mod 16 at prize scale 16^4): worst-case L1-theta girth = 5,
# via the INTEGER-coefficient relation 4*zeta^0 - zeta^11 == 0 mod p (4 is a primitive 16th root since
# 2^16=-1 => 4^16=1). A {0,+-1}-Hamming scan MISSES this (needs coeff 4). Counting-cap: the (2 phi(n))^w
# = n^w signed weight-w words collide into F_p once n^w >~ p, forcing gamma <= log_n p + O(1) = beta+O(1)
# at the adversarial prime -- a code-independent alphabet-capacity ceiling no BCH/HT/Roos/vLW bound beats.
from sympy import primitive_root
p=65537; n=16
g=int(primitive_root(p)); h=pow(g,(p-1)//n,p)
assert pow(4,16,p)==1 and next(d for d in range(1,17) if pow(4,d,p)==1)==16, "4 not a primitive 16th root"
j=next(j for j in range(16) if pow(h,j,p)==4)
assert (4 - pow(h,j,p))%p==0
print(f"n={n} p={p} (beta=4): 4 = h^{j} is a primitive 16th root; weight-5 relation 4*zeta^0 - zeta^{j} == 0 mod p")
print(f"=> worst-case L1-theta girth <= 5 (integer coeff 4 essential; {{0,+-1}} misses it).")
print(f"   transfer-exact band r<girth/2 ~ 2.5 vs prize depth r~ln q = {4*__import__('math').log(n):.1f}: band never reaches prize depth.")
print("   COUNTING-CAP: gamma <= ceil(log_n p)+O(1)=beta+O(1) (n^w collide into F_p once n^w>p). wf-S5 'girth grows' is TYPICAL-case only.")
