from math import comb
# r EVEN (the actual s-step fold regime), 2r<s, r>=2:
# C(s/4, r/2) <= C(s/2, r) via C(a,k)<=C(2a,2k) with a=s/4,k=r/2 EXACTLY (2k=r since r even).
viol=0; checked=0; strict_viol=0
for mu in range(3,14):
    s=2**mu
    for r in range(2, s//2, 2):  # r even
        checked+=1
        if not (comb(s//4, r//2) <= comb(s//2, r)):
            viol+=1
        # full strict decay 2^{r/2} C(s/4,r/2) < 2^r C(s/2,r)
        if not (2**(r//2)*comb(s//4,r//2) < 2**r * comb(s//2,r)):
            strict_viol+=1
print(f"r-even: checked={checked}  C(s/4,r/2)<=C(s/2,r) viol={viol}  strict-decay viol={strict_viol}")
# also need: is 2*(s/4) = s/2 in Nat when s=2^mu? yes. and 2*(r/2)=r when r even. confirm s div:
for mu in [3,7,13]:
    s=2**mu
    assert 2*(s//4)==s//2
print("s/4 doubling == s/2: OK for powers of two")
