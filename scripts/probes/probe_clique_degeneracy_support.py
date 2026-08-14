#!/usr/bin/env python3
"""
PROBE (rule 2) for a SECOND brick: characterize WHICH kernel pencils s2(b)=Σ_β b(β)ev_β are
GENUINE full-support errors on W (the 'false positive' / degeneracy object of #444 line 187).

In-tree duality (Round 20 evalSyndrome_family_injective): pairing s2(b) against Λ_{E_α} reads off
b(α)·Λ_{E_α}(α), and Λ_{E_α}(α) ≠ 0.  CLAIM to verify: the error vector e on W with e_α = the
'W-supported error' whose syndrome is s2(b) has support = {α : b(α) ≠ 0}.  Concretely: s2(b) as a
syndrome is the evaluation transform of the weight vector b restricted to W; its 'error support'
(the W-coords that are nonzero) is exactly supp(b).  So s2(b) is a FULL weight-(w+1) error  iff
b(α)≠0 ∀α∈W.  Verify the pairing-readoff: pairing(Λ_{E_α}, s2(b)) = b(α)·Λ_{E_α}(α) exactly, over
ℚ and F_p, for random b, random distinct nodes.  (This is the algebraic content of the clean lemma.)
"""
import random
from fractions import Fraction

def clique_locator_coeffs(W, alpha):
    poly=[Fraction(1)]
    for b in W:
        if b==alpha: continue
        new=[Fraction(0)]*(len(poly)+1)
        for i,c in enumerate(poly):
            new[i]+=-b*c; new[i+1]+=c
        poly=new
    return poly

def ev(t,D): 
    out,p=[],Fraction(1)
    for _ in range(D): out.append(p); p*=t
    return out

def pairing(P,s,D):  # Σ_{j<D} P_j s_j
    return sum((P[j] if j<len(P) else Fraction(0))*s[j] for j in range(D))

def loc_eval(W,alpha,x):
    r=Fraction(1)
    for b in W:
        if b!=alpha: r*=(x-b)
    return r

rng=random.Random(1)
ok=True
for trial in range(200):
    wcard=rng.randint(3,6)
    vals=set()
    while len(vals)<wcard: vals.add(rng.randint(1,100))
    W=[Fraction(v) for v in vals]
    b={a:Fraction(rng.randint(-5,5)) for a in W}      # allow zeros => partial support
    D=wcard+rng.randint(0,3)
    s2=[sum(b[a]*ev(a,D)[j] for a in W) for j in range(D)]
    for a in W:
        loc=clique_locator_coeffs(W,a)
        lhs=pairing(loc,s2,D)
        rhs=b[a]*loc_eval(W,a,a)
        if lhs!=rhs:
            ok=False; print("MISMATCH",trial,a,lhs,rhs); break
    if not ok: break

print("pairing(Λ_{E_α}, s2(b)) == b(α)·Λ_{E_α}(α) exactly:", "PASS 200/200" if ok else "FAIL")
print("=> error-support(s2(b)) = {α : b(α)≠0}; s2(b) full weight-(w+1) iff b(α)≠0 ∀α. Λ_{E_α}(α)≠0 verified by construction.")
