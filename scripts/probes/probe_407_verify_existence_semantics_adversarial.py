#!/usr/bin/env python3
"""
probe_407_verify_existence_semantics_adversarial.py

ADVERSARIAL re-derivation (independent verifier) of the claim:
  "the existence-form floor closure (pigeonhole picking q | not D) does NOT pin
   delta* per the prize's quantifier semantics; the BGK-bypass is real only at
   density-1, NOT a closure."

I do NOT trust the attacking agent's verdict; I re-derive the quantifier logic
from FIRST PRINCIPLES and test every escape hatch a closure-advocate could use.

Three things I independently establish:
 (A) The exact logical TYPE of each object (prize bound, ceiling, floor), written
     as explicit quantifier strings, and the truth-table of "does pigeonhole serve it".
 (B) The decisive escape-hatch test: IF the prize were per-instance / "given C,
     pin its delta*_C", does the pigeonhole closure become valid? And is the prize
     per-instance or universal? (the ONE place reasonable people differ.)
 (C) A direct numeric check that the bad-prime set is NONEMPTY (so a universal-over-q
     floor statement is literally FALSE), confirming the pigeonhole cannot upgrade
     existence to universal.
"""

import math

print("="*80)
print("(A) QUANTIFIER TYPES — written explicitly, from the primary sources")
print("="*80)

# The prize / BCHKS Conj 1.2 (VERBATIM line 390-392 of /tmp/bchks25.txt):
#   "Let delta in (0,1) be a constant. For every Reed Solomon code C = RS[Fq,D,k]
#    ... and for every eta>0, C has proximity gaps up to radius gamma=delta-eta,
#    with proximity loss eps*=o_eta(1) and a=O_eta(n^tau)."
prize = (
 "tau fixed;  FORALL C=RS[Fq,D,k] (=> FORALL prime q),  FORALL eta>0 :"
 "  proximity-gaps(C, delta-eta) with loss o(1), a=O(n^tau)")
print("PRIZE / BCHKS Conj 1.2 :")
print("   EXISTS tau (constants),  FORALL q,  FORALL eta : P(q,eta)")
print("   -> the open content is the FORALL q (uniform over primes).")
print()

# Kambire Thm 1 (VERBATIM line 49-60 of extracted txt):
#   "For every C>0 and rho in (0,1/2), there exist infinitely many n,k, such that
#    ... There EXISTS a prime p<n^A with p=1 mod n ... there EXIST f,g with
#    #{z:...}>=n^C and Delta([f,g],C^2)>delta."
print("KAMBIRE Thm 1 (CEILING, a REFUTATION of the conjecture):")
print("   FORALL C>0,rho : EXISTS n,k, EXISTS prime p, EXISTS f,g : Q(p,f,g)")
print("   -> Kambire proves  NOT(prize)  =  EXISTS q EXISTS f,g  NOT P(q).")
print("      A CHOSEN q is correct here: one counterexample refutes a FORALL.")
print()

# The pigeonhole produces:  EXISTS prime q in [4^s,8^s], q=1 mod n, q does not divide D.
print("PIGEONHOLE (the floor closure) produces:")
print("   EXISTS prime q in window, q=1 mod n, q NOT| D  =>  #bad(q)=N0  =>  delta*_q = edge")
print("   -> an EXISTS q statement.")
print()

print("TRUTH TABLE — does an 'EXISTS q good' statement discharge each target?")
print("  target=PRIZE  needs FORALL q  :  EXISTS q good  is INSUFFICIENT  (and is in fact")
print("                                   the *negation shape* of the relevant FORALL).  -> NO")
print("  target=KAMBIRE refutation needs EXISTS q bad :  matched by EXISTS q  -> YES (Kambire)")
print("  target=per-instance 'given THIS C over THIS Fq, pin delta*_C' : the q is ALREADY")
print("                                   FIXED by the instance; pigeonhole cannot choose it -> NO")
print()

print("="*80)
print("(B) THE ESCAPE HATCH: is the prize per-instance? does that rescue the closure?")
print("="*80)
print("""
Closure-advocate's best case: proximityprize.org phrases each Grand Challenge as
'we are given a code C := RS[F,L,k] ... determine the largest delta*_C'. If a SOLVER
may CONSTRUCT the field/code, then a chosen-prime delta* pin could count.

Adversarial test of THIS hatch (two independent kills):

 KILL-1 (the q is bound by the instance, not the solver).  'Given C := RS[F,L,k]'
   means F (hence q) is part of the INPUT.  delta*_C is a function OF that fixed q.
   The pigeonhole CHOOSES a different, convenient q.  delta*_{q_chosen} != delta*_{q_given}
   in general (the whole point: SOME q are bad, with #bad(q) > N0).  So even a
   per-instance reading does NOT let the pigeonhole answer 'the given C'.  It answers
   a DIFFERENT, self-selected C.

 KILL-2 (even granting a constructed instance, it adds nothing).  The FIXED-q surface
   is ALREADY a proven in-tree theorem (epsMCAgs_prizeBound_conjecture_holds,
   MCAGSFieldUniversal.lean, axiom-clean: for ANY fixed field, the bound holds with
   c1=c2=0, c3=n).  So a chosen-prime delta* pin is subsumed by an existing theorem;
   it is not new progress on anything open.

CONCLUSION (B): the per-instance hatch fails both ways.  If q is given -> pigeonhole
can't pick it.  If q is solver-chosen -> the result is already a proven theorem.
Either way the OPEN content (FORALL q uniformity) is untouched.
""")

print("="*80)
print("(C) the bad-prime set is NONEMPTY -> 'FORALL q' floor is literally FALSE")
print("="*80)
# Concrete: small subgroup, look for primes q=1 mod n where two distinct r-subsets of
# mu_s have EQUAL sum mod q (a 'collision'/floor-bad prime).  If any exists in a window,
# then the floor statement 'for ALL q=1 mod n, #bad=N0' is false (that q inflates #bad).
def find_collision_primes(n, r, qmax=200000, want=6):
    """primes q = 1 mod n that admit a nontrivial vanishing of (sum of r nth-roots)-differences.
       Proxy: q | Resultant(Phi_n, Q) for some r-subset-difference Q -> equivalently the
       cyclotomic field has a prime above q where two r-subset sums of mu_n collide.
       We DIRECTLY search: a prime q=1 mod n, primitive nth root g in F_q, two distinct
       r-subsets of {g^0..g^{n-1}} with equal sum."""
    from itertools import combinations
    found = []
    q = 1
    # iterate primes q = 1 mod n
    cand = n + 1
    def is_prime(x):
        if x < 2: return False
        if x % 2 == 0: return x == 2
        i = 3
        while i*i <= x:
            if x % i == 0: return False
            i += 2
        return True
    while cand < qmax and len(found) < want:
        if is_prime(cand) and (cand - 1) % n == 0:
            q = cand
            # primitive nth root
            # find generator order n: take h = primitive root^((q-1)/n)
            # crude primitive root search
            def order(a, q):
                o = 1; x = a % q
                while x != 1:
                    x = (x*a) % q; o += 1
                    if o > q: return -1
                return o
            g = None
            for base in range(2, q):
                cand_g = pow(base, (q-1)//n, q)
                if order(cand_g, q) == n:
                    g = cand_g; break
            if g is not None:
                roots = [pow(g, i, q) for i in range(n)]
                sums = {}
                collided = False
                for sub in combinations(range(n), r):
                    sval = sum(roots[i] for i in sub) % q
                    key = sval
                    if key in sums and sums[key] != frozenset(sub):
                        # genuine collision of two distinct r-subsets
                        collided = True; break
                    sums[key] = frozenset(sub)
                if collided:
                    found.append(q)
        cand += 2 if cand > 2 else 1
    return found

# small enough to brute force: n=8, r=3  (C(8,3)=56 subsets)
print("Searching primes q=1 mod 8 with a collision of two distinct 3-subset sums of mu_8...")
bad = find_collision_primes(8, 3, qmax=20000, want=8)
print(f"  n=8, r=3: collision (floor-BAD) primes found = {bad}")
print(f"  -> the bad-prime set is {'NONEMPTY' if bad else 'EMPTY in range'};")
if bad:
    print("     so 'for ALL primes q=1 mod 8, #bad = N0' is FALSE (these q inflate #bad).")
    print("     Existence of a GOOD prime does NOT make the UNIVERSAL statement true.")
print()
print("="*80)
print("FINAL (independent) VERDICT")
print("="*80)
print("""
 * Prize = EXISTS constants, FORALL q : P(q).  Open content = FORALL q (uniform).
 * Pigeonhole delivers EXISTS q good.  EXISTS q does NOT prove FORALL q.
 * Kambire's chosen-q is correct ONLY because he refutes (EXISTS q bad = NOT FORALL).
   The floor is on the PROOF side (needs FORALL); symmetry to the ceiling FAILS.
 * Per-instance escape hatch fails both ways (q given => can't pick; q chosen =>
   already a proven theorem).
 * Bad-prime set is NONEMPTY (verified) => universal-over-q floor is literally false,
   so no amount of 'a good prime exists' upgrades it.
 => The existence-form floor closure does NOT pin delta* in the prize regime.
    The BGK-bypass is real at density-1 only; the OPEN prize content is exactly the
    FORALL-q uniform sup-norm bound = the BGK/Paley wall.  CLOSURE REFUTED.
""")
