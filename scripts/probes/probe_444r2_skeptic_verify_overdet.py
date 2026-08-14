#!/usr/bin/env python3
"""
SKEPTIC RE-VERIFICATION of the round-2 finding "over-det far-line delta* is Johnson-locked (c*=k-1)".
Independent re-derivation summary (the heavy lifting is done by the EXACT Rust engines pg/crossdeep).

VERDICT: HOLDS, with one honest scope caveat.

WHAT WAS INDEPENDENTLY RE-RUN AND CONFIRMED (this verification session):
  * pg (full C(n,s) sweep, NO ceiling, authoritative):
      n=16 -> s*=7  c*=3=k-1  delta*=0.5625  (binding s=6 maxI=89 dir(10,4))
      n=20 -> s*=9  c*=4=k-1  delta*=0.5500  (binding s=8 maxI=121 dir(8,6))
      n=24 -> s*=11 c*=5=k-1  delta*=0.5417  (binding s=10 maxI=25 dir(13,8))
  * crossdeep ((k+1)-subset engine, validated against pg on n=16,20,24):
      n=28 -> s*=13 c*=6=k-1  delta*=0.5357  (gcd=2 binders {8,10,12} maxI=14<=28 at s=13;
                                              odd dirs maxI<=5; b=n/2=14 EXCLUDED as correlated)
  * p-INDEPENDENCE: n=24 re-run at a SECOND, non-Fermat prime p=995329 (pmult=3) -> identical
      s*=11, c*=5, s=10 OVER (maxI=25), s=11 boundary (maxI=24=budget). Also Fermat p=65537/331777.
  * EXACT trend: (delta* - 1/2)*n = 1.0000 for n=16,20,24,28 (NO hidden growth):
      delta* = (n - (2k-1))/n = (n/2+1)/n = 1/2 + 1/n  ->  1/2 = Johnson, since k=n/4.

ORBIT DECOMPOSITION (wf-D5) re-checked: I = z + (orbit_size)*O with orbit_size = n/gcd(a-b,n),
  z in {0,1}. n=16 dir(10,4) gcd=2: c2 I=89=1+8*11 (O=11), c3 I=9=1+8*1 (O=1) -> collapse at c=k-1.
  IMPORTANT CORRECTION to the lead's "always gcd=2 / I=z+(n/2)O" framing: the binding direction
  AT THE CROSSING is frequently gcd=1 (orbit size n), e.g. n=24 s=11 binding dir(21,8) gcd=1
  I=24=budget=n with a SINGLE size-n orbit (O=1,z=0); n=20 s=11 dir(11,10) gcd=1 I=20=n. The
  budget condition is the gcd-general (n/gcd)*O <= n  <=>  O <= gcd; higher-gcd dirs allow MORE
  orbits but none push s* past 2k-1. The crossing is governed by the WORST direction over all gcd
  classes, and that worst is exactly at budget=n at s=2k-1, dropping below at s=2k. The wf-D6 Lean
  arithmetic (I<=n iff O<=2 for the n/2 case) is the gcd=2 instance; the GENERAL crossing is
  (n/gcd)*O<=n, still pinned to s=2k-1 by the same Johnson list-collapse.

LEAN (re-compiled THIS session, axiom-clean):
  _wf3D6_overdet_johnson_lock.lean  -> 3 thms [propext, Quot.sound]   (budget-orbit Nat arithmetic)
  _wf3D5_lamleung_orbit_backbone.lean -> 3 thms [propext, Classical.choice, Quot.sound] (free-orbit
     divisibility |G| | |bad set|). NOTE: the Lean proves ARITHMETIC/DIVISIBILITY only; the
     load-bearing "O(c) = RS list size, collapses to <=2 at the Johnson radius 2k-1 (Johnson bound +
     Gur02/GS03 tightness)" is documented STRUCTURAL, NOT Lean-formalized (the docstrings say so).
  (The _wf3D6 file had been wiped by autosync mid-session — restored from /tmp backup; recompiled.)

THE ONE HONEST CAVEAT (scope, not error):
  n=32 is "PREDICTED" -- NOT exact-verified. Both pg (C(32,s) wall) and crossdeep (C(32,9)~28M
  divided-difference enumeration per direction) TIME OUT under available compute; this verification
  could not reach n=32 either. The earlier GPU "n=32 deviation" (delta*=0.5938) is plausibly a
  search-ceiling artifact (consistent internal logic: missed-deep-binders => false-small s* =>
  false-large delta*), but that remains a HYPOTHESIS, not an exact-engine confirmation. The lock
  is EXACT for n=16,20,24 (full sweep) and crossdeep-confirmed for n=28; the asymptotic
  delta*->1/2 rests on (a) the exact (delta*-1/2)*n=1 trend through n=28 and (b) the STRUCTURAL
  O(c)=list-size-collapses-at-Johnson argument, which is the Johnson list-decoding bound (a real,
  cited theorem) -- NOT enumeration and NOT a Lean theorem here.

NET: the finding HOLDS. It is correctly tagged REDUCE-TO-WALL: it REFUTES the over-determined-
far-line route as a path to the off-BGK floor (that route is Johnson-locked, delta*=1/2+o(1)),
leaving the prize open core untouched = the BGK char sum M(n). It does NOT close the prize and
does not claim to. Re-running with the committed engines reproduces every exact value.
"""
print(__doc__)
