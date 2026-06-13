# Is there a STRUCTURAL reason for the factor 1/2 (=> #bad <= K/2)?
# K = 2^r C(n/2,r) counts antipodal-free r-subsets = choose r antipodal classes, assign a sign each.
# The e1-spectrum has the symmetry: e1(-S) = -e1(S) (negate every element). On mu_n, -1 = zeta^{n/2} in mu_n,
# so S -> -S = zeta^{n/2}*S is a bijection of (r+1)-subsets preserving the deficit-2 band (line through -S),
# and e1(-S) = -e1(S). So bad gammas come in +/- PAIRS (unless e1=0). => #bad <= 2*(#{distinct |e1|}) but
# that's the WRONG direction. The pairing means #bad is roughly even, with a +1 for the e1=0 fiber.
# Check parity of ladder: 97(odd),145(odd),89(odd),113(odd),225(odd),104(EVEN).
print("ladder parity:", [(r,v,'odd' if v%2 else 'even') for r,v in zip(range(3,9),[97,145,89,113,225,104])])
# odd for r=3..7 (=> e1=0 IS achieved, contributing the unpaired +1), even at r=8 (=> e1=0 NOT achieved at central).
# So #bad = 2*M + [0 or 1]. This explains the '+1' in r=3 closed form n*C(n/4,2)+1 (even part 96=2*48, +1).
# The factor-1/2 vs K: K counts SIGNED configs; bad gamma identifies gamma=-e1 which is sign-sensitive but the
# +/- pairing on subsets means the e1-IMAGE is symmetric, NOT halved. So /2 is NOT from this symmetry.
# Conclusion: the /2 is EMPIRICAL, not structural. Document honestly.
import math
# How tight does K/2 get at central band as n grows? We have only n=16 (104/128=0.8125 of K/2).
# Lower bound on central #bad: it's >= (the e1=0 count?) Hard. Honest: UNKNOWN for n>=32.
print()
print("central-band ratio #bad/(K/2) at n=16, r=8:", 104/128)
print("=> only 1.23x headroom below K/2 at the single measured central point; n>=32 central UNVERIFIED.")
