import numpy as np
# WHY 3/7? Trace the conservation. Q3(n;G) = #{6-tuples g_i in G: sum g_i^{n1}=..., sum g_i^{n2}=...}.
# Curve bound (Cor 3.4): Q3 << tau^{11/3} + tau^5/p.  Trivial/diagonal: Q3 >= tau^3 (3!=6 perm of 3 equal pairs... actually diagonal gives ~tau^3).
# The 6th-moment route (Lemma3.1, k=l=3): |S|^{18} <= p^r tau^{18-12} Q3 Q3 = p^r tau^6 Q3^2.
# So |S| <= (p^r tau^6 Q3^2)^{1/18}.  With Q3<<tau^{11/3}: |S| << (p tau^6 tau^{22/3})^{1/18} = (p tau^{40/3})^{1/18}
#   = p^{1/18} tau^{40/54} = p^{1/18} tau^{20/27}.  <-- Lemma 3.7 (with p^{1/9}=p^{2/18}? recheck constant)
# Nontrivial iff p^{1/18} tau^{20/27} < tau  <=> p^{1/18} < tau^{7/27} <=> tau > p^{27/(18*7)} = p^{27/126}=p^{3/14}=p^{0.214}
# Hmm that's p^{3/14}, not 3/7. The 3/7 wall comes from needing Q3<<tau^{11/3} to BEAT the trivial Q3 estimate.

print("=== Where does Q3 curve bound beat trivial? ===")
# Trivial bound on Q3 (no AG): Q3 <= tau^4 (fix 4 of 6, last 2 determined up to ~tau? actually Q3<=tau^4 by Cauchy).
# Curve gives tau^{11/3}. Beats tau^4 always (11/3<4). But the RELEVANT comparison:
# Q3 has a DIAGONAL lower bound ~ tau^3 (and the main-term floor). Curve tau^{11/3} vs diagonal tau^3:
#   tau^{11/3} >> tau^3 always, so curve bound is ABOVE diagonal -> it's a real (non-vacuous-vs-diagonal) bound only matters for the moment.
# The s^5/p... let's check the actual T3 terms. T3 << s^{7/3}p^{11/3} + s p^4, s=(p-1)/tau.
# T3 trivial = s^6 * (#solutions of diagonal) ~ s^6 * p^... no: T3 counts x_i in F_p^*, with G replaced by all of F_p^* scaled.
# Q3 = s^{-6} T3.  Trivial T3: fix x4,x5,x6 (p^3 ways) -> 2 eqns in x1,x2,x3 -> generically p^1 solutions => T3~p^4. 
# So curve s^{7/3}p^{11/3} beats trivial p^4 iff s^{7/3}p^{11/3} < p^4 <=> s^{7/3}<p^{1/3} <=> s<p^{1/7} <=> (p/tau)<p^{1/7} <=> tau>p^{6/7}?? 
# vs sp^4 term beats p^4 iff s<1 impossible. So the sp^4 term is ALWAYS >= trivial p^4 when s>=1!
print("T3 bound terms: s^{7/3}p^{11/3} and s*p^4, with s=(p-1)/tau >= 1.")
print("Trivial T3 ~ p^4. The term s*p^4 >= p^4 for all s>=1 => NEVER beats trivial unless other term dominates AND s small.")
for beta in [7/3.0, 2.5, 3, 4, 5]:
    # tau=p^{1/beta}, s=p^{1-1/beta}=p^{(beta-1)/beta}
    es = (beta-1)/beta
    e_t3_curve = (7/3)*es + 11/3   # exponent of s^{7/3}p^{11/3}
    e_t3_lin   = es + 4            # exponent of s p^4
    e_t3_triv  = 4
    e_best = min(e_t3_curve, e_t3_lin)
    print(f"beta={beta:4.2f}: s=p^{es:.3f}  curveTerm=p^{e_t3_curve:.3f}  linTerm=p^{e_t3_lin:.3f}  triv=p^{e_t3_triv:.3f}  beats_triv={e_best<e_t3_triv}")
print()
print("=> s*p^4 term: exponent (beta-1)/beta + 4 > 4 always. The bound NEVER goes below trivial p^4")
print("   in prize regime; it only beats trivial when s small i.e. tau large (tau>=p^{3/7}). CONFIRMED FLOOR.")
