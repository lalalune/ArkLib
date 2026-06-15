# CORRECTED PRIZE TARGET: the grand MCA challenge is line-decoding/bad-point count, NOT far-line incidence (2026-06-14)

## The course-correction (read ABF26 = eprint-2026-680, §4)
The entire session (and the #357/#389/#407 lineage) computed FAR-LINE INCIDENCE I(δ) = #close
codewords on a line. ABF26 §4.1 shows this is the WRONG object for the grand MCA challenge:
- **ε_mca(C,δ)** = max over lines L of the fraction of **BAD** points. A point g∈L is GOOD if for
  EVERY agreement set S making g (S,δ)-close to C, the WHOLE line L is (S,δ)-close for that same S
  (i.e. the spanning words u0,u1 both restrict to codewords on S). BAD = not good. So bad points are
  the δ-close points whose agreement set is NOT mutually shared across the line.
- Ordering ε_pg ≤ ε_ca ≤ ε_mca; δ*_MCA is the SMALLEST/hardest. Far-line incidence (close count) is
  an upper proxy; ε_mca (bad count) can be MUCH smaller if close codewords MUTUALLY ALIGN.
- This is why the far-line work was prize-inert (it reproduced Johnson): it counted close, not bad.

## The exact frontier (ABF26 Table 1 + §4.2–4.4)
- Grand MCA challenge: smooth RS L=μ_n (n=2^m), rate ρ∈{1/2,1/4,1/8,1/16}, ε*=2^-128. Find largest
  δ* with ε_mca(C,δ*) ≤ ε*; prove ε_mca > ε* for all δ>δ*. Key question: is δ* > Johnson / near capacity?
- Budget: ε*·|F| ~ n (since |F| ~ n·2^128). So want ε_mca ≤ n/|F|.
- KNOWN upper bounds: below Johnson ε_mca ≤ O(n/|F|) [BCIKS20]; near Johnson ε_mca ≤ O_ρ(n/(η^5|F|))
  [BCHKS25 Thm 4.12] (blows up as η→0, doesn't cleanly reach Johnson). Subspace-design/FRS reach
  capacity: ε_mca(C,1−ρ−η) ≤ O(n/(η|F|)+n/(η^3|F|)) [GG25 Thm 4.14] — but FRS, NOT explicit RS.
- LOWER bound / ceiling: [BCHKS25;KK25 Thm 4.16] worst-case smooth RS has ε_ca(C,1−ρ−Θ(1/log n)) ≥
  n^c/|F| ⟹ δ* ≤ capacity − Ω(1/log n). Error JUMP at Johnson [BCHKS25 Cor 1.7]: ε_mca ≥ Ω(n²/|F|)
  exactly at Johnson.
- ⟹ The conjectured TRUE answer: **δ* = capacity − Θ(1/log n)** (Thm 4.16 lower bound + a matching
  upper bound to be proven). This is consistent with the session's "δ*=1−ρ−H(ρ)/(β log n)" guess.

## The route: LINE-DECODING (ABF26 §4.4, the GG25 engine)
- **Def 4.20 (line-decodable).** C is (δ,a,b) line-decodable if for every f1,f2 and every U:F→C,
  Pr_γ[Δ(f1+γf2, U(γ)) ≤ δ] ≥ a/|F| ⟹ ∃u1,u2∈C with Pr_γ[U(γ)=u1+γu2] ≥ b/|F| (close codewords are
  COLLINEAR in C).
- **Thm 4.21 [GG25 Thm 3.5].** C is (δ,a,n+1) line-decodable ⟹ ε_mca(C,δ) ≤ a/|F|.
- PRIZE = prove explicit smooth RS is (1−ρ−c/log n, n, n+1) line-decodable. GG25 proved this for
  SUBSPACE-DESIGN codes (FRS); explicit RS is NOT subspace-design ⟹ a NEW argument is needed.
- "bad point" (MCA) ⟺ "non-collinear close codeword" (line-decoding). The line-decoding bad count =
  #(close codewords) − #(collinear close codewords).

## The NOVEL lever (connects this session's machinery to the RIGHT object)
For explicit smooth RS L=μ_n, the close-codeword agreements are governed by VANISHING SUMS of
2-power roots of unity, which by Lam-Leung/Mann are RIGID (only antipodal relations). This session
proved/established: (a) antipodal closed form I(t)=C(n/2^s,t/2^s) for the agreement structure;
(b) divided-difference D(R,i)∈Z[ζ_n] q-independent-height rigidity; (c) char-uniformity at binding.
CONJECTURE (novel, nobody has tried — GG25 used subspace-design instead): the antipodal rigidity of
μ_n FORCES the close codewords on a line to be COLLINEAR (the non-collinear/bad count ≤ n), giving
explicit-RS line-decodability at capacity−Θ(1/log n). This is in-regime, and CLOSED (the antipodal
relation ideal is fully classified — no open math), IF the rigidity⟹collinearity step holds.

## Decisive tests to run (the attack)
1. NUMERIC: compute ε_mca directly (bad-point fraction, ABF26 def) for worst-case smooth-RS lines, as
   a function of δ; find where it crosses budget~n; is it BEYOND Johnson / near capacity−Θ(1/log n)?
   (vs the far-line incidence which crosses AT Johnson). This is the make-or-break numeric.
2. STRUCTURE: does antipodal/Lam-Leung rigidity force collinearity of close codewords (line-decoding)?
3. REFUTE: find a smooth-RS line whose bad count is large just beyond Johnson (would kill it).
4. PIN: is δ* = capacity − Θ(1/log n) exactly (Thm 4.16 lower + the conjectured antipodal upper)?

In-tree to build on: GG25SpreadBound.lean (Lemma 3.2), curve-decodability defs, LamLeungMultisetAntipodal,
_AntipodalEvenOddDescent.lean. Paper: ~/papers/arklib/eprint-2026-680-ABF26.pdf (text /tmp/abf26.txt).
