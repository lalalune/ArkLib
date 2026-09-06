# Excluding common-composition locator architectures and all 27 proper binary lifts

This is a written, independently audited algebraic exclusion for a restricted six-locator architecture. It is not Lean-formalized, does not exclude arbitrary six-locator configurations, and does not prove the Proximity Prize. The proof retains genuine common-domain divisibility. In fact it needs neither splitting nor squarefreeness and is valid in every characteristic.

## The exact theorem

Let K be any field and let b>=1 be an integer, with n=6b-2. Let psi(X) and D(Y) be monic polynomials with

    deg psi=ell>=2,       V(X)=D(psi(X)),       deg V=n.

Let integers a>=1 and 0<r<ell satisfy ell*a+r=2b. There cannot be six distinct monic polynomials W_i satisfying all of the following:

    W_i=F_i(psi(X))*Q_i(X),
    deg F_i=a, deg Q_i=r,
    W_i divides V,
    dim_K span(W_1,...,W_6)=3,
    gcd(W_1,...,W_6)=1,
    deg gcd(W_i,W_j)<=b for i!=j.

The factors may be normalized monic without changing W_i: rescale F_i to make it monic, which makes the compensating Q_i monic because W_i already is. All arguments below use these normalized factors.

Two useful inequalities are automatic. First ell*a>=ell>r, so ell*a>b. Second, with M=deg D, the equality ell*M=n gives

    M=3a+(3r-2)/ell < 3a+3 <= 6a.

At the production parameters, take ell=2^h for any h=2,...,28. Put c=1 when h is even and c=2 when h is odd, and set

    a=(2^(30-h)-c)/3,       r=(c*ell+2)/3,
    psi=X^ell,             D=Y^(2^(30-h))-1,
    n=1073741824,           b=178956971.

These are integers with a>=1, 0<r<ell, ell*a+r=2b, and deg D=3a+c<6a. The theorem excludes all 27 common-power architectures. At h=2 it is exactly W_i=F_i(X^4)Q_i with deg F_i=89478485 and deg Q_i=2. At h=3 it has ell=8, deg F_i=44739242 and deg Q_i=6. At h=28 it has ell=268435456, a=1, and deg Q_i=89478486. The even h recover the fourteen fourth-power levels. The levels h=29,30 have a=0 and are outside the theorem. A separate balanced-syzygy argument for the pure quadratic lift h=1 is given below; the theorem itself requires r>0.

## Common domain consequences, using divisibility rather than root heuristics

Since F_i(psi) divides D(psi), one has

    F_i(Y) divides D(Y).

Indeed divide D(Y) by F_i(Y) in K[Y] and then substitute Y=psi(X). A nonzero remainder of degree less than a would become a nonzero polynomial of degree less than ell*a, so it could not be divisible by F_i(psi). This argument works even in inseparable characteristics.

Suppose distinct monic F_i of degree a lie in a fixed two-dimensional polynomial space. The gcd G of any two distinct members is the gcd of that whole space, since those two members form a basis. Write g=deg G. The F_i/G are pairwise coprime, hence for any m selected members their lcm has degree

    deg lcm(F_1,...,F_m)=m*a-(m-1)*g.

This holds even when G and one individual quotient share factors. Each irreducible can occur beyond its common G-multiplicity in at most one quotient. Since the lcm divides D, its degree is at most M.

Also, for any A,B,Q,

    gcd(Q*A(psi),Q*B(psi))=Q*gcd(A,B)(psi)

up to a nonzero constant. This follows by factoring out Q and composing a Bezout identity for A/gcd(A,B) and B/gcd(A,B). It does not require Q to be coprime to the other factors.

## Two bounds for fixed-factor lines

A projective line of pure tensors with F fixed contains at most one configured W_i. Any two would share F(psi), whose degree is ell*a>b.

A stronger elementary lemma gives the other bound: **any projective line of degree-2b divisor locators contains at most four configured points**, regardless of the power architecture. If five distinct monic degree-d locators, d=2b, lie in a two-dimensional polynomial space, their common pairwise gcd has some degree delta<=b=d/2. The lcm of the five members therefore has degree

    5d-4delta >= 3d = 6b = n+2.

But that lcm divides the common degree-n domain polynomial. This is impossible. In particular every fixed-Q line has at most four configured points. This proof requires no splitting, separability, or counting modulo ell.

## Elementary classification of the three-dimensional tensor space

Because r<ell, the polynomials psi(X)^j X^t for 0<=j<=a and 0<=t<=r have pairwise distinct leading degrees ell*j+t. This gives an injective K-linear map

    K[Y]_(<=a) tensor K[X]_(<=r) -> K[X],
    F tensor Q -> F(psi(X))Q(X).

Thus the six W_i are six projectively distinct rank-one tensors spanning a three-dimensional space L. Choose three of them as a tensor basis F_1 tensor Q_1, F_2 tensor Q_2, F_3 tensor Q_3. Put U0=span(F_1,F_2,F_3) and V0=span(Q_1,Q_2,Q_3).

Every configured F_i belongs to U0 and every Q_i to V0. To prove this, contract its tensor with a linear functional nonzero on its Q factor; the result is a nonzero multiple of F_i lying in U0. Contract on the other side for Q_i. Hence both factor spaces have dimension at most three.

If dim U0=3, use F_1,F_2,F_3 as a basis. The matrix of a combination

    sum_j alpha_j F_j tensor Q_j

has rows alpha_j Q_j. Its rank is exactly the dimension of the span of the Q_j for which alpha_j is nonzero. Therefore it has rank one exactly when all active Q_j are proportional. The proportionality classes of three nonzero vectors have only three possibilities:

- Three singleton classes: only the three basis points are rank one.
- A class of two and a singleton: a fixed-Q line plus one isolated point. There are at most four configured points on the line and one elsewhere, hence at most five.
- One class of three: all of L has Q fixed. Then Q is a positive-degree common factor of all W_i, contradicting their gcd being one.

The same reasoning applies if dim V0=3, interchanging F and Q. A fixed-F line has at most one configured point, and a fixed-F plane has a nonconstant common factor. These cases cannot contain six admissible points either.

The remaining possibility is dim U0=dim V0=2. Indeed their product dimension must be at least dim L=3, so once both are at most two neither can be one. Now L is a hyperplane in the four-dimensional tensor space U0 tensor V0. With two-dimensional coordinates u,v, its pure tensors are exactly

    u^T H v=0

for a nonzero 2-by-2 matrix H over K.

If rank H=1, write H=p q^T. The equation is (u^T p)(q^T v)=0. Its pure points form one line with F fixed and one line with Q fixed. There are at most one plus four configured points, hence at most five. This directly handles reducible sections and their intersection; no assumption about conic rationality or algebraic closure is used.

If rank H=2, each nonzero u has a unique projective v in the kernel of u^T H, and conversely. This correspondence is an invertible projective linear map over K. Thus distinct configured tensors have pairwise distinct F factors. All six F_i lie in the same two-dimensional pencil U0. Its common gcd G has G(psi) dividing every W_i, so the overall gcd-one assumption forces G=1. Their lcm consequently has degree 6a. But it divides D, so

    6a<=M<6a,

which is impossible. This closes the final case.

This classification covers zero coefficients, lines plus isolated points, contained fixed-factor planes, reducible conics, and projective-graph conics using only ranks and gcds. It does not rely on a geometric classification of arbitrary plane sections of a Segre variety.

## A separate balanced-syzygy exclusion for a pure common quadratic lift

The main theorem needs a positive remainder degree r. At production the pure quadratic architecture W_i=F_i(psi), deg psi=2, deg F_i=b is excluded by the balanced-syzygy condition forced by actual pair realization. This is an additional hypothesis, not a consequence of the preceding divisor and pair-gcd assumptions alone.

Let b be odd, put q=(b-1)/2, and choose a polynomial basis w_j=F_j(psi), j=1,2,3, for the locator span. Each F_j has degree at most b. The linear map

    (K[Y]_(<=q))^3 -> K[Y]_(<=b+q),
    (A_1,A_2,A_3) -> sum_j A_j F_j

has source dimension 3q+3 and target dimension 3q+2. It therefore has a nonzero kernel vector. Composing it with psi yields a nonzero syzygy of w of degree at most 2q=b-1. The balanced condition excludes every such syzygy: its coefficient map T_w in the [reconstruction note](astra_mca_locator_reconstruction-2026-09-05.md) is injective below degree b. Hence a common quadratic composition is impossible for a balanced locator span when b is odd, over every field and for any monic quadratic psi.

At production q=89478485. The source and target dimensions are 268435458 and 268435457, and the resulting syzygy has degree at most 178956970, strictly below b=178956971. Thus the genuine six-pair constraints also exclude the pure X^2 architecture. This does not extend the positive-remainder theorem to an arbitrary factor Q of degree equal to ell, where the tensor-substitution injection fails.

## Reproduction and precise scope

Run `python3 scripts/probes/astra_mca_near_power_locator_exclusion_check.py`. It checks all 27 production degree identities, the exact two-degree obstruction for five points on a line, and the graph-case degree gap; exhausts every rank-one hyperplane section of the 2-by-2 tensor space over F2,F3,F5,F7; checks the three-dimensional-factor proportionality classification; verifies composition and low-degree quadratic-syzygy controls; and verifies exact polynomial common-domain controls at lengths 16 and 28. The length-28 control has five points on a fixed-Q line, and is correctly rejected because its pair gcd degree is six rather than the permitted five. Thus the probe does not simply reject every fixed-factor configuration.

The general theorem is proved by the preceding argument, not by the finite controls. Its production application is exact for the stated common-power factorizations and does not assume that arbitrary locators possess such a factorization. No saturation, residual-pairing, or square-resultant assumption is needed for the 27 proper positive-remainder exclusions; the weaker pairwise gcd bound from a genuine noncollinear realization already suffices. The separate pure quadratic exclusion additionally uses the balanced syzygies already required by an actual realization.

An independent agent reviewed the elementary tensor classification, the general composition argument, all 27 binary levels, and the separate balanced quadratic exclusion. Its independently computed production dimensions and degree gaps agree with the checker. This is agent review of a written proof, not external human peer review or Lean verification.

The [inversion sharpness family](astra_mca_inversion_locator_sharpness-2026-09-05.md)
shows that the abstract four-points-per-line ceiling cannot be lowered to
three, even with common cyclotomic divisibility, balanced syzygies, and a
birational full locator map. It is a non-dyadic length-10 construction;
its six reconstructed pencils supply only one common projective bad
direction. This tests the limits of the structural argument and supplies
no production counterexample.
