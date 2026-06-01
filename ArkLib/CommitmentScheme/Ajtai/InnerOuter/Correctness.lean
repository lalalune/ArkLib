/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/
import ArkLib.CommitmentScheme.Ajtai.InnerOuter.Scheme
import ArkLib.CommitmentScheme.Ajtai.Simple.Correctness

/-!
# Correctness of the Inner-Outer Ajtai Commitment

Perfect correctness for lawful gadget decompositions: if the message and inner gadget
decompositions invert their gadget matrices, an honest commitment always verifies.

Adapted from VCV-io's `LatticeCrypto.Ajtai.InnerOuter.Correctness`.

## References

* [Nguyen, N. K., and Seiler, G., *Greyhound: Fast Polynomial Commitments from Lattices*][NS24]
* [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi: Efficient Lattice-Based Multilinear
    Polynomial Commitments over Extension Fields*][NOZ26]
-/

open OracleComp CommitmentScheme CompPoly ArkLib.Lattices ArkLib.Lattices.CyclotomicModulus
  ArkLib.Lattices.Ajtai

namespace ArkLib.Lattices.Ajtai.InnerOuter

variable {R : Type} [Field R] [BEq R] [LawfulBEq R] (Φ : CyclotomicModulus R) [IsCyclotomic Φ]
variable {innerRows messageRows messageDigits outerRows blocks innerDigits : Nat}
variable [DecidableEq (PolyVec (Rq Φ) messageRows)]
variable [DecidableEq (PolyVec (Rq Φ) innerRows)]
variable [DecidableEq (Commitment Φ outerRows)]

/-- Honest message decompositions pass the message gadget checks. -/
theorem openMessage_message_checks (base : R)
    (decomp : Decomposition Φ messageRows messageDigits innerRows innerDigits)
    (hMessageDecomp : IsLawfulGadgetDecomposition Φ base decomp.message)
    (pp : PublicParams Φ innerRows messageRows messageDigits outerRows blocks innerDigits)
    (m : Message Φ messageRows blocks) :
    (List.finRange blocks).all (fun i =>
      Simple.verify Φ (gadgetMatrix Φ base messageRows messageDigits)
        ((openMessage Φ decomp pp m).messageDecomp i) (m i) ()) = true := by
  simp only [List.all_eq_true]
  intro i _
  have hprod : Simple.commit Φ (gadgetMatrix Φ base messageRows messageDigits)
      ((openMessage Φ decomp pp m).messageDecomp i) = m i := by
    simpa [Simple.commit, gadgetMul, openMessage] using hMessageDecomp (m i)
  simp [Simple.verify, hprod]

/-- Honest inner decompositions pass the inner gadget checks. -/
theorem openMessage_inner_checks (base : R)
    (decomp : Decomposition Φ messageRows messageDigits innerRows innerDigits)
    (hInnerDecomp : IsLawfulGadgetDecomposition Φ base decomp.inner)
    (pp : PublicParams Φ innerRows messageRows messageDigits outerRows blocks innerDigits)
    (m : Message Φ messageRows blocks) :
    (List.finRange blocks).all (fun i =>
      Simple.verify Φ (gadgetMatrix Φ base innerRows innerDigits)
        ((openMessage Φ decomp pp m).innerDecomp i)
        (Simple.commit Φ pp.innerMatrix ((openMessage Φ decomp pp m).messageDecomp i)) ())
      = true := by
  simp only [List.all_eq_true]
  intro i _
  have hprod : Simple.commit Φ (gadgetMatrix Φ base innerRows innerDigits)
      ((openMessage Φ decomp pp m).innerDecomp i) =
      Simple.commit Φ pp.innerMatrix ((openMessage Φ decomp pp m).messageDecomp i) := by
    simpa [Simple.commit, gadgetMul, openMessage] using
      hInnerDecomp (Simple.commit Φ pp.innerMatrix (decomp.message (m i)))
  simp [Simple.verify, hprod]

variable
  [SampleableType (Simple.PublicParams Φ innerRows (messageRows * messageDigits))]
  [SampleableType (Simple.PublicParams Φ outerRows (blocks * (innerRows * innerDigits)))]

/-- Inner-outer Ajtai commitments are perfectly correct for any lawful decompositions. -/
theorem perfectlyCorrect_of_lawful (base : R)
    (decomp : Decomposition Φ messageRows messageDigits innerRows innerDigits)
    (hMessageDecomp : IsLawfulGadgetDecomposition Φ base decomp.message)
    (hInnerDecomp : IsLawfulGadgetDecomposition Φ base decomp.inner) :
    (commitmentScheme Φ (outerRows := outerRows) (blocks := blocks) base
      decomp).PerfectlyCorrect := by
  intro pp _ m cd hmem
  simp only [commitmentScheme, support_pure, Set.mem_singleton_iff] at hmem
  rcases hmem with rfl
  have hMessage := openMessage_message_checks Φ base decomp hMessageDecomp pp m
  have hInner := openMessage_inner_checks Φ base decomp hInnerDecomp pp m
  change verify Φ base pp m (commitWithOpening Φ pp (openMessage Φ decomp pp m))
    (openMessage Φ decomp pp m) = true
  unfold verify
  rw [hMessage, hInner]
  simp [commitWithOpening, Simple.verify]

/-- **Perfect correctness with genuine base-`b` (binary) decompositions.** Instantiating both
the message and inner decompositions with the Hachi gadget inverse `gadgetDecompose` built from
any `DigitDecomposition` (lawful by `gadgetDecompose_lawful`), the inner-outer Ajtai commitment
is perfectly correct. The only requirement is `1 ≤ deg φ` (so the gadget constants do not
reduce) and at least one digit per block. -/
theorem perfectlyCorrect_of_digits [DecidableEq R] (base : R)
    (hdeg : 1 ≤ Φ.φ.natDegree) (hmsg : 0 < messageDigits) (hinner : 0 < innerDigits)
    (ddMsg : DigitDecomposition base messageDigits)
    (ddInner : DigitDecomposition base innerDigits) :
    (commitmentScheme Φ (messageRows := messageRows) (innerRows := innerRows)
        (outerRows := outerRows) (blocks := blocks) base
        (Decomposition.ofDigits Φ ddMsg ddInner)).PerfectlyCorrect :=
  perfectlyCorrect_of_lawful Φ base _
    (gadgetDecompose_lawful Φ hmsg hdeg ddMsg)
    (gadgetDecompose_lawful Φ hinner hdeg ddInner)

end ArkLib.Lattices.Ajtai.InnerOuter

/-! ## Concrete instantiation over `ZMod q`

The genuine base-`b` (binary) gadget decomposition `zmodDigitDecomposition` instantiates the
inner-outer commitment over `R = ZMod q`, giving perfect correctness whenever `1 < b`, every
residue fits in the chosen digit count (`q ≤ b ^ digits`), and `1 ≤ deg φ`. -/

namespace ArkLib.Lattices.Ajtai.InnerOuter

section ZMod

variable {q : ℕ} [NeZero q] [Fact (Nat.Prime q)] [BEq (ZMod q)] [LawfulBEq (ZMod q)]
  (Φ : CyclotomicModulus (ZMod q)) [IsCyclotomic Φ]
variable {innerRows messageRows messageDigits outerRows blocks innerDigits : Nat}
variable [DecidableEq (PolyVec (Rq Φ) messageRows)]
variable [DecidableEq (PolyVec (Rq Φ) innerRows)]
variable [DecidableEq (Commitment Φ outerRows)]
variable
  [SampleableType (Simple.PublicParams Φ innerRows (messageRows * messageDigits))]
  [SampleableType (Simple.PublicParams Φ outerRows (blocks * (innerRows * innerDigits)))]

/-- **Perfect correctness with the concrete binary decomposition.** Both message and inner
decompositions are the base-`b` digit decomposition of `ZMod q` (`zmodDigitDecomposition`), the
Hachi gadget inverse `G⁻¹`. -/
theorem perfectlyCorrect (b : ℕ) (hb : 1 < b) (hdeg : 1 ≤ Φ.φ.natDegree)
    (hmsg : 0 < messageDigits) (hinner : 0 < innerDigits)
    (hqm : q ≤ b ^ messageDigits) (hqi : q ≤ b ^ innerDigits) :
    (commitmentScheme Φ (messageRows := messageRows) (innerRows := innerRows)
        (outerRows := outerRows) (blocks := blocks) (b : ZMod q)
        (Decomposition.ofDigits Φ (zmodDigitDecomposition b messageDigits hb hqm)
          (zmodDigitDecomposition b innerDigits hb hqi))).PerfectlyCorrect :=
  perfectlyCorrect_of_digits Φ (b : ZMod q) hdeg hmsg hinner _ _

end ZMod

end ArkLib.Lattices.Ajtai.InnerOuter
