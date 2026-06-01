/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/
import ArkLib.CommitmentScheme.Ajtai.Simple.Scheme
import ArkLib.CommitmentScheme.Ajtai.Gadget
import VCVio

/-!
# Inner-Outer Ajtai Commitment Scheme

The Greyhound [NS24] / Hachi [NOZ26] inner-outer commitment composition over the cyclotomic
ring `Rq Φ`:
each message block is gadget-decomposed and inner-committed under `A`; the inner
commitments are gadget-decomposed, flattened, and outer-committed under `B`.

Adapted from VCV-io's `LatticeCrypto.Ajtai.InnerOuter.Scheme`.

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

/-- Public parameters: inner Ajtai matrix `A` and outer Ajtai matrix `B`. -/
structure PublicParams (Φ : CyclotomicModulus R)
    (innerRows messageRows messageDigits outerRows blocks innerDigits : Nat) where
  /-- Inner Ajtai matrix `A`. -/
  innerMatrix : Simple.PublicParams Φ innerRows (messageRows * messageDigits)
  /-- Outer Ajtai matrix `B`. -/
  outerMatrix : Simple.PublicParams Φ outerRows (blocks * (innerRows * innerDigits))

/-- Opening: gadget decompositions of the message blocks and of the inner commitments. -/
structure Opening (Φ : CyclotomicModulus R)
    (innerRows messageRows messageDigits blocks innerDigits : Nat) where
  /-- Gadget decompositions of the message blocks. -/
  messageDecomp : PolyVec (PolyVec (Rq Φ) (messageRows * messageDigits)) blocks
  /-- Gadget decompositions of the inner commitments. -/
  innerDecomp : PolyVec (PolyVec (Rq Φ) (innerRows * innerDigits)) blocks

/-- The decomposition operations used by the honest committer. -/
structure Decomposition (Φ : CyclotomicModulus R)
    (messageRows messageDigits innerRows innerDigits : Nat) where
  /-- Decompose one message block w.r.t. the message gadget. -/
  message : PolyVec (Rq Φ) messageRows → PolyVec (Rq Φ) (messageRows * messageDigits)
  /-- Decompose one inner commitment w.r.t. the inner gadget. -/
  inner : PolyVec (Rq Φ) innerRows → PolyVec (Rq Φ) (innerRows * innerDigits)

/-- The honest decomposition whose message and inner steps are both the Hachi gadget inverse
`G⁻¹` (`gadgetDecompose`) built from base-`b` digit decompositions. -/
def Decomposition.ofDigits [DecidableEq R] {base : R}
    (ddMsg : DigitDecomposition base messageDigits)
    (ddInner : DigitDecomposition base innerDigits) :
    Decomposition Φ messageRows messageDigits innerRows innerDigits where
  message := gadgetDecompose Φ ddMsg
  inner := gadgetDecompose Φ ddInner

/-- Messages: block vectors over the message row space. -/
abbrev Message (Φ : CyclotomicModulus R) (messageRows blocks : Nat) :=
  PolyVec (PolyVec (Rq Φ) messageRows) blocks

/-- Inner-outer commitments live in the outer row space. -/
abbrev Commitment (Φ : CyclotomicModulus R) (outerRows : Nat) := Simple.Commitment Φ outerRows

/-- Honest opening generation from the supplied decomposition operations. -/
def openMessage (decomp : Decomposition Φ messageRows messageDigits innerRows innerDigits)
    (pp : PublicParams Φ innerRows messageRows messageDigits outerRows blocks innerDigits)
    (m : Message Φ messageRows blocks) :
    Opening Φ innerRows messageRows messageDigits blocks innerDigits :=
  let ss := fun i => decomp.message (m i)
  { messageDecomp := ss
    innerDecomp := fun i => decomp.inner (Simple.commit Φ pp.innerMatrix (ss i)) }

/-- Compute the outer commitment from an opening. -/
def commitWithOpening
    (pp : PublicParams Φ innerRows messageRows messageDigits outerRows blocks innerDigits)
    (opening : Opening Φ innerRows messageRows messageDigits blocks innerDigits) :
    Commitment Φ outerRows :=
  Simple.commit Φ pp.outerMatrix (PolyVec.flattenBlocks opening.innerDecomp)

variable [DecidableEq (PolyVec (Rq Φ) messageRows)]
variable [DecidableEq (PolyVec (Rq Φ) innerRows)]
variable [DecidableEq (Commitment Φ outerRows)]

/-- Verify an inner-outer opening: message gadget checks, inner gadget checks, outer check. -/
def verify (base : R)
    (pp : PublicParams Φ innerRows messageRows messageDigits outerRows blocks innerDigits)
    (m : Message Φ messageRows blocks) (c : Commitment Φ outerRows)
    (opening : Opening Φ innerRows messageRows messageDigits blocks innerDigits) : Bool :=
  (List.finRange blocks).all (fun i =>
    Simple.verify Φ (gadgetMatrix Φ base messageRows messageDigits)
      (opening.messageDecomp i) (m i) ()) &&
    (List.finRange blocks).all (fun i =>
      Simple.verify Φ (gadgetMatrix Φ base innerRows innerDigits)
        (opening.innerDecomp i)
        (Simple.commit Φ pp.innerMatrix (opening.messageDecomp i)) ()) &&
    Simple.verify Φ pp.outerMatrix (PolyVec.flattenBlocks opening.innerDecomp) c ()

variable
  [SampleableType (Simple.PublicParams Φ innerRows (messageRows * messageDigits))]
  [SampleableType (Simple.PublicParams Φ outerRows (blocks * (innerRows * innerDigits)))]

/-- The inner-outer Ajtai commitment as a `CommitmentScheme`. -/
def commitmentScheme (base : R)
    (decomp : Decomposition Φ messageRows messageDigits innerRows innerDigits) :
    CommitmentScheme
      (PublicParams Φ innerRows messageRows messageDigits outerRows blocks innerDigits)
      (Message Φ messageRows blocks) (Commitment Φ outerRows)
      (Opening Φ innerRows messageRows messageDigits blocks innerDigits) where
  setup := do
    let A ← $ᵗ (Simple.PublicParams Φ innerRows (messageRows * messageDigits))
    let B ← $ᵗ (Simple.PublicParams Φ outerRows (blocks * (innerRows * innerDigits)))
    pure { innerMatrix := A, outerMatrix := B }
  commit pp m :=
    let opening := openMessage Φ decomp pp m
    pure (commitWithOpening Φ pp opening, opening)
  verify pp m c opening := verify Φ base pp m c opening

end ArkLib.Lattices.Ajtai.InnerOuter
