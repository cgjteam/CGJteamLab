import CGJteamLab.HilbertBookZero

namespace Geometry

variable (Geo : Geometry.Geo)

variable [HilbertIncidence Geo]
variable [HilbertCongruence Geo]

/-!
# Euclid I.27

This file intentionally retains two formulations of Proposition I.27.

The first theorem exposes the proposition at the level of the already
developed Hilbert synthetic interface.  Its proof is a direct application
of `parallel_from_equal_angles`.

The second theorem starts from a more explicit transversal configuration
of the kind normally represented by the classical Euclidean diagram.  It
makes visible the additional incidence, order, ray-orientation,
side-of-line, and parallel-transport work needed to connect that
configuration with the Hilbert alternate-angle criterion.

At the present stage we deliberately do not identify one of these two
formulations as uniquely canonical.

There is a genuine proof-theoretic question here.

The Hilbert development has already established the implication

    equal alternate angles -> parallel lines

before Proposition I.27 is reached in the Euclidean sequence.  Therefore
a thin Euclid-level wrapper is consistent with the architecture used
elsewhere in the project.

On the other hand, the explicit transversal formulation records geometric
information that is largely implicit in the traditional statement and
diagram of I.27.

Both versions are retained so that this distinction can be studied later,
in particular by comparing the Euclidean proof, the Hilbert dependency
graph, Book Zero, and the external proof corpus.

No conclusion about the final preferred API should be inferred merely
from the present ordering or names of the two theorems.
-/


/--
Euclid I.27 at the level of the established Hilbert synthetic interface.

The points are given in the ordered alternate-angle configuration expected
by `parallel_from_equal_angles`:

    A-D-C,
    C-E-B,
    D-E-F.

The angles

    angle ECD
    angle EBF

are alternate interior angles determined by this configuration.

The mathematical content is

    angle ECD ~= angle EBF
    ----------------------
           AD || BF

and this content has already been proved in the Hilbert layer.

Consequently the Euclid-level theorem is a thin wrapper rather than a
reconstruction of the underlying alternate-angle argument.

This formulation is intentionally retained even though a more explicit
transversal version is given below.  The purpose is to preserve the fact
that, at the level of the developed synthetic API, the central implication
of I.27 is already available as a reusable theorem.
-/
theorem euclid_proposition_27
    (A C D B E F : Geo.Point)
    (hADC : Geo.Between A D C)
    (hCEB : Geo.Between C E B)
    (hDEF : Geo.Between D E F)
    (hCED : ¬ Collinear Geo C E D)
    (hAngle : Geo.AngleCongruent E C D E B F) :
    Geo.Parallel A D B F := by

  exact
    parallel_from_equal_angles
      Geo
      A C D
      B E F
      hADC
      hCEB
      hDEF
      hCED
      hAngle


/--
Euclid I.27 in an explicit transversal configuration.

This formulation begins from geometry closer to that displayed in a
classical diagram:

    A-E-B,
    C-F-D,

with `E` and `F` lying on the transversal `trans`.

The selected interior arms `EA` and `FD` lie on opposite sides of the
transversal, and the hypothesis is

    angle AEF ~= angle EFD.

The proof has two conceptually different parts.

First, the diagram-level configuration is normalized to the form required
by the Hilbert alternate-angle theorem.

A point `M` is chosen between `E` and `F`.  This explicitly names the two
directions of the transversal.  From

    E-M-F

we obtain the corresponding same-ray relations at `E` and `F`.
After reversing the first angle and transporting its transversal arms
along these same rays, the original hypothesis becomes

    angle MEA ~= angle MFD.

The theorem

    hilbert_parallel_of_alternate_angles_oppositeSide_lines

can then be applied and yields the local parallelism

    EA || FD.

Second, this local result is transported to the original lines occurring
in the Euclidean statement.

Using

    A-E-B

the left parallel line is changed from `EA` to `AB`.

Using

    C-F-D

the right parallel line is changed from `FD` to `CD`.

The final conclusion is therefore

    AB || CD.

This proof does not establish a different alternate-angle principle from
`euclid_proposition_27` above.  Rather, it exposes the geometric work
required to pass from an explicit classical transversal configuration to
the normalized configuration already supported by the Hilbert theory.

The exact proof-theoretic status of the distinction between these two
formulations is intentionally left open.  It may eventually be appropriate
to regard the first theorem as the proposition at the synthetic API level
and this theorem as a configuration-normalization result.  Alternatively,
the explicit transversal formulation may turn out to be the more useful
public representation of Euclid I.27.

For now both are retained so that this question is not erased by premature
refactoring.
-/
theorem euclid_proposition_27_transversal
    (A B C D E F : Geo.Point)
    (trans : Geo.Line)
    (hAEB : Geo.Between A E B)
    (hCFD : Geo.Between C F D)
    (hEF : E ≠ F)
    (hEtrans : HilbertIncidence.OnLine E trans)
    (hFtrans : HilbertIncidence.OnLine F trans)
    (hOpposite : HilbertOppositeSide Geo A D trans)
    (hAngle : Geo.AngleCongruent A E F E F D) :
    Geo.Parallel A B C D := by

  rcases hilbert_between_exists Geo E F hEF with
    ⟨M, hEMF⟩

  have hFME : Geo.Between F M E :=
    (HilbertOrder.between_incidence E M F hEMF).2.2.2.2

  have hEMRay : HilbertSameRay Geo E M F :=
    hilbert_sameRay_of_between Geo E M F hEMF

  have hFMERay : HilbertSameRay Geo F M E :=
    hilbert_sameRay_of_between Geo F M E hFME

  have hReversed :
      Geo.AngleCongruent F E A E F D :=
    (Geo.angle_congruent_reverse_first
      A E F E F D).mp hAngle

  have hLeft :
      Geo.Angle M E A = Geo.Angle F E A :=
    hilbert_angle_eq_of_sameRay_first
      Geo E M F A hEMRay

  have hRight :
      Geo.Angle M F D = Geo.Angle E F D :=
    hilbert_angle_eq_of_sameRay_first
      Geo F M E D hFMERay

  have hAlternate :
      Geo.AngleCongruent M E A M F D := by
    unfold Geometry.Geo.AngleCongruent at hReversed ⊢
    rw [hLeft, hRight]
    exact hReversed

  have hLocal :
      Geo.Parallel E A F D :=
    hilbert_parallel_of_alternate_angles_oppositeSide_lines
      Geo E A F M D trans
      hEMF
      hEtrans
      hFtrans
      hOpposite
      hAlternate

  have hAEFD :
      Geo.Parallel A E F D :=
    ParallelSwapFirstLine
      Geo E A F D hLocal

  have hAEBcol :
      Collinear Geo A B E :=
    PrimCollinearRotate
      Geo A E B
      (HilbertOrder.between_incidence
        A E B hAEB).2.2.2.1

  have hAB : A ≠ B :=
    (HilbertOrder.between_incidence
      A E B hAEB).2.2.1

  have hABFD :
      Geo.Parallel A B F D :=
    collinear_parallel_trans
      Geo A B E F D
      hAB
      hAEBcol
      hAEFD

  have hABDF :
      Geo.Parallel A B D F :=
    ParallelSwapSecondLine
      Geo A B F D hABFD

  have hDFAB :
      Geo.Parallel D F A B :=
    ParallelSymmetry
      Geo A B D F hABDF

  have hDCF :
      Collinear Geo D C F :=
    PrimCollinearCycle
      Geo F D C
      (PrimCollinearCycle
        Geo C F D
        (HilbertOrder.between_incidence
          C F D hCFD).2.2.2.1)

  have hDC : D ≠ C :=
    (HilbertOrder.between_incidence
      C F D hCFD).2.2.1.symm

  have hDCAB :
      Geo.Parallel D C A B :=
    collinear_parallel_trans
      Geo D C F A B
      hDC
      hDCF
      hDFAB

  have hCDAB :
      Geo.Parallel C D A B :=
    ParallelSwapFirstLine
      Geo D C A B hDCAB

  exact
    ParallelSymmetry
      Geo C D A B hCDAB

end Geometry
