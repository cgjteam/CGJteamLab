# Euclid, Elements - Book I

This directory contains the documentation accompanying the reconstruction of Euclid's *Elements*, Book I, in the CGJteamLab Lean 4 project.

The Book I development covers propositions I.1-I.48. The corresponding Lean modules are imported by the main `CGJteamLab.lean` module.

## Main document

- [Book1R.pdf](Book1R.pdf) - combined Book I reconstruction and mathematical documentation.

## Proposition-by-proposition documents

Each proposition also has a separate PDF. These files are intended to make individual constructions and proofs easy to inspect without opening the complete Book I document.

| Euclid | Brief statement | Lean source |
|---|---|---|
| I.1 | Construction of an equilateral triangle on a given segment | [Proposition01.lean](../../Proposition01.lean) |
| I.2 | Transfer of length: constructing from a given point a segment equal to a given segment | [Proposition02.lean](../../Proposition02.lean) |
| I.3 | Cutting off from a longer segment a part equal to a shorter segment | [Proposition03.lean](../../Proposition03.lean) |
| I.4 | Side-angle-side congruence (SAS) | [Proposition04.lean](../../Proposition04.lean) |
| I.5 | Base angles of an isosceles triangle are equal | [Proposition05.lean](../../Proposition05.lean) |
| I.6 | Equal angles in a triangle subtend equal opposite sides | [Proposition06.lean](../../Proposition06.lean) |
| I.7 | Uniqueness of a vertex determined by a base and two prescribed distances | [Proposition07.lean](../../Proposition07.lean) |
| I.8 | Side-side-side congruence (SSS) | [Proposition08.lean](../../Proposition08.lean) |
| I.9 | Construction of an angle bisector | [Proposition09.lean](../../Proposition09.lean) |
| I.10 | Construction of the midpoint of a segment | [Proposition10.lean](../../Proposition10.lean) |
| I.11 | Construction of a perpendicular at a point on a line | [Proposition11.lean](../../Proposition11.lean) |
| I.12 | Construction of a perpendicular from a point to a line | [Proposition12.lean](../../Proposition12.lean) |
| I.13 | Adjacent angles on a straight line sum to two right angles | [Proposition13.lean](../../Proposition13.lean) |
| I.14 | Converse of I.13: two angles summing to two right angles form a straight line | [Proposition14.lean](../../Proposition14.lean) |
| I.15 | Vertical angles are equal | [Proposition15.lean](../../Proposition15.lean) |
| I.16 | An exterior angle of a triangle is greater than either opposite interior angle | [Proposition16.lean](../../Proposition16.lean) |
| I.17 | Any two angles of a triangle sum to less than two right angles | [Proposition17.lean](../../Proposition17.lean) |
| I.18 | The greater side of a triangle subtends the greater angle | [Proposition18.lean](../../Proposition18.lean) |
| I.19 | The greater angle of a triangle subtends the greater side | [Proposition19.lean](../../Proposition19.lean) |
| I.20 | Triangle inequality | [Proposition20.lean](../../Proposition20.lean) |
| I.21 | Comparison of sides and angle for a point inside a triangle | [Proposition21.lean](../../Proposition21.lean) |
| I.22 | Construction of a triangle from three given side lengths | [Proposition22.lean](../../Proposition22.lean) |
| I.23 | Construction of an angle equal to a given angle | [Proposition23.lean](../../Proposition23.lean) |
| I.24 | A greater included angle gives a greater third side | [Proposition24.lean](../../Proposition24.lean) |
| I.25 | A greater third side gives a greater included angle | [Proposition25.lean](../../Proposition25.lean) |
| I.26 | Angle-side-angle / angle-angle-side congruence | [Proposition26.lean](../../Proposition26.lean) |
| I.27 | Equal alternate interior angles imply parallel lines | [Proposition27.lean](../../Proposition27.lean) |
| I.28 | Parallelism criteria from corresponding and same-side interior angles | [Proposition28.lean](../../Proposition28.lean) |
| I.29 | Angle relations formed by a transversal of parallel lines | [Proposition29.lean](../../Proposition29.lean) |
| I.30 | Lines parallel to the same line are parallel to each other | [Proposition30.lean](../../Proposition30.lean) |
| I.31 | Construction of a parallel line through a given point | [Proposition31.lean](../../Proposition31.lean) |
| I.32 | Sum of the angles of a triangle and the exterior-angle theorem | [Proposition32.lean](../../Proposition32.lean) |
| I.33 | Joining the ends of equal and parallel segments gives equal and parallel segments | [Proposition33.lean](../../Proposition33.lean) |
| I.34 | Properties of a parallelogram: opposite sides, opposite angles, and a diagonal | [Proposition34.lean](../../Proposition34.lean) |
| I.35 | Parallelograms on the same base and between the same parallels are equal | [Proposition35.lean](../../Proposition35.lean) |
| I.36 | Parallelograms on equal bases and between the same parallels are equal | [Proposition36.lean](../../Proposition36.lean) |
| I.37 | Triangles on the same base and between the same parallels are equal | [Proposition37.lean](../../Proposition37.lean) |
| I.38 | Triangles on equal bases and between the same parallels are equal | [Proposition38.lean](../../Proposition38.lean) |
| I.39 | Equal triangles on the same base lie between the same parallels | [Proposition39.lean](../../Proposition39.lean) |
| I.40 | Equal triangles on equal bases lie between the same parallels | [Proposition40.lean](../../Proposition40.lean) |
| I.41 | A parallelogram on the same base has twice the area of a triangle | [Proposition41.lean](../../Proposition41.lean) |
| I.42 | Construction of a parallelogram equal to a given triangle with a prescribed angle | [Proposition42.lean](../../Proposition42.lean) |
| I.43 | Complements about the diagonal of a parallelogram are equal | [Proposition43.lean](../../Proposition43.lean) |
| I.44 | Application to a given segment of a parallelogram equal to a given triangle | [Proposition44.lean](../../Proposition44.lean) |
| I.45 | Construction of a parallelogram equal to a given rectilinear figure | [Proposition45.lean](../../Proposition45.lean) |
| I.46 | Construction of a square on a given segment | [Proposition46.lean](../../Proposition46.lean) |
| I.47 | Pythagorean theorem | [Proposition47.lean](../../Proposition47.lean) |
| I.48 | Converse of the Pythagorean theorem | [Proposition48.lean](../../Proposition48.lean) |
## Diagrams

- [book1.png](book1.png) is the Book I illustration used by the documentation.
- [`figures/`](figures/) contains Asymptote source files for proposition diagrams and auxiliary construction/audit figures.

The diagrams are part of the mathematical documentation: they are used to make the incidence, order, congruence, parallelism, and construction data visible, but they are not substitutes for the formal Lean proofs.

## Formalization approach

The reconstruction is carried out in synthetic geometry. The Lean development is built on the Hilbert-style infrastructure of CGJteamLab and the project's `Book Zero` interface rather than on coordinates or analytic geometry.

The documentation therefore records not only Euclid's argument, but also the additional incidence, betweenness, congruence, ray, angle, parallelism, and construction facts that have to be made explicit in a proof assistant.

## Audit status

Book I is under continuing documentation and diagram audit. The proposition PDFs and the combined `Book1R.pdf` may be revised when the mathematical commentary, dependency analysis, diagrams, or correspondence between the informal argument and the Lean proof is improved.

For the current formal source, the Lean files in the repository are authoritative.
