// equilateral_exact3.asy
// Exact-period witness for the p=3 configuration.
//
// For the implementation-order product r_a r_b:
//   A -> B,
//   B -> C,
//   C -> A.
//
// Thus the product is not the identity, and together with the proved
// cube relation this exhibits the geometric 3-cycle behind exact period 3.

import CoxeterFiguresCommon;

size(11cm);

pair A = (0,0);
pair B = (6,0);
pair C = (3,3*sqrt(3));

pair MA = midpoint(B,C);
pair MB = midpoint(A,C);
pair MC = midpoint(A,B);

draw(A--B--C--cycle, mainpen);

draw(lineThrough(A,MA,0.12,0.14), helppen);
draw(lineThrough(B,MB,0.12,0.14), helppen);
draw(lineThrough(C,MC,0.12,0.14), helppen);

markPointLabel("$A$", A, SW);
markPointLabel("$B$", B, SE);
markPointLabel("$C$", C, N);

label("$a$", A + 0.55*(MA-A) + (-0.28,0.08), W);
label("$b$", B + 0.55*(MB-B) + (0.28,0.08), E);
label("$c$", C + 0.45*(MC-C) + (0.28,0.05), E);

// Directed 3-cycle on the vertices.
// The product is r_a r_b in the pointwise convention used in the proof.
draw(A--B, Arrow);
draw(B--C, Arrow);
draw(C--A, Arrow);

label("$r_a r_b$", midpoint(A,B) + (0,-0.45), S);
label("$r_a r_b$", midpoint(B,C) + (0.40,0.10), E);
label("$r_a r_b$", midpoint(C,A) + (-0.40,0.10), W);

// Exactness witness used in Lean.
label("$B\mapsto C,\quad B\neq C$", (3.0,-1.0), S);
label("$\left(r_a r_b\right)^3=1$", (3.0,5.0), N);
