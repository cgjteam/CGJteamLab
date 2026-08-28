// equilateral_braid.asy
// The geometric source of the braid relation.
//
// Reflection in b transports axis a to c:
//   r_b(a) = c  ->  r_b r_a r_b = r_c.
//
// Reflection in a transports axis b to c:
//   r_a(b) = c  ->  r_a r_b r_a = r_c.
//
// Therefore:
//   r_a r_b r_a = r_b r_a r_b.

import CoxeterFiguresCommon;

size(12cm);

pair A = (0,0);
pair B = (6,0);
pair C = (3,3*sqrt(3));

pair MA = midpoint(B,C);
pair MB = midpoint(A,C);
pair MC = midpoint(A,B);

// Main equilateral configuration.
draw(A--B--C--cycle, mainpen);

draw(lineThrough(A,MA,0.15,0.18), axispen);
draw(lineThrough(B,MB,0.15,0.18), axispen);
draw(lineThrough(C,MC,0.15,0.18), axispen);

markPointLabel("$A$", A, SW);
markPointLabel("$B$", B, SE);
markPointLabel("$C$", C, N);

markPointLabel("$M_A$", MA, E);
markPointLabel("$M_B$", MB, NW);
markPointLabel("$M_C$", MC, S);

label("$a$", A + 0.48*(MA-A) + (-0.35,0.05), W);
label("$b$", B + 0.48*(MB-B) + (0.35,0.05), E);
label("$c$", C + 0.42*(MC-C) + (0.35,0.05), E);

// Transport statements.
label("$r_b(a)=c$", (1.35,4.75), W);
label("$r_a(b)=c$", (4.65,4.75), E);

// Conjugation statements.
label("$r_b r_a r_b=r_c$", (1.20,-0.85), S);
label("$r_a r_b r_a=r_c$", (4.80,-0.85), S);

// Final braid relation.
label("$r_a r_b r_a=r_b r_a r_b$", (3.0,-1.55), S);
