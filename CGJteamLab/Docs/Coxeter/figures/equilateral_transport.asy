// equilateral_transport.asy
// Carrier transport in the p=3 configuration.
//
// Reflection in b sends:
//   A   -> C
//   M_A -> M_C
// Hence the carrier a = A M_A is transported onto c = C M_C.

import CoxeterFiguresCommon;

size(11cm);

pair A = (0,0);
pair B = (6,0);
pair C = (3,3*sqrt(3));

pair MA = midpoint(B,C);
pair MB = midpoint(A,C);
pair MC = midpoint(A,B);

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

draw(A--C, helppen);
draw(MA--MC, helppen);

label("$r_b(A)=C$", midpoint(A,C) + (-0.55,0.15), W);
label("$r_b(M_A)=M_C$", midpoint(MA,MC) + (0.55,-0.05), E);

label("$r_b(a)=c$", (3.0,5.0), N);
