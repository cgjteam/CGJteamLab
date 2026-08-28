// perpendicular_axes_exact2.asy
// Exactness witness for the perpendicular-axis case.
//
// U lies on l1, so r1(U)=U.
// U is off l2, so r2(U)=U' != U.
// Therefore (r2 r1)(U)=U' != U.

import CoxeterFiguresCommon;

size(10cm);

pair O = (0,0);
pair U = (3.0,0);
pair Up = (-3.0,0);
pair V = (0,2.7);

path l1 = (-4.3,0) -- (4.3,0);
path l2 = (0,-3.6) -- (0,3.6);

draw(l1, axispen);
draw(l2, axispen);

draw((0.36,0)--(0.36,0.36)--(0,0.36), mainpen);

markPointLabel("$O$", O, SW);
markPointLabel("$U$", U, S);
markPointLabel("$r_2(U)$", Up, S);
markPointLabel("$V$", V, E);

label("$l_1$", (4.3,0), E);
label("$l_2$", (0,3.6), N);

draw(U--Up, helppen);

label("$r_1(U)=U$", U + (0.0,0.55), N);
label("$r_2(U)\neq U$", (0,-0.55), S);
