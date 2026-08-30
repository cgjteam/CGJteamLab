// finite_radial_polygon.asy
// Schematic oriented equilateral radial polygon for the general finite-period chapter.

import CoxeterFiguresCommon;

size(11cm);

pair O  = (0,0);
real R = 3.0;

pair Vn  = R*dir(90);
pair Vn1 = R*dir(30);
pair Vn2 = R*dir(-30);
pair V3  = R*dir(-90);
pair V4  = R*dir(-150);
pair V5  = R*dir(150);

draw(circle(O,R), helppen);
draw(Vn--Vn1--Vn2--V3--V4--V5--cycle, mainpen);

// Local radial data.
draw(O--Vn, helppen);
draw(lineThrough(O,Vn1,0.80,0.25), axispen);
draw(O--Vn2, helppen);

// Two-step chord in the local window.
draw(Vn--Vn2, helppen);

markPointLabel("$O$", O, SW);
markPointLabel("$V_n$", Vn, N);
markPointLabel("$V_{n+1}$", Vn1, NE);
markPointLabel("$V_{n+2}$", Vn2, SE);
markPoint(V3);
markPoint(V4);
markPoint(V5);

label("$a_{n+1}$", -1.25*dir(30) + (-0.12,-0.12), SW);
label("two-step chord", midpoint(Vn,Vn2) + (-0.55,0.18), NW);
