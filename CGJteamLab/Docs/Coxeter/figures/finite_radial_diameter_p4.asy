// finite_radial_diameter_p4.asy
// Diameter branch forced by the square case p=4.

import CoxeterFiguresCommon;

size(10cm);

pair O   = (0,0);
real R = 2.8;

pair Vn  = R*dir(135);
pair Vn1 = R*dir(45);
pair Vn2 = R*dir(-45);
pair Vn3 = R*dir(-135);

draw(circle(O,R), helppen);
draw(Vn--Vn1--Vn2--Vn3--cycle, mainpen);

// Previous and next radial carriers coincide with the diameter Vn--Vn2.
draw(lineThrough(Vn,Vn2,0.16,0.16), axispen);

// The middle carrier is perpendicular to that diameter.
draw(lineThrough(O,Vn1,0.90,0.22), axispen);

// Right-angle marker at O.
pair u = unit(Vn-O);
pair v = unit(Vn1-O);
real s = 0.34;
draw(O+s*u -- O+s*u+s*v -- O+s*v, mainpen);

markPoint(Vn);
markPoint(Vn1);
markPoint(Vn2);
markPoint(Vn3);
dot(O);

label("$V_n$", Vn, NW);
label("$V_{n+1}$", Vn1, NE);
label("$V_{n+2}$", Vn2, SE);
label("$V_{n+3}$", Vn3, SW);
label("$O=M$", O + (0,-0.28), S);

label("$a_n=a_{n+2}$", midpoint(Vn,O) + (-0.35,0.18), NW);
label("$a_{n+1}$", midpoint(O,Vn1) + (0.25,0.12), NE);
