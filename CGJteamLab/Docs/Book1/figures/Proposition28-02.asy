import markers;

settings.outformat = "pdf";
size(11cm);

// Euclid I.28A: corresponding angles.
// Explicit arcs are used so that the intended sectors are always drawn.

pair A = (-4.2,  1.8);
pair G = (-1.0,  1.8);
pair B = ( 3.8,  1.8);

pair C = (-3.6, -1.8);
pair H = ( 0.7, -1.8);
pair D = ( 4.4, -1.8);

pair E = (-2.1,  4.0);
pair F = ( 1.8, -4.0);

draw(A--B, linewidth(1.0));
draw(C--D, linewidth(1.0));
draw(E--F, linewidth(1.0));

dot(A); dot(G); dot(B);
dot(C); dot(H); dot(D);
dot(E); dot(F);

label("$A$", A, W);
label("$G$", G, N);
label("$B$", B, E);

label("$C$", C, W);
label("$H$", H, S);
label("$D$", D, E);

label("$E$", E, NW);
label("$F$", F, SE);

// Direction angles of the relevant rays.
real aGE = degrees(atan2((E-G).y, (E-G).x));
real aGH = degrees(atan2((H-G).y, (H-G).x));
real aHG = degrees(atan2((G-H).y, (G-H).x));

// Radii.
real r1 = 0.38;
real r2 = 0.52;

// angle EGB: intended exterior angle above AB at G.
// Ray GB has direction 0 degrees.
draw(arc(G, r1, 0, aGE), linewidth(0.9));

// angle GHD: intended interior/opposite angle above CD at H.
// Ray HD has direction 0 degrees.
draw(arc(H, r1, 0, aHG), linewidth(0.9));

// angle AGH: vertical to EGB, below AB at G.
// Ray GA has direction 180 degrees.
// Convert the negative direction of GH to its equivalent in [0,360).
real aGHpos = aGH;
if (aGHpos < 0) aGHpos += 360;

// Draw it with a second concentric arc to distinguish the derived angle.
draw(arc(G, r2, 180, aGHpos), linewidth(0.9));
draw(arc(G, r2+0.09, 180, aGHpos), linewidth(0.9));
