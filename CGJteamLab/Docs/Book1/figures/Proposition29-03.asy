import markers;

settings.outformat = "pdf";
size(11cm);

// Euclid I.29: corresponding angles.

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

real aGE = degrees(atan2((E-G).y,(E-G).x));
real aHG = degrees(atan2((G-H).y,(G-H).x));
real r = 0.42;

// angle EGB
draw(arc(G,r,0,aGE), linewidth(0.9));

// angle GHD
draw(arc(H,r,0,aHG), linewidth(0.9));
