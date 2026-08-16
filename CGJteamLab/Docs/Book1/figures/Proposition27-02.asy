settings.outformat = "pdf";
size(11cm);

// Euclid I.27: first reductio branch.
// The two candidate lines meet beyond B and D at G.
//
// Orders on the two lines:
// A-E-B-G
// C-F-D-G

pair G = (5.0, 0.0);

// First line through G.
pair E = (-0.9,  1.55);
pair v1 = E-G;
pair A = E + 0.55*v1;
pair B = E + 0.58*(G-E);

// Second line through G.
pair F = (-0.2, -1.35);
pair v2 = F-G;
pair C = F + 0.55*v2;
pair D = F + 0.58*(G-F);

// Main lines and transversal.
draw(A--G, linewidth(1.0));
draw(C--G, linewidth(1.0));
draw(E--F, linewidth(1.0));

// Points.
dot(A); dot(E); dot(B);
dot(C); dot(F); dot(D);
dot(G);

// Labels.
label("$A$", A, NW);
label("$E$", E, N);
label("$B$", B, NE);

label("$C$", C, SW);
label("$F$", F, S);
label("$D$", D, SE);

label("$G$", G, E);
