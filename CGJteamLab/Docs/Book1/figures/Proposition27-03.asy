settings.outformat = "pdf";
size(11cm);

// Euclid I.27: second reductio branch.
// The two candidate lines meet beyond A and C at H.
//
// Orders on the two lines:
// H-A-E-B
// H-C-F-D

pair H = (-5.0, 0.0);

// First line through H.
pair E = (0.7,  1.45);
pair A = H + 0.46*(E-H);
pair B = E + 0.55*(E-H);

// Second line through H.
pair F = (0.1, -1.35);
pair C = H + 0.46*(F-H);
pair D = F + 0.55*(F-H);

// Main lines and transversal.
draw(H--B, linewidth(1.0));
draw(H--D, linewidth(1.0));
draw(E--F, linewidth(1.0));

// Points.
dot(H);
dot(A); dot(E); dot(B);
dot(C); dot(F); dot(D);

// Labels.
label("$H$", H, W);

label("$A$", A, NW);
label("$E$", E, N);
label("$B$", B, NE);

label("$C$", C, SW);
label("$F$", F, S);
label("$D$", D, SE);
