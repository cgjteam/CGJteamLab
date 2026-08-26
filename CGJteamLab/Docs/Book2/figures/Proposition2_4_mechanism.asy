// Proposition2_4_mechanism.asy
// Euclid Book II, Proposition 4.
// ASCII-only Asymptote source.

settings.outformat = "pdf";
size(13cm,0);

pen mainpen = linewidth(0.85);
pen cutpen = linewidth(1.05);
pen dashpen = dashed + linewidth(0.65);

// Classical Heath configuration: AB is the top side of square ADEB.
pair A=(0,6), C=(2.25,6), B=(6,6);
pair D=(0,0), F=(2.25,0), E=(6,0);
pair G=(2.25,2.25), H=(0,2.25), K=(6,2.25);

// Outer square and Euclid's auxiliary lines.
draw(A--B--E--D--cycle, mainpen);
draw(B--D, dashpen);
draw(C--F, cutpen);
draw(H--K, cutpen);

// Right-angle mark at A.
draw((0.28,6)--(0.28,5.72)--(0,5.72), linewidth(0.6));

// Points.
dot(A); dot(B); dot(C); dot(D); dot(E); dot(F); dot(G); dot(H); dot(K);
label("$A$", A, NW);
label("$C$", C, N);
label("$B$", B, NE);
label("$D$", D, SW);
label("$F$", F, S);
label("$E$", E, SE);
label("$G$", G, NE);
label("$H$", H, W);
label("$K$", K, E);

// Euclid's names for the four subfigures.
label("$AG$", (1.0,4.15));
label("$CK$", (4.35,4.15));
label("$HF$", (1.0,1.05));
label("$GE$", (4.35,1.05));
