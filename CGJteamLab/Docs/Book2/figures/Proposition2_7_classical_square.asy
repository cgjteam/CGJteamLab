// Proposition2_7_classical_square.asy
// Euclid Book II, Proposition 7: classical square/diagonal construction.
// ASCII-only source.

settings.outformat = "pdf";
size(12.5cm,0);
defaultpen(fontsize(10pt));

pen mainpen = black+0.9bp;
pen auxpen = black+0.6bp;
pen dashpen = gray(0.55)+0.55bp+dashed;
pen fillA = gray(0.94);
pen fillB = gray(0.88);

// Square ABED with arbitrary cut A-C-B.
pair A=(0,6), C=(2.3,6), B=(6,6);
pair D=(0,0), F=(2.3,0), E=(6,0);
pair G=(2.3,2.3), H=(0,2.3), K=(6,2.3);

// Light emphasis of the two complementary rectangles around the diagonal.
fill(A--C--G--H--cycle, fillA);
fill(G--K--E--F--cycle, fillA);
fill(C--B--K--G--cycle, fillB);
fill(H--G--F--D--cycle, fillB);

// Classical carriers.
draw(A--B--E--D--cycle, mainpen);
draw(B--D, dashpen);
draw(C--F, auxpen);
draw(H--K, auxpen);

// Right angle at A.
draw((0.28,6)--(0.28,5.72)--(0,5.72), black+0.55bp);

// Points.
for(pair P : new pair[] {A,C,B,D,F,E,G,H,K}) dot(P, black);
label("$A$", A, NW);
label("$C$", C, N);
label("$B$", B, NE);
label("$D$", D, SW);
label("$F$", F, S);
label("$E$", E, SE);
label("$G$", G, NE);
label("$H$", H, W);
label("$K$", K, E);

label("$A-C-B$", (3,6.55), N);
label("diagonal $BD$", (4.35,4.1), NE);
label("parallels through $C$ and $G$", (3,-0.55), S);
