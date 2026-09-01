// Proposition2_1_binary_split.asy
// Euclid Book II, Proposition 1: formal binary rectangle split.
// ASCII-only Asymptote source.

settings.outformat = "pdf";
size(12cm,0);

defaultpen(fontsize(9pt));
pen mainpen = black + linewidth(0.85);
pen cutpen = black + linewidth(1.05);
pen auxpen = gray(0.48) + dashed + linewidth(0.65);
pen fill1 = gray(0.96);
pen fill2 = gray(0.90);

pair B=(0,0), M=(2.4,0), C=(6.0,0);
pair D=(0,3.2), L=(2.4,3.2), E=(6.0,3.2);
// X lies on D-C and M-L.
pair X=(2.4,3.2-(3.2/6.0)*2.4);

fill(B--M--L--D--cycle, fill1);
fill(M--C--E--L--cycle, fill2);

draw(B--C--E--D--cycle, mainpen);
draw(M--L, cutpen);
draw(D--C, auxpen);

dot(B); dot(M); dot(C); dot(D); dot(L); dot(E); dot(X);
label("$B$", B, SW);
label("$M$", M, S);
label("$C$", C, SE);
label("$D$", D, NW);
label("$L$", L, N);
label("$E$", E, NE);
label("$X$", X, E);

label("$BMLD$", (1.1,0.45));
label("$MCEL$", (4.2,0.45));
label("$B-M-C$", (3.0,-0.72), S);
