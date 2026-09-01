// Proposition2_2_mechanism.asy
// Euclid Book II, Proposition 2: configured II.1 cut used by Lean.
// ASCII-only Asymptote source.
settings.outformat = "pdf";
size(13cm,0);

pen mainpen = black + linewidth(0.9);
pen cutpen = black + linewidth(0.85);
pen dashpen = gray(0.45) + dashed + linewidth(0.65);
pen fillleft = gray(0.94);
pen fillright = gray(0.985);

pair B=(0,6), M=(2.4,6), C=(6,6);
pair D=(0,0), L=(2.4,0), E=(6,0);
pair X=(2.4,2.4);

fill(B--M--L--D--cycle, fillleft);
fill(M--C--E--L--cycle, fillright);

draw(B--C--E--D--cycle, mainpen);
draw(M--L, cutpen);
draw(D--C, dashpen);

dot(B); dot(M); dot(C); dot(D); dot(L); dot(E); dot(X);
label("$B$", B, NW);
label("$M$", M, N);
label("$C$", C, NE);
label("$D$", D, SW);
label("$L$", L, S);
label("$E$", E, SE);
label("$X$", X, E);

label("Rect(BM, BC)", (1.2,3.15));
label("Rect(MC, BC)", (4.2,3.15));
label("$B-M-C$", (3.0,6.70));
label("hidden diagonal witness $X$", (3.0,-0.70));
