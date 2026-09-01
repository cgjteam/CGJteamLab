// Proposition2_1_three_part_split.asy
// Euclid Book II, Proposition 1: formal three-part rectangle split.
// ASCII-only Asymptote source.

settings.outformat = "pdf";
size(13cm,0);

defaultpen(fontsize(9pt));
pen mainpen = black + linewidth(0.85);
pen cutpen = black + linewidth(1.05);
pen auxpen = gray(0.48) + dashed + linewidth(0.65);
pen fill1 = gray(0.96);
pen fill2 = gray(0.90);

pair B=(0,0), M=(2.0,0), N=(4.5,0), C=(7.0,0);
pair D=(0,3.2), L=(2.0,3.2), K=(4.5,3.2), E=(7.0,3.2);
pair X=(2.0,3.2-(3.2/7.0)*2.0);
// Y is the intersection of L-C with N-K.
pair Y=(4.5,3.2-(3.2/5.0)*(4.5-2.0));

fill(B--M--L--D--cycle, fill1);
fill(M--N--K--L--cycle, fill2);
fill(N--C--E--K--cycle, fill1);

draw(B--C--E--D--cycle, mainpen);
draw(M--L, cutpen);
draw(N--K, cutpen);
draw(D--C, auxpen);
draw(L--C, auxpen);

dot(B); dot(M); dot(N); dot(C); dot(D); dot(L); dot(K); dot(E); dot(X); dot(Y);
label("$B$", B, SW);
label("$M$", M, S);
label("$N$", N, S);
label("$C$", C, SE);
label("$D$", D, NW);
label("$L$", L, N);
label("$K$", K, N);
label("$E$", E, NE);
label("$X$", X, SW);
label("$Y$", Y, NE);

label("$BMLD$", (0.9,0.42));
label("$MNKL$", (3.25,0.42));
label("$NCEK$", (5.75,2.45));
label("first cut $M-L$; second cut $N-K$", (3.5,-0.78), S);
