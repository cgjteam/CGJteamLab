// Proposition2_2_mechanism.asy
// Euclid Book II, Proposition 2.
// ASCII-only Asymptote source.

settings.outformat = "pdf";
size(15cm,0);

pen mainpen = linewidth(0.8);
pen cutpen = linewidth(1.0);
pen dashpen = dashed + linewidth(0.65);
pen lightpen = gray(0.55) + linewidth(0.7);

pair B=(0,4), C=(6,4), E=(6,0), D=(0,0);
pair M=(2.4,4), L=(2.4,0);
pair X=(2.4,1.6);

draw(B--C--E--D--cycle, mainpen);
draw(M--L, cutpen);
draw(D--C, dashpen);

dot(B); dot(C); dot(D); dot(E); dot(M); dot(L); dot(X);
label("$B$", B, NW);
label("$C$", C, NE);
label("$E$", E, SE);
label("$D$", D, SW);
label("$M$", M, N);
label("$L$", L, S);
label("$X$", X, E);

label("(a) square cut used by II.2", (3,-0.75));

pair shift=(9.0,0.4);
pair V0=shift+(0,0), V1=shift+(3.2,0), V2=shift+(3.2,2.4), V3=shift+(0,2.4);

draw(V0--V1--V2--V3--cycle, mainpen);
dot(V0); dot(V1); dot(V2); dot(V3);
label("$V_0$", V0, SW);
label("$V_1$", V1, SE);
label("$V_2$", V2, NE);
label("$V_3$", V3, NW);

draw(V0--V1, linewidth(1.15));
draw(V1--V2, lightpen);
label("first side", (V0+V1)/2, S);
label("second side", (V1+V2)/2, E);

pair a=shift+(0.5,3.1), b=shift+(2.7,3.1);
draw(a--b, lightpen, Arrow(TeXHead));
label("$V_0V_1V_2V_3\;\longmapsto\;V_1V_2V_3V_0$", shift+(1.6,3.55));

label("(b) cyclic representative rotation", shift+(1.6,-0.75));
