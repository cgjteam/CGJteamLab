// Proposition2_4_II2_outer_split.asy
// Euclid Book II, Proposition 4: the II.2 outer decomposition used by Lean.
// ASCII-only Asymptote source.

settings.outformat = "pdf";
size(12.5cm,0);
defaultpen(fontsize(9pt)+black);

pen mainpen = linewidth(0.9);
pen cutpen = linewidth(1.0);
pen auxpen = gray(0.60) + linewidth(0.65);

pair A=(0,4.8), C=(2.0,4.8), B=(6.0,4.8);
pair D=(0,0), L=(2.0,0), E=(6.0,0);

fill(A--C--L--D--cycle, gray(0.94));
fill(C--B--E--L--cycle, gray(0.985));

draw(A--B--E--D--cycle, mainpen);
draw(C--L, cutpen);

// Small right-angle marker at A: this is the supplied square on AB.
draw((0.28,4.8)--(0.28,4.52)--(0,4.52), auxpen);

dot(A); dot(C); dot(B); dot(D); dot(L); dot(E);
label("$A$", A, NW);
label("$C$", C, N);
label("$B$", B, NE);
label("$D$", D, SW);
label("$L$", L, S);
label("$E$", E, SE);

label("$\mathrm{Rect}(AB,AC)$", (1.0,2.35));
label("$\mathrm{Rect}(AB,CB)$", (4.0,2.35));
label("$A-C-B$", (3.0,5.35));
label("II.2 outer split", (3.0,-0.55));
