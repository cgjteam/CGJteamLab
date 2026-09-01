// Proposition2_2_classical.asy
// Euclid Book II, Proposition 2: classical square split.
// ASCII-only Asymptote source.
settings.outformat = "pdf";
size(13cm,0);

pen mainpen = black + linewidth(0.9);
pen cutpen = black + linewidth(0.8);
pen auxpen = gray(0.55) + linewidth(0.65);
pen fillleft = gray(0.94);
pen fillright = gray(0.985);

pair A=(0,6), C=(2.4,6), B=(6,6);
pair D=(0,0), F=(2.4,0), E=(6,0);

fill(A--C--F--D--cycle, fillleft);
fill(C--B--E--F--cycle, fillright);

draw(A--B--E--D--cycle, mainpen);
draw(C--F, cutpen);

// Small right-angle cue at A.
draw((0.28,6)--(0.28,5.72)--(0,5.72), auxpen);

dot(A); dot(B); dot(C); dot(D); dot(E); dot(F);
label("$A$", A, NW);
label("$C$", C, N);
label("$B$", B, NE);
label("$D$", D, SW);
label("$F$", F, S);
label("$E$", E, SE);

label("Rect(AB, AC)", (1.2,3.0));
label("Rect(AB, CB)", (4.2,3.0));
label("$A-C-B$", (3.0,6.70));
label("parallel through $C$", (2.4,-0.65));
