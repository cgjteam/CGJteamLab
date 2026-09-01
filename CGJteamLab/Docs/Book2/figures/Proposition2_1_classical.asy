// Proposition2_1_classical.asy
// Euclid Book II, Proposition 1: source-level three-part configuration.
// ASCII-only Asymptote source.

settings.outformat = "pdf";
size(13cm,0);

defaultpen(fontsize(9pt));
pen mainpen = black + linewidth(0.85);
pen cutpen = black + linewidth(1.0);
pen lightpen = gray(0.68) + linewidth(0.65);
pen fill1 = gray(0.96);
pen fill2 = gray(0.90);

// Divided side B-D-E-C.
pair B=(0,0), D=(2.0,0), E=(4.5,0), C=(7.0,0);
pair Bt=(0,3.1), Dt=(2.0,3.1), Et=(4.5,3.1), Ct=(7.0,3.1);

fill(B--D--Dt--Bt--cycle, fill1);
fill(D--E--Et--Dt--cycle, fill2);
fill(E--C--Ct--Et--cycle, fill1);

draw(B--C--Ct--Bt--cycle, mainpen);
draw(D--Dt, cutpen);
draw(E--Et, cutpen);

// Separate undivided straight line A, carrying the common transverse magnitude.
pair A0=(-2.1,0.3), A1=(-2.1,3.0);
draw(A0--A1, mainpen);
label("$A$", (A0+A1)/2, W);

// Matching qualitative tick on A and the rectangle height.
draw((-2.23,1.55)--(-1.97,1.55), lightpen);
draw((-0.13,1.55)--(0.13,1.55), lightpen);

// Base points and labels.
dot(B); dot(D); dot(E); dot(C);
label("$B$", B, SW);
label("$D$", D, S);
label("$E$", E, S);
label("$C$", C, SE);

label("$BD$", (B+D)/2+(0,0.30));
label("$DE$", (D+E)/2+(0,0.30));
label("$EC$", (E+C)/2+(0,0.30));
label("parallels through $D,E$", (3.5,3.55), N);
