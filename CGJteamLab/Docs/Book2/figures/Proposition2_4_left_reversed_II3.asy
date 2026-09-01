// Proposition2_4_left_reversed_II3.asy
// Euclid Book II, Proposition 4: reversed II.3 branch B-C-A.
// ASCII-only Asymptote source.

settings.outformat = "pdf";
size(12.5cm,0);
defaultpen(fontsize(9pt)+black);

pen mainpen = linewidth(0.9);
pen cutpen = linewidth(1.0);
pen auxpen = gray(0.60) + linewidth(0.65);
pen squarepen = linewidth(1.0);

// Reverse orientation: B-C-A.  The fixed height is CA.
pair B=(0,3.0), C=(3.6,3.0), A=(6.0,3.0);
pair D=(0,0.6), L=(3.6,0.6), E=(6.0,0.6);

fill(B--C--L--D--cycle, gray(0.96));
fill(C--A--E--L--cycle, gray(0.90));

draw(B--A--E--D--cycle, mainpen);
draw(C--L, cutpen);

// Mark the right piece as the square on CA.
draw(C--A--E--L--cycle, squarepen);
draw((3.82,3.0)--(3.82,2.78)--(3.6,2.78), auxpen);

dot(B); dot(C); dot(A); dot(D); dot(L); dot(E);
label("$B$", B, NW);
label("$C$", C, N);
label("$A$", A, NE);
label("$D$", D, SW);
label("$L$", L, S);
label("$E$", E, SE);

label("$\mathrm{Rect}(BC,CA)$", (1.8,1.72));
label("$\mathrm{Sq}(CA)$", (4.8,1.72));
label("$B-C-A$", (3.0,3.55));
label("reversed II.3", (3.0,0.0));
