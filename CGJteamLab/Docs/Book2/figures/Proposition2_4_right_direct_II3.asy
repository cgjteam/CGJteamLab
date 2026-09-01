// Proposition2_4_right_direct_II3.asy
// Euclid Book II, Proposition 4: direct II.3 branch A-C-B.
// ASCII-only Asymptote source.

settings.outformat = "pdf";
size(12.5cm,0);
defaultpen(fontsize(9pt)+black);

pen mainpen = linewidth(0.9);
pen cutpen = linewidth(1.0);
pen auxpen = gray(0.60) + linewidth(0.65);
pen squarepen = linewidth(1.0);

// Direct orientation: A-C-B.  The fixed height is CB.
pair A=(0,4.0), C=(2.4,4.0), B=(6.0,4.0);
pair D=(0,0.4), L=(2.4,0.4), E=(6.0,0.4);

fill(A--C--L--D--cycle, gray(0.96));
fill(C--B--E--L--cycle, gray(0.90));

draw(A--B--E--D--cycle, mainpen);
draw(C--L, cutpen);

// Mark the right piece as the square on CB.
draw(C--B--E--L--cycle, squarepen);
draw((2.64,4.0)--(2.64,3.76)--(2.4,3.76), auxpen);

dot(A); dot(C); dot(B); dot(D); dot(L); dot(E);
label("$A$", A, NW);
label("$C$", C, N);
label("$B$", B, NE);
label("$D$", D, SW);
label("$L$", L, S);
label("$E$", E, SE);

label("$\mathrm{Rect}(AC,CB)$", (1.2,2.16));
label("$\mathrm{Sq}(CB)$", (4.2,2.16));
label("$A-C-B$", (3.0,4.55));
label("direct II.3", (3.0,-0.18));
