// Proposition2_3_classical.asy
// Euclid Book II, Proposition 3: classical source configuration.
// ASCII-only Asymptote source.

settings.outformat = "pdf";
size(13cm,0);

defaultpen(fontsize(9pt)+black);
pen mainpen = linewidth(0.85);
pen cutpen = linewidth(1.05);
pen lightfill = gray(0.94);

// Classical roles: A-C-B on the top side.  CDEB is the square on CB.
pair A=(0,3.8), C=(2.4,3.8), B=(6.0,3.8);
pair F=(0,0), D=(2.4,0), E=(6.0,0);

// Larger rectangle ABEF, with the square CDEB on the right.
fill(A--C--D--F--cycle, lightfill);
draw(A--B--E--F--cycle, mainpen);
draw(C--D, cutpen);

// Emphasize the square on CB without adding a second geometric state.
draw(C--B--E--D--cycle, mainpen);

// Equal-side marks for the square: CB = CD qualitatively.
real mx=(C.x+B.x)/2;
draw((mx,3.68)--(mx,3.92), linewidth(0.55));
real my=(C.y+D.y)/2;
draw((2.28,my)--(2.52,my), linewidth(0.55));

dot(A); dot(C); dot(B); dot(F); dot(D); dot(E);
label("$A$", A, NW);
label("$C$", C, N);
label("$B$", B, NE);
label("$F$", F, SW);
label("$D$", D, S);
label("$E$", E, SE);

label("$A-C-B$", (3.0,4.38));
label("$\mathrm{Rect}(AC,CB)$", (1.2,1.9));
label("$\mathrm{Sq}(CB)$", (4.2,1.9));
label("square $CDEB$ on $CB$", (4.2,-0.62));
