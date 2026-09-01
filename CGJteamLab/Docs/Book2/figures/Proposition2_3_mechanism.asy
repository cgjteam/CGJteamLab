// Proposition2_3_mechanism.asy
// Euclid Book II, Proposition 3: configured Lean / II.1 cut.
// ASCII-only Asymptote source.

settings.outformat = "pdf";
size(13cm,0);

defaultpen(fontsize(9pt)+black);
pen mainpen = linewidth(0.85);
pen cutpen = linewidth(1.05);
pen dashpen = dashed + linewidth(0.65);
pen squarepen = linewidth(0.85);
pen leftfill = gray(0.95);
pen rightfill = gray(0.90);

// B-M-C is the top side of the configured outer rectangle.
// MC and CE have the same magnitude.
pair B=(0,0), M=(2.4,0), C=(6,0);
pair D=(0,-3.6), L=(2.4,-3.6), E=(6,-3.6);
pair X=(2.4,-2.16);

// Supplied square MCFG is deliberately separate from the internal right piece.
pair F=(6,3.6), G=(2.4,3.6);

fill(B--M--L--D--cycle, leftfill);
fill(M--C--E--L--cycle, rightfill);

draw(B--C--E--D--cycle, mainpen);
draw(M--L, cutpen);
draw(D--C, dashpen);
draw(M--C--F--G--cycle, squarepen);

dot(B); dot(M); dot(C); dot(D); dot(L); dot(E); dot(X); dot(F); dot(G);
label("$B$", B, NW);
label("$M$", M, NW);
label("$C$", C, NE);
label("$D$", D, SW);
label("$L$", L, S);
label("$E$", E, SE);
label("$X$", X, E);
label("$F$", F, NE);
label("$G$", G, NW);

label("$\mathrm{Rect}(BM,MC)$", (1.2,-1.55));
label("internal $\mathrm{Rect}(MC,MC)$", (4.2,-1.55));
label("supplied $\mathrm{Sq}(MC)$", (4.2,1.75));
label("$CE\cong MC$", (6,-1.8), E);
label("$B-M-C$", (1.2,0.48));
