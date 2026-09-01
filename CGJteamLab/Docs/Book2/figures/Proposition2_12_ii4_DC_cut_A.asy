// Proposition2_12_ii4_DC_cut_A.asy
// Euclid Book II, Proposition 12.
// Proposition II.4 applied to DC cut at A.
// ASCII-only Asymptote source.

settings.outformat = "pdf";
size(13cm,0);
defaultpen(fontsize(9.5pt));

pen mainpen = linewidth(0.85);
pen cutpen = linewidth(1.05);
pen dashpen = dashed + linewidth(0.65);

// Outer square on DC.  D-A-C is the top side.
pair D=(0,6), A=(2.25,6), C=(6,6);
pair P=(0,0), F=(2.25,0), Q=(6,0);
pair G=(2.25,2.25), H=(0,2.25), K=(6,2.25);

// Outer square, Euclid's diagonal, and the two cuts determined by A and G.
draw(D--C--Q--P--cycle, mainpen);
draw(C--P, dashpen);
draw(A--F, cutpen);
draw(H--K, cutpen);

// Right-angle mark at D.
draw((0.28,6)--(0.28,5.72)--(0,5.72), linewidth(0.6));

// Source points on the divided side and the diagonal intersection.
dot(D); dot(A); dot(C); dot(G);
label("$D$", D, NW);
label("$A$", A, N);
label("$C$", C, NE);
label("$G$", G, NE);

// The four visible content regions.
label("$\mathrm{Rect}(DA,AC)$", (1.10,4.15));
label("$\mathrm{Sq}(AC)$", (4.20,4.15));
label("$\mathrm{Sq}(DA)$", (1.10,1.05));
label("$\mathrm{Rect}(DA,AC)$", (4.20,1.05));

label("$D-A-C$", (3.0,6.55), N);
