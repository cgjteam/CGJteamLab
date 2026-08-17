settings.outformat = "pdf";
size(11cm);

// Euclid I.31 -- final configuration.
// Proposition I.27 gives AB || PQ.

pair A = (-3.8, 0.0);
pair B = ( 3.8, 0.0);
pair P = (-1.2, 3.0);
pair Q = ( 4.0, 3.0);

draw(A--B, linewidth(1.0));
draw(P--Q, linewidth(1.0));

dot(A); dot(B); dot(P); dot(Q);

label("$A$", A, SW);
label("$B$", B, SE);
label("$P$", P, NW);
label("$Q$", Q, NE);

// Matching parallel marks.
draw((-1.4,-0.12)--(-1.15,0.12), linewidth(0.8));
draw((-1.15,-0.12)--(-0.90,0.12), linewidth(0.8));

draw((0.8,2.88)--(1.05,3.12), linewidth(0.8));
draw((1.05,2.88)--(1.30,3.12), linewidth(0.8));
