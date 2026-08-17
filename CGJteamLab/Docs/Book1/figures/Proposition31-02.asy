settings.outformat = "pdf";
size(11cm);

// Euclid I.31 -- transversal AP, point E with A-E-P,
// and copied alternate angle at P.

pair A = (-3.4, 0.0);
pair B = ( 3.8, 0.0);
pair P = ( 1.6, 3.0);

// E lies strictly between A and P.
pair E = A + 0.55*(P-A);

// Constructed point Q chosen so that PQ is parallel to AB.
pair Q = P + (3.2, 0.0);

draw(A--B, linewidth(1.0));
draw(A--P, linewidth(1.0));
draw(P--Q, linewidth(1.0));

dot(A); dot(B); dot(E); dot(P); dot(Q);

label("$A$", A, SW);
label("$B$", B, SE);
label("$E$", E, NW);
label("$P$", P, N);
label("$Q$", Q, E);

// Mark angle EAB.
real aAE = degrees(atan2((E-A).y, (E-A).x));
draw(arc(A, 0.52, 0, aAE), linewidth(0.9));

// Mark angle EPQ.
real aPE = degrees(atan2((E-P).y, (E-P).x));
if (aPE < 0) aPE += 360;
draw(arc(P, 0.52, aPE, 360), linewidth(0.9));
