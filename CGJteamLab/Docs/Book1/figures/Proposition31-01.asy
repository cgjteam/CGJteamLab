settings.outformat = "pdf";
size(11cm);

// Euclid I.31 -- given line AB and external point P.

pair A = (-4.0, 0.0);
pair B = ( 4.0, 0.0);
pair P = ( 1.4, 3.0);

draw(A--B, linewidth(1.0));

dot(A); dot(B); dot(P);

label("$A$", A, SW);
label("$B$", B, SE);
label("$P$", P, N);
