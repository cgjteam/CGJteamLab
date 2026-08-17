import markers;

settings.outformat = "pdf";
size(11cm);

// Euclid I.29: base configuration.

pair A = (-4.2,  1.8);
pair G = (-1.0,  1.8);
pair B = ( 3.8,  1.8);

pair C = (-3.6, -1.8);
pair H = ( 0.7, -1.8);
pair D = ( 4.4, -1.8);

pair E = (-2.1,  4.0);
pair F = ( 1.8, -4.0);

draw(A--B, linewidth(1.0));
draw(C--D, linewidth(1.0));
draw(E--F, linewidth(1.0));

dot(A); dot(G); dot(B);
dot(C); dot(H); dot(D);
dot(E); dot(F);

label("$A$", A, W);
label("$G$", G, N);
label("$B$", B, E);
label("$C$", C, W);
label("$H$", H, S);
label("$D$", D, E);
label("$E$", E, NW);
label("$F$", F, SE);

// Parallel marks.
draw((-3.0,1.68)--(-2.75,1.92), linewidth(0.8));
draw((-2.75,1.68)--(-2.50,1.92), linewidth(0.8));

draw((-2.4,-1.92)--(-2.15,-1.68), linewidth(0.8));
draw((-2.15,-1.92)--(-1.90,-1.68), linewidth(0.8));
