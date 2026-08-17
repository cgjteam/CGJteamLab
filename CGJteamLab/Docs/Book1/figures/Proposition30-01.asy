settings.outformat = "pdf";
size(11cm);

// Euclid I.30: three distinct parallel lines.

pair A = (-4.0,  2.2);
pair B = ( 4.0,  2.2);

pair E = (-4.0,  0.0);
pair F = ( 4.0,  0.0);

pair C = (-4.0, -2.2);
pair D = ( 4.0, -2.2);

draw(A--B, linewidth(1.0));
draw(E--F, linewidth(1.0));
draw(C--D, linewidth(1.0));

dot(A); dot(B);
dot(C); dot(D);
dot(E); dot(F);

label("$A$", A, W);
label("$B$", B, E);

label("$E$", E, W);
label("$F$", F, E);

label("$C$", C, W);
label("$D$", D, E);

// Parallel marks.
draw((-2.8,2.08)--(-2.55,2.32), linewidth(0.8));
draw((-2.55,2.08)--(-2.30,2.32), linewidth(0.8));

draw((-0.2,-0.12)--(0.05,0.12), linewidth(0.8));
draw((0.05,-0.12)--(0.30,0.12), linewidth(0.8));

draw((2.3,-2.32)--(2.55,-2.08), linewidth(0.8));
draw((2.55,-2.32)--(2.80,-2.08), linewidth(0.8));
