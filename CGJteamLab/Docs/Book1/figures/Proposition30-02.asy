settings.outformat = "pdf";
size(11cm);

// Euclid I.30: classical proof configuration.
// Three parallel lines cut by one transversal.

pair A = (-4.0,  2.4);
pair G = (-1.8,  2.4);
pair B = ( 4.0,  2.4);

pair E = (-4.0,  0.0);
pair H = ( 0.0,  0.0);
pair F = ( 4.0,  0.0);

pair C = (-4.0, -2.4);
pair K = ( 1.8, -2.4);
pair D = ( 4.0, -2.4);

pair T1 = (-3.0,  4.0);
pair T2 = ( 3.0, -4.0);

// Three parallel lines.
draw(A--B, linewidth(1.0));
draw(E--F, linewidth(1.0));
draw(C--D, linewidth(1.0));

// Transversal.
draw(T1--T2, linewidth(1.0));

// Points.
dot(A); dot(G); dot(B);
dot(E); dot(H); dot(F);
dot(C); dot(K); dot(D);

// Labels.
label("$A$", A, W);
label("$G$", G, N);
label("$B$", B, E);

label("$E$", E, W);
label("$H$", H, N);
label("$F$", F, E);

label("$C$", C, W);
label("$K$", K, S);
label("$D$", D, E);

// Parallel marks on the three horizontal lines.
draw((-3.0,2.28)--(-2.75,2.52), linewidth(0.8));
draw((-2.75,2.28)--(-2.50,2.52), linewidth(0.8));

draw((-0.2,-0.12)--(0.05,0.12), linewidth(0.8));
draw((0.05,-0.12)--(0.30,0.12), linewidth(0.8));

draw((2.3,-2.52)--(2.55,-2.28), linewidth(0.8));
draw((2.55,-2.52)--(2.80,-2.28), linewidth(0.8));
