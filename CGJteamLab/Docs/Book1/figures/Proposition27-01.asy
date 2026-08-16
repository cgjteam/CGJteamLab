import markers;

settings.outformat = "pdf";
size(11cm);

// Euclid I.27: initial transversal configuration.
// A-E-B and C-F-D are collinear, and AB || CD.

pair A = (-4.2,  1.8);
pair E = (-1.2,  1.8);
pair B = ( 3.8,  1.8);

pair C = (-3.4, -1.8);
pair F = ( 0.0, -1.8);
pair D = ( 4.4, -1.8);

// Main lines and transversal.
draw(A--B, linewidth(1.0));
draw(C--D, linewidth(1.0));
draw(E--F, linewidth(1.0));

// Points.
dot(A); dot(E); dot(B);
dot(C); dot(F); dot(D);

// Labels.
label("$A$", A, W);
label("$E$", E, N);
label("$B$", B, E);

label("$C$", C, W);
label("$F$", F, S);
label("$D$", D, E);

// Equal alternate interior angles.
//
// At E, angle AEF is already the small interior angle.
markangle(
  n=1,
  radius=16,
  A, E, F
);

// At F we draw the intended small interior angle EFD explicitly.
// Using arc() avoids markangle choosing the reflex/exterior sector.
real r = 0.38;

real a1 = degrees(atan2((E-F).y, (E-F).x));
real a2 = degrees(atan2((D-F).y, (D-F).x));

// Normalize to the small counterclockwise sweep from FD to FE.
draw(arc(F, r, a2, a1), linewidth(0.9));
