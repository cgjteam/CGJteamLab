import markers;

settings.outformat = "pdf";
size(12cm);

// ------------------------------------------------------------
// Geometry
// ------------------------------------------------------------

pair A = (-3.8, 3.5);
pair B = (-5.0, 0);
pair C = (-0.9, 0);

// H genuinely lies between B and C.
real t = 0.55;
pair H = B + t*(C-B);

pair D = (2.3, 3.5);
pair E = (1.1, 0);
pair F = (5.2, 0);

// ------------------------------------------------------------
// Main figures
// ------------------------------------------------------------

draw(A--B--C--cycle, linewidth(1.0));
draw(D--E--F--cycle, linewidth(1.0));

// Auxiliary segment
draw(A--H, linewidth(0.8));

// ------------------------------------------------------------
// Points
// ------------------------------------------------------------

dot(A);
dot(B);
dot(C);
dot(H);

dot(D);
dot(E);
dot(F);

// ------------------------------------------------------------
// Labels
// ------------------------------------------------------------

label("$A$", A, N);
label("$B$", B, SW);
label("$H$", H, S);
label("$C$", C, SE);

label("$D$", D, N);
label("$E$", E, SW);
label("$F$", F, SE);

// ------------------------------------------------------------
// SAS angle
// ------------------------------------------------------------

// angle ABH ~= angle DEF
markangle(
  n=1,
  radius=14,
  H, B, A
);

markangle(
  n=1,
  radius=14,
  F, E, D
);

// ------------------------------------------------------------
// SAS side congruences
// ------------------------------------------------------------

// AB ~= DE
draw(
  A--B,
  p=linewidth(1.0),
  marker=StickIntervalMarker(i=1, n=1)
);

draw(
  D--E,
  p=linewidth(1.0),
  marker=StickIntervalMarker(i=1, n=1)
);

// BH ~= EF
draw(
  B--H,
  p=linewidth(1.0),
  marker=StickIntervalMarker(i=1, n=2)
);

draw(
  E--F,
  p=linewidth(1.0),
  marker=StickIntervalMarker(i=1, n=2)
);