import markers;

settings.outformat = "pdf";
size(12cm);

// ------------------------------------------------------------
// Geometry
// ------------------------------------------------------------

pair A = (-3.8, 3.5);
pair B = (-5.0, 0);
pair C = (-0.9, 0);

// G genuinely lies between B and A.
real t = 0.48;
pair G = B + t*(A-B);

pair D = (2.3, 3.5);
pair E = (1.1, 0);
pair F = (5.2, 0);

// ------------------------------------------------------------
// Main figures
// ------------------------------------------------------------

draw(A--B--C--cycle, linewidth(1.0));
draw(D--E--F--cycle, linewidth(1.0));

// Auxiliary segment
draw(G--C, linewidth(0.8));

// ------------------------------------------------------------
// Points
// ------------------------------------------------------------

dot(A);
dot(B);
dot(C);
dot(G);

dot(D);
dot(E);
dot(F);

// ------------------------------------------------------------
// Labels
// ------------------------------------------------------------

label("$A$", A, N);
label("$B$", B, SW);
label("$C$", C, SE);
label("$G$", G, W);

label("$D$", D, N);
label("$E$", E, SW);
label("$F$", F, SE);

// ------------------------------------------------------------
// SAS angle
// ------------------------------------------------------------

// angle GBC ~= angle DEF
markangle(
  n=1,
  radius=14,
  C, B, G
);

markangle(
  n=1,
  radius=14,
  F, E, D
);

// ------------------------------------------------------------
// SAS side congruences
// ------------------------------------------------------------

// GB ~= DE
draw(
  G--B,
  p=linewidth(1.0),
  marker=StickIntervalMarker(i=1, n=1)
);

draw(
  D--E,
  p=linewidth(1.0),
  marker=StickIntervalMarker(i=1, n=1)
);

// BC ~= EF
draw(
  B--C,
  p=linewidth(1.0),
  marker=StickIntervalMarker(i=1, n=2)
);

draw(
  E--F,
  p=linewidth(1.0),
  marker=StickIntervalMarker(i=1, n=2)
);