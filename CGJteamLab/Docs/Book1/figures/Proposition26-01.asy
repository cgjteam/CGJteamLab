import markers;

settings.outformat = "pdf";
size(12cm);

// ------------------------------------------------------------
// Geometry
// ------------------------------------------------------------

pair A = (-3.8, 3.5);
pair B = (-5.0, 0);
pair C = (-0.9, 0);

pair D = (2.3, 3.5);
pair E = (1.1, 0);
pair F = (5.2, 0);

// ------------------------------------------------------------
// Main figures
// ------------------------------------------------------------

draw(A--B--C--cycle, linewidth(1.0));
draw(D--E--F--cycle, linewidth(1.0));

// ------------------------------------------------------------
// Points
// ------------------------------------------------------------

dot(A);
dot(B);
dot(C);

dot(D);
dot(E);
dot(F);

// ------------------------------------------------------------
// Labels
// ------------------------------------------------------------

label("$A$", A, N);
label("$B$", B, SW);
label("$C$", C, SE);

label("$D$", D, N);
label("$E$", E, SW);
label("$F$", F, SE);

// ------------------------------------------------------------
// Angle congruence classes
// ------------------------------------------------------------

// angle ABC ~= angle DEF
// First angle class: one arc.
markangle(
  n=1,
  radius=14,
  C, B, A
);

markangle(
  n=1,
  radius=14,
  F, E, D
);

// angle BCA ~= angle EFD
// Second angle class: two arcs.
markangle(
  n=2,
  radius=14,
  A, C, B
);

markangle(
  n=2,
  radius=14,
  D, F, E
);

// ------------------------------------------------------------
// Segment congruence class
// ------------------------------------------------------------

// BC ~= EF
// One tick.
draw(
  B--C,
  p=linewidth(1.0),
  marker=StickIntervalMarker(i=1, n=1)
);

draw(
  E--F,
  p=linewidth(1.0),
  marker=StickIntervalMarker(i=1, n=1)
);