// Proposition2_5_left_II3.asy
// Euclid Book II, Proposition 5.
// Formal state: II.3 on AC cut at D, with midpoint transport AC ~= CB.
// ASCII-only Asymptote source.

settings.outformat = "pdf";
size(13cm,0);
defaultpen(fontsize(9pt)+black);

pen mainpen = linewidth(0.85);
pen cutpen = linewidth(1.05);
pen auxpen = gray(0.55)+linewidth(0.65);

// Formal baseline order A-D-C-B.  AC and CB are drawn congruent.
pair A=(0,0), D=(2.2,0), C=(4,0), B=(8,0);
real h=1.8; // diagrammatic height, chosen equal to DC
pair E=(0,h), L=(2.2,h), H=(4,h);

// Exact II.3 cut of Rect(AC,DC).
fill(A--D--L--E--cycle, gray(0.95));
fill(D--C--H--L--cycle, gray(0.89));
draw(A--C--H--E--cycle, mainpen);
draw(D--L, cutpen);

// Baseline continuation records the midpoint half CB.
draw(C--B, auxpen);

// Equal-half marks for AC ~= CB (documentary only).
draw((1.15,-0.11)--(1.15,0.11), linewidth(0.65));
draw((6.0,-0.11)--(6.0,0.11), linewidth(0.65));

// Right-angle marker at D: the right cut piece has sides DC and DC.
draw((2.2,0.25)--(2.45,0.25)--(2.45,0), linewidth(0.55));

// Points and labels.
for (pair P : new pair[] {A,D,C,B,E,L,H}) dot(P);
label("$A$",A,S); label("$D$",D,S); label("$C$",C,S); label("$B$",B,S);
label("$E$",E,NW); label("$L$",L,N); label("$H$",H,NE);

label("$\mathrm{Rect}(AD,DC)$", (1.1,0.9));
label("$\mathrm{Sq}(DC)$", (3.1,0.9));
label("$AC\cong CB$", (6.0,0.42));
label("$\mathrm{Rect}(AC,DC)$", (2.0,2.08));
