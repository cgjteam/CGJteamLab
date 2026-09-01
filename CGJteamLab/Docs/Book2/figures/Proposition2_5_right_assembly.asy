// Proposition2_5_right_assembly.asy
// Euclid Book II, Proposition 5.
// Formal state: II.1 assembles the two right-hand rectangles on AC cut at D.
// The midpoint congruence then makes the whole rectangle square-shaped.
// ASCII-only Asymptote source.

settings.outformat = "pdf";
size(13cm,0);
defaultpen(fontsize(9pt)+black);

pen mainpen = linewidth(0.85);
pen cutpen = linewidth(1.05);
pen auxpen = gray(0.55)+linewidth(0.65);

// Formal order A-D-C-B with AC ~= CB.
pair A=(0,0), D=(2.0,0), C=(4,0), B=(8,0);
real h=4.0; // diagrammatic height chosen equal to AC and CB
pair E=(0,h), L=(2.0,h), H=(4,h);

fill(A--D--L--E--cycle, gray(0.94));
fill(D--C--H--L--cycle, gray(0.89));
draw(A--C--H--E--cycle, mainpen);
draw(D--L, cutpen);

// Baseline continuation records CB, congruent to AC.
draw(C--B, auxpen);
draw((1.0,-0.11)--(1.0,0.11), linewidth(0.65));
draw((6.0,-0.11)--(6.0,0.11), linewidth(0.65));

// Equal adjacent-side marks show why the assembled whole is square-shaped.
draw((-0.11,2.0)--(0.11,2.0), linewidth(0.65));

for (pair P : new pair[] {A,D,C,B,E,L,H}) dot(P);
label("$A$",A,S); label("$D$",D,S); label("$C$",C,S); label("$B$",B,S);
label("$E$",E,NW); label("$L$",L,N); label("$H$",H,NE);

label("$\mathrm{Rect}(AD,CB)$", (1.0,2.0));
label("$\mathrm{Rect}(DC,CB)$", (3.0,2.0));
label("$\mathrm{Rect}(AC,CB)$", (2.0,4.42));
label("$AC\cong CB$", (6.0,0.42));
label("square-shaped whole", (2.0,-0.55));
