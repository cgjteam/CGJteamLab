// Proposition2_5_db_split.asy
// Euclid Book II, Proposition 5.
// Formal state: II.1 splits DB at C with AD as the fixed side.
// ASCII-only Asymptote source.

settings.outformat = "pdf";
size(13cm,0);
defaultpen(fontsize(9pt)+black);

pen mainpen = linewidth(0.85);
pen cutpen = linewidth(1.05);
pen auxpen = gray(0.55)+linewidth(0.65);

pair A=(0,0), D=(1.8,0), C=(3.6,0), B=(7.2,0);
real h=1.8; // diagrammatic height, chosen equal to AD
pair E=(1.8,h), L=(3.6,h), H=(7.2,h);

// Rect(DB,AD), split at C.
fill(D--C--L--E--cycle, gray(0.92));
fill(C--B--H--L--cycle, gray(0.96));
draw(D--B--H--E--cycle, mainpen);
draw(C--L, cutpen);

// The segment AD is shown as the fixed-side magnitude.
draw(A--D, auxpen);
draw((0.9,-0.11)--(0.9,0.11), linewidth(0.65));
draw((1.68,0.90)--(1.92,0.90), linewidth(0.65));

for (pair P : new pair[] {A,D,C,B,E,L,H}) dot(P);
label("$A$",A,S); label("$D$",D,S); label("$C$",C,S); label("$B$",B,S);
label("$E$",E,NW); label("$L$",L,N); label("$H$",H,NE);

label("$\mathrm{Rect}(DC,AD)$", (2.7,0.9));
label("$\mathrm{Rect}(CB,AD)$", (5.4,0.9));
label("$\mathrm{Rect}(DB,AD)$", (4.5,2.08));
label("fixed side $AD$", (0.9,-0.45));
