import graph;

size(11cm, 0);

pen mainpen = linewidth(0.9);
pen auxpen = linewidth(0.8) + dashed;
pen carrierpen = linewidth(0.45);
pen markpen = linewidth(0.8);

pair B=(0,0), C=(2,0), F=(4,0), G=(6,0);
pair A=(0.5,2.2), D=(2.5,2.2), E=(3.5,2.2), H=(5.5,2.2);

// Carriers for the two parallels.
draw((-0.25,0)--(6.25,0), carrierpen);
draw((0.25,2.2)--(5.75,2.2), carrierpen);

// Given parallelograms.
draw(A--B--C--D--cycle, mainpen);
draw(E--F--G--H--cycle, mainpen);

// Intermediate parallelogram constructed in the Lean proof.
draw(E--B--C--H--cycle, auxpen);

// Equal-base marks on BC and FG.
void baseMark(pair P, pair Q) {
  pair M=(P+Q)/2;
  pair v=unit(Q-P);
  pair n=(-v.y,v.x);
  draw(M-0.12*v-0.10*n -- M+0.08*v+0.10*n, markpen);
  draw(M+0.08*v-0.10*n -- M+0.28*v+0.10*n, markpen);
}
baseMark(B,C);
baseMark(F,G);

// Point labels.
label("$A$", A, NW);
label("$D$", D, N);
label("$E$", E, N);
label("$H$", H, NE);
label("$B$", B, SW);
label("$C$", C, SE);
label("$F$", F, SW);
label("$G$", G, SE);

label("$EBCH$", (2.75,1.08), fontsize(9));
