import graph;

size(14cm, 0);

pen mainpen = linewidth(0.9);
pen auxpen = linewidth(0.8) + dashed;
pen carrierpen = linewidth(0.45);
pen midpen = linewidth(0.45) + dashed;

// Given triangles on base BC, with top vertices A,D on a parallel line.
pair B=(0,0), C=(6,0);
pair A=(2,4), D=(5,4);

// Midpoints used by the two applications of Hilbert Theorem 45.
pair M=(1,2);       // midpoint of BA
pair N=(4,2);       // midpoint of CA
pair P=(2.5,2);     // midpoint of BD
pair Q=(5.5,2);     // midpoint of CD

// Extension points produced by Hilbert Theorem 45.
// M-N-F and P-Q-G, with MN=NF and PQ=QG in this representative picture.
pair F=(7,2);
pair G=(8.5,2);

// The two parallel carriers occurring in the public theorem.
draw((-0.45,0)--(8.9,0), carrierpen);
draw((1.55,4)--(5.45,4), carrierpen);

// The common upper carrier recovered internally by the Lean proof.
draw((0.65,2)--(8.85,2), midpen);

// Given triangles ABC and DBC.
draw(A--B--C--cycle, mainpen);
draw(D--B--C--cycle, mainpen);

// Hilbert-45 parallelograms corresponding to the two triangles.
draw(M--B--C--F--cycle, auxpen);
draw(P--B--C--G--cycle, auxpen);

// Midpoints and constructed points.
dot(M); dot(N); dot(P); dot(Q); dot(F); dot(G);

// Labels.
label("$A$", A, NW);
label("$D$", D, NE);
label("$B$", B, SW);
label("$C$", C, SE);

label("$M$", M, NW);
label("$N$", N, SE);
label("$P$", P, NW);
label("$Q$", Q, SE);
label("$F$", F, N);
label("$G$", G, NE);

label("$MBCF$", (3.15,0.72), fontsize(9));
label("$PBCG$", (5.35,0.78), fontsize(9));
