import graph;
size(430,0);
defaultpen(fontsize(9pt)+black);

// Euclid II.6 classical configuration.
// Baseline order: A -- C -- B -- D, with C the midpoint of AB.
pair A=(0,4), C=(2,4), B=(4,4), D=(6,4);
pair E=(2,0), G=(4,0), F=(6,0);
pair K=(0,2), L=(2,2), H=(4,2), M=(6,2);

// Auxiliary boundary labels used to name the gnomon in Euclid's style.
pair N=(5,4);     // point on the top side of the gnomon
pair O=H;         // re-entrant corner of the gnomon
pair P=(6,1);     // point on the right side of the gnomon

// The classical gnomon is the square CEFD minus the small square LG.
fill(C--D--M--L--cycle, gray(0.93));
fill(H--M--F--G--cycle, gray(0.93));

// Square CEFD on CD and the Euclidean auxiliary lines.
draw(C--D--F--E--cycle, linewidth(0.8));
draw(A--D, linewidth(0.8));
draw(E--D, linewidth(0.7));
draw(B--G, linewidth(0.7));
draw(K--M, linewidth(0.7));
draw(A--K, linewidth(0.7));

// Emphasize LG, the square equal to the square on BC.
draw(L--H--G--E--cycle, dashed+linewidth(0.55));

// Points.
dot(A); dot(C); dot(B); dot(D);
dot(E); dot(F); dot(G);
dot(K); dot(L); dot(H); dot(M);
dot(N); dot(P);

label("$A$",A,N); label("$C$",C,N); label("$B$",B,N); label("$D$",D,N);
label("$E$",E,S); label("$G$",G,S); label("$F$",F,S);
label("$K$",K,W); label("$L$",L,W); label("$H$",H,NE); label("$M$",M,E);

// Auxiliary labels matching the Euclidean name of the gnomon.
label("$N$",N,1.2N);
label("$O$",O,SW);
label("$P$",P,E);

// Region labels.
label("$LG$",(L+G)/2,SW);
label("$AM$",(A+M)/2+(0,0.16));

// Equal-half marks on AC and CB.
draw((1,3.90)--(1,4.10));
draw((3,3.90)--(3,4.10));

// Midpoint marks showing that N bisects BD.
draw((4.45,3.90)--(4.55,4.10));
draw((5.45,3.90)--(5.55,4.10));
