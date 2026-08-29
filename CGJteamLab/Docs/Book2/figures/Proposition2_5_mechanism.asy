import graph;
size(420,0);
defaultpen(fontsize(9pt)+black);

pair A=(0,0), C=(4,0), D=(5.3,0), B=(8,0);
pair E=(4,4), F=(8,4);
real yh=8-D.x;
pair H=(D.x,yh), G=(D.x,4);
pair K=(0,yh), L=(4,yh), M=(8,yh);

// Light grayscale fill for the classical gnomon: square CEFB minus LG.
fill(C--B--M--L--cycle, gray(0.93));
fill(H--M--F--G--cycle, gray(0.93));

// Main square and Euclidean construction.
draw(C--E--F--B--cycle, linewidth(0.8));
draw(A--B, linewidth(0.8));
draw(B--E, linewidth(0.7));
draw(D--G, linewidth(0.7));
draw(K--M, linewidth(0.7));
draw(A--K, linewidth(0.7));

// Emphasize the small square LG = square on CD.
draw(L--H--G--E--cycle, dashed+linewidth(0.55));

// Points.
dot(A); dot(C); dot(D); dot(B); dot(E); dot(F);
dot(H); dot(G); dot(K); dot(L); dot(M);

label("$A$",A,S); label("$C$",C,S); label("$D$",D,S); label("$B$",B,S);
label("$E$",E,NW); label("$F$",F,NE);
label("$H$",H,SE); label("$G$",G,N);
label("$K$",K,NW); label("$L$",L,W); label("$M$",M,E);

// Region labels, following Euclid's traditional two-letter figure notation.
label("$LG$",(L+G)/2,NE);
label("$CM$",(C+M)/2+(0,-0.25));
label("gnomon $CMG$",(6.6,3.35));

// Equal-half marks AC and CB.
draw((2,-0.10)--(2,0.10));
draw((6,-0.10)--(6,0.10));
