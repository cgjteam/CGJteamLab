import graph;

size(420,0);
defaultpen(fontsize(10pt));

pair A=(0,0), B=(3,0), C=(0,4);
pair F=(3,-3), G=(0,-3);
pair K=(-4,4), H=(-4,0);
pair D=(7,3), E=(4,7);
pair M=(48/25,36/25);
pair L=(148/25,111/25);
pair N=(112/25,84/25);

pen main=black+0.9bp;
pen aux=black+0.55bp+dashed;
pen cut=black+1.15bp;

// Right triangle.
draw(A--B--C--cycle,main);

// Squares on the three sides.
draw(A--B--F--G--cycle,main);
draw(A--C--K--H--cycle,main);
draw(B--C--E--D--cycle,main);

// Euclid's internal cut and the diagonal used by the scissors proof.
draw(A--L,cut);
draw(D--C,aux);

// Small right-angle mark at A.
pair u=(0.34,0), v=(0,0.34);
draw(u--(0.34,0.34)--v,main);

// Points used by the cut.
dot(M); dot(L); dot(N);

label("$A$",A,SW);
label("$B$",B,SE);
label("$C$",C,NW);
label("$D$",D,SE);
label("$E$",E,NE);
label("$F$",F,SE);
label("$G$",G,SW);
label("$H$",H,SW);
label("$K$",K,NW);
label("$M$",M,SE);
label("$L$",L,NE);
label("$N$",N,NE);
