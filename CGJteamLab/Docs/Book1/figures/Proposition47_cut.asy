import graph;

size(380,0);
defaultpen(fontsize(10pt));

pair A=(0,0), B=(3,0), C=(0,4);
pair D=(7,3), E=(4,7);
pair M=(48/25,36/25);
pair L=(148/25,111/25);
pair N=(112/25,84/25);

pen main=black+0.9bp;
pen aux=black+0.55bp+dashed;
pen cut=black+1.2bp;

// Hypotenuse square and the right triangle side needed to locate A.
draw(B--C--E--D--cycle,main);
draw(A--B--C,main);

// The perpendicular cut A-M-N-L and the diagonal D-N-C.
draw(A--L,cut);
draw(D--C,aux);

// Make the two cut parallelograms visible as boundary cycles.
draw(L--D--B--M--cycle,black+0.65bp);
draw(M--C--E--L--cycle,black+0.65bp);

dot(M); dot(L); dot(N);

label("$A$",A,SW);
label("$B$",B,SE);
label("$C$",C,W);
label("$D$",D,SE);
label("$E$",E,NE);
label("$M$",M,SE);
label("$L$",L,NE);
label("$N$",N,NE);
