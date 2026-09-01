import graph;

size(440,0);
defaultpen(fontsize(10pt));

pen main=black+0.9bp;
pen circ=gray(0.48)+0.65bp;
pen aux=gray(0.35)+0.7bp+dashed;
pen note=gray(0.35);

pair B=(0,0);
pair C=(0,3);
pair D=(5,3);
pair E=(5,0);
pair F=(8,0);
pair G=(4,0);
pair K=(6,0);
real r=4;
real hy=sqrt(r*r-1);
pair H=(5,hy);
pair Hm=(5,-hy);

draw(B--C--D--E--B,main);
draw(B--F,main);
draw(D--H,main);
draw(G--H,main);
draw(K--H,main);

// Two equal circles. Draw the full circles faintly.
draw(circle(G,r),circ);
draw(circle(K,r),circ);

// perpendicular bisector through E
draw((5,-4.1)--(5,4.35),aux);

// midpoint ticks on GE and EK
draw((4.5,-0.11)--(4.5,0.11),main);
draw((5.5,-0.11)--(5.5,0.11),main);

// right angle at E
real s=0.27;
draw(E+(-s,0)--E+(-s,s)--E+(0,s),main);

dot(B); dot(C); dot(D); dot(E); dot(F); dot(G); dot(K); dot(H);

label("$B$",B,SW);
label("$C$",C,NW);
label("$D$",D,NW);
label("$E$",E,SE);
label("$F$",F,SE);
label("$G$",G,S);
label("$K$",K,S);
label("$H$",H,NE);

label("$E$ midpoint of $GK$",(5,-0.62),S,note);
label("$GH=GF$",(3.95,2.25),W,note);
label("$KH=GF$",(6.05,2.25),E,note);
label("common point of equal circles",(5,4.25),N,note);
label("rectangle axis / perpendicular bisector",(5.18,-3.05),E,note);
