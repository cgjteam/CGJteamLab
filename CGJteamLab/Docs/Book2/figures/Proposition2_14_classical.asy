import graph;

size(440,0);
defaultpen(fontsize(10pt));

pen main=black+0.9bp;
pen aux=gray(0.42)+0.7bp;
pen note=gray(0.38);

pair B=(0,0);
pair C=(0,3);
pair D=(5,3);
pair E=(5,0);
pair F=(8,0);
pair G=(4,0);
real r=4;
real hy=sqrt(r*r-1);
pair H=(5,hy);

draw(B--C--D--E--B,main);
draw(B--F,main);
draw(E--H,main);
draw(G--H,main);

// Semicircle with center G and endpoints B,F.
draw(arc(G,r,0,180),aux);

// right angle at E for rectangle carrier
real s=0.27;
draw(E+(-s,0)--E+(-s,s)--E+(0,s),main);

// midpoint ticks on BG and GF
draw((2,-0.10)--(2,0.10),main);
draw((6,-0.10)--(6,0.10),main);

dot(B); dot(C); dot(D); dot(E); dot(F); dot(G); dot(H);

label("$B$",B,SW);
label("$C$",C,NW);
label("$D$",D,NW);
label("$E$",E,SE);
label("$F$",F,SE);
label("$G$",G,S);
label("$H$",H,NE);

label("$EF=ED$",(6.55,0.38),N,note);
label("$G$ midpoint of $BF$",(2.0,-0.62),S,note);
label("II.5 on $BF$",(3.2,0.58),N,note);
label("I.47 on $GEH$",(4.35,2.25),W,note);
label("semicircle $BHF$",(1.55,3.15),N,note);
