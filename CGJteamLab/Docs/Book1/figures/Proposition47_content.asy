import graph;

size(470,0);
defaultpen(fontsize(9pt));

pair A=(0,0), B=(3,0), C=(0,4);
pair F=(3,-3), G=(0,-3);
pair K=(-4,4), H=(-4,0);
pair D=(7,3), E=(4,7);
pair M=(48/25,36/25);
pair L=(148/25,111/25);

pen main=black+0.75bp;
pen bridge=black+0.65bp+dashed;
pen emph=black+1.1bp;

// Left content chain: square ABFG <-> rectangle LDBM.
pair s1=(0,0);
draw((A+s1)--(B+s1)--(F+s1)--(G+s1)--cycle,main);
draw((A+s1)--(B+s1)--(C+s1)--cycle,main);
draw((L+s1)--(D+s1)--(B+s1)--(M+s1)--cycle,emph);
draw((B+s1)--(A+s1)--(D+s1)--cycle,bridge);
draw((B+s1)--(F+s1)--(C+s1)--cycle,bridge);
label("$A$",A+s1,SW); label("$B$",B+s1,SE); label("$C$",C+s1,NW);
label("$D$",D+s1,SE); label("$F$",F+s1,SE); label("$G$",G+s1,SW);
label("$M$",M+s1,SE); label("$L$",L+s1,NE);
label("(a)",(2.7,-4.0)+s1,S);

// Right content chain: square ACKH <-> rectangle MCEL.
pair s2=(15,0);
draw((A+s2)--(C+s2)--(K+s2)--(H+s2)--cycle,main);
draw((A+s2)--(B+s2)--(C+s2)--cycle,main);
draw((M+s2)--(C+s2)--(E+s2)--(L+s2)--cycle,emph);
draw((C+s2)--(A+s2)--(E+s2)--cycle,bridge);
draw((C+s2)--(K+s2)--(B+s2)--cycle,bridge);
label("$A$",A+s2,SW); label("$B$",B+s2,SE); label("$C$",C+s2,NW);
label("$E$",E+s2,NE); label("$H$",H+s2,SW); label("$K$",K+s2,NW);
label("$M$",M+s2,SE); label("$L$",L+s2,NE);
label("(b)",(0.6,-1.1)+s2,S);
