import graph;
size(280);
pair A=(0,2), B=(0,0), C=(4,2), D=(4,0), M=(2,1);
pen p=linewidth(0.8);
draw(A--B,p); draw(C--D,p); draw(A--C,p); draw(B--D,p);
draw(A--D,p); draw(B--C,p);
dot(A); dot(B); dot(C); dot(D); dot(M);
label("$A$",A,NW); label("$B$",B,SW); label("$C$",C,NE); label("$D$",D,SE); label("$M$",M,E);
// congruence ticks on AB and CD
pair mab=(A+B)/2, mcd=(C+D)/2;
draw(mab+(-.10,0)--mab+(.10,0),p);
draw(mcd+(-.10,0)--mcd+(.10,0),p);
