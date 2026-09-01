import graph;
settings.outformat="pdf";
size(13cm,0);
defaultpen(fontsize(10pt));

pen mainpen=black+0.9bp;
pen auxpen=black+0.55bp;
pen lightpen=gray(0.58)+0.45bp;
pen dashpen=gray(0.45)+0.55bp+dashed;

void dotlabel(string s, pair P, pair dir=NE) { dot(P,black); label("$"+s+"$",P,dir); }
void segtick(pair A, pair B) {
  pair M=(A+B)/2; pair v=unit(B-A); pair w=(-v.y,v.x);
  draw(M-0.10*w--M+0.10*w,mainpen);
}
void rightmark(pair O, pair u, pair v, real s=0.21) {
  pair eu=unit(u), ev=unit(v);
  draw(O+s*eu--O+s*(eu+ev)--O+s*ev,mainpen);
}

pair A=(-4,0), C=(0,0), B=(4,0), D=(6.4,0), E=(0,4), F=(6.4,4);
pair G=(6.4,-2.4);

draw(A--D,mainpen);
draw(C--E,mainpen);
draw(C--D--F--E--cycle,auxpen);
draw(A--E,auxpen);

// Produced carriers: emphasize the parts beyond B and D.
draw(E--B,mainpen);
draw(B--G,dashpen);
draw(F--D,mainpen);
draw(D--G,dashpen);
draw(A--G,auxpen);

segtick(A,C); segtick(C,B); segtick(C,E);
rightmark(C,A-C,E-C);

dotlabel("A",A,SW); dotlabel("C",C,S); dotlabel("B",B,SW); dotlabel("D",D,SE);
dotlabel("E",E,NW); dotlabel("F",F,NE); dotlabel("G",G,SE);

label("$E-B-G$",(4.9,-1.15),SW);
label("$F-D-G$",(6.85,0.8),E);
label("produced carriers",(4.9,3.3),NE);
