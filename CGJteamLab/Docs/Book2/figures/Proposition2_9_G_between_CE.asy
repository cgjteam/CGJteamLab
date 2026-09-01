import graph;
settings.outformat="pdf";
size(12.8cm,0);
defaultpen(fontsize(10pt));

pen mainpen=black+0.9bp;
pen auxpen=black+0.55bp;
pen lightpen=gray(0.58)+0.50bp;

void dotlabel(string s, pair P, pair dir=NE) { dot(P,black); label("$"+s+"$",P,dir); }
void rightmark(pair O, pair u, pair v, real s=0.20) {
  pair eu=unit(u), ev=unit(v);
  draw(O+s*eu--O+s*(eu+ev)--O+s*ev,mainpen);
}

pair A=(-4,0), C=(0,0), D=(1.45,0), B=(4,0), E=(0,4);
real t=(D.x-E.x)/(B.x-E.x);
pair F=E+t*(B-E);
pair G=(0,F.y);

draw(A--B,mainpen);
draw(C--E,mainpen);
draw(E--B,mainpen);
draw(D--F,mainpen);
draw(F--G,mainpen);
draw(G--C,mainpen);
rightmark(C,A-C,E-C);
rightmark(D,A-D,F-D);
rightmark(G,E-G,F-G);

dotlabel("A",A,SW); dotlabel("C",C,S); dotlabel("D",D,S); dotlabel("B",B,SE);
dotlabel("E",E,NW); dotlabel("F",F,NE); dotlabel("G",G,W);
label("$E-F-B$",(3.25,2.0),E);
label("$C-G-E$",(-0.42,2.0),W);
label("$DFGC$",(0.72,1.05));
label("Pasch fixes the order of $G$",(0,4.55),N);
