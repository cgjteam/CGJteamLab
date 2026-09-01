import graph;
settings.outformat="pdf";
size(12.5cm,0);
defaultpen(fontsize(10pt));

pen mainpen=black+0.9bp;
pen auxpen=black+0.55bp;
pen lightpen=gray(0.58)+0.50bp;

void dotlabel(string s, pair P, pair dir=NE) { dot(P,black); label("$"+s+"$",P,dir); }
void rightmark(pair O, pair u, pair v, real s=0.22) {
  pair eu=unit(u), ev=unit(v);
  draw(O+s*eu--O+s*(eu+ev)--O+s*ev,mainpen);
}

pair A=(-4,0), C=(0,0), D=(1.45,0), B=(4,0), E=(0,4);
real t=(D.x-E.x)/(B.x-E.x);
pair F=E+t*(B-E);

draw(A--B,mainpen);
draw(C--E,mainpen);
draw(E--B,mainpen);
draw(D--F,mainpen);
draw(A--E,auxpen);
rightmark(C,A-C,E-C);
rightmark(D,A-D,F-D);

dotlabel("A",A,SW); dotlabel("C",C,S); dotlabel("D",D,S); dotlabel("B",B,SE);
dotlabel("E",E,NW); dotlabel("F",F,NE);
label("$E-F-B$",(3.15,2.15),E);
label("$DF\parallel CE$",(1.85,1.25),E);
