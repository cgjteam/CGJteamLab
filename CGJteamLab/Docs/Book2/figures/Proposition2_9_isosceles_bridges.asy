import graph;
settings.outformat="pdf";
size(13.5cm,0);
defaultpen(fontsize(10pt));

pen mainpen=black+0.9bp;
pen auxpen=black+0.55bp;
pen lightpen=gray(0.58)+0.50bp;

void dotlabel(string s, pair P, pair dir=NE) { dot(P,black); label("$"+s+"$",P,dir); }
void segtick(pair A, pair B, int n=1) {
  pair M=(A+B)/2; pair v=unit(B-A); pair w=(-v.y,v.x);
  for(int k=0;k<n;++k) {
    real d=(k-(n-1)/2.0)*0.12;
    draw(M+d*v-0.10*w--M+d*v+0.10*w,mainpen);
  }
}
void rightmark(pair O, pair u, pair v, real s=0.20) {
  pair eu=unit(u), ev=unit(v);
  draw(O+s*eu--O+s*(eu+ev)--O+s*ev,mainpen);
}

pair A=(-4,0), C=(0,0), D=(1.45,0), B=(4,0), E=(0,4);
real t=(D.x-E.x)/(B.x-E.x);
pair F=E+t*(B-E);
pair G=(0,F.y);

draw(A--B,mainpen);
draw(C--E,auxpen);
draw(E--B,mainpen);
draw(D--F,mainpen);
draw(F--G,mainpen);
draw(G--C,auxpen);
draw(A--F,auxpen);

rightmark(D,A-D,F-D);
rightmark(G,E-G,F-G);
segtick(G,E,1); segtick(G,F,1);
segtick(D,F,2); segtick(D,B,2);

dotlabel("A",A,SW); dotlabel("C",C,S); dotlabel("D",D,S); dotlabel("B",B,SE);
dotlabel("E",E,NW); dotlabel("F",F,NE); dotlabel("G",G,W);
label("$GE\cong GF$",(-0.75,2.55),W);
label("$DF\cong DB$",(2.2,0.7),E);
label("$GF\cong CD$ by I.34",(0.75,0.95),S);
label("I.32 + angle subtraction + I.6",(0,4.55),N);
