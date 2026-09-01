import graph;
settings.outformat="pdf";
size(15.5cm,0);
defaultpen(fontsize(9.5pt));

pen mainpen=black+0.9bp;
pen auxpen=black+0.52bp;
pen lightpen=gray(0.60)+0.45bp;

void dotlabel(string s, pair P, pair dir=NE) { dot(P,black); label("$"+s+"$",P,dir); }
void rightmark(pair O, pair u, pair v, real s=0.20) {
  pair eu=unit(u), ev=unit(v);
  draw(O+s*eu--O+s*(eu+ev)--O+s*ev,mainpen);
}
void segtick(pair A, pair B, int n=1) {
  pair M=(A+B)/2; pair v=unit(B-A); pair w=(-v.y,v.x);
  for(int k=0;k<n;++k) {
    real d=(k-(n-1)/2.0)*0.11;
    draw(M+d*v-0.09*w--M+d*v+0.09*w,mainpen);
  }
}

// Left panel: AF through E, expanded further by ACE and EGF.
pair shL=(-4.8,0);
pair A=shL+(-3.4,0), C=shL+(0,0), D=shL+(1.25,0), B=shL+(3.4,0), E=shL+(0,3.4);
real t=(D.x-E.x)/(B.x-E.x);
pair F=E+t*(B-E);
pair G=(C.x,F.y);

draw(A--E--F--A,mainpen);
draw(A--C--E,auxpen);
draw(E--G--F,auxpen);
draw(C--G,lightpen);
draw(C--D,lightpen);
rightmark(C,A-C,E-C);
rightmark(G,E-G,F-G);
rightmark(E,A-E,F-E);
segtick(A,C,1); segtick(C,E,1); segtick(G,E,2); segtick(G,F,2);

dotlabel("A",A,SW); dotlabel("C",C,S); dotlabel("E",E,NW); dotlabel("G",G,W); dotlabel("F",F,NE);
label("AF via E",shL+(0.6,4.15),N);
label("$AEF$",shL+(0.6,-1.05),S);
label("$ACE$",shL+(-2.1,1.45),W);
label("$EGF$",shL+(1.55,2.15),E);

// Right panel: the second decomposition of the same hypotenuse AF through D.
pair shR=(6.5,0);
pair A2=shR+(-3.4,0), D2=shR+(1.6,0), B2=shR+(3.25,0), F2=shR+(1.6,2.65);

draw(A2--D2--F2--A2,mainpen);
rightmark(D2,A2-D2,F2-D2);
segtick(D2,B2,3); segtick(D2,F2,3);

dotlabel("A",A2,SW); dotlabel("D",D2,S); dotlabel("B",B2,SE); dotlabel("F",F2,NE);
label("AF via D",shR+(-0.5,3.35),N);
label("$ADF$",shR+(-0.5,-1.05),S);
label("$DB\cong DF$",shR+(2.1,1.0),E);

label("common hypotenuse $AF$",(0.7,-2.75),S);
