import graph;
settings.outformat="pdf";
size(15.5cm,0);
defaultpen(fontsize(9.5pt));

pen mainpen=black+0.9bp;
pen auxpen=black+0.52bp;
pen lightpen=gray(0.60)+0.45bp;
pen dashpen=gray(0.48)+0.55bp+dashed;

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

// Left panel: AG through E, with the two leg-expansion triangles ACE and FEG.
pair shL=(-4.8,0);
pair A=shL+(-3.4,0), C=shL+(0,0), B=shL+(3.4,0), D=shL+(5.4,0);
pair E=shL+(0,3.4), F=shL+(5.4,3.4), G=shL+(5.4,-2.0);

draw(A--E--G--A,mainpen);
draw(A--C--E,auxpen);
draw(E--F--G,auxpen);
draw(C--D,lightpen);
draw(C--E,auxpen);
draw(F--D,lightpen);
rightmark(C,A-C,E-C);
rightmark(F,E-F,G-F);
rightmark(E,A-E,G-E);
segtick(A,C,1); segtick(C,E,1); segtick(E,F,2); segtick(F,G,2);

dotlabel("A",A,SW); dotlabel("C",C,S); dotlabel("E",E,NW); dotlabel("F",F,NE); dotlabel("G",G,SE);
label("AG via E",shL+(1.0,4.15),N);
label("I.47 on EAG",shL+(1.0,-1.15),S);
label("I.47 on ACE",shL+(-2.25,1.55),W);
label("I.47 on FEG",shL+(5.95,1.55),E);

// Right panel: the second decomposition of the same hypotenuse AG through D.
pair shR=(6.5,0);
pair A2=shR+(-3.4,0), D2=shR+(3.2,0), G2=shR+(3.2,-2.0);
pair B2=shR+(1.2,0);

draw(A2--D2--G2--A2,mainpen);
rightmark(D2,A2-D2,G2-D2);
segtick(D2,B2,1); segtick(D2,G2,1);

dotlabel("A",A2,SW); dotlabel("B",B2,S); dotlabel("D",D2,SE); dotlabel("G",G2,SE);
label("AG via D",shR+(0.0,1.2),N);
label("I.47 on DAG",shR+(-0.15,-1.25),S);
label("$DB\cong DG$",shR+(1.55,-0.55),S);

// Visual common-hypotenuse cue.
label("common hypotenuse $AG$",(0.7,-3.05),S);
