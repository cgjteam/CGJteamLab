import graph;
settings.outformat="pdf";
size(13cm,0);
defaultpen(fontsize(10pt));

pen mainpen=black+0.9bp;
pen auxpen=black+0.55bp;
pen lightpen=gray(0.58)+0.45bp;

void dotlabel(string s, pair P, pair dir=NE) {
  dot(P, black);
  label("$"+s+"$", P, dir);
}

void segtick(pair A, pair B, int n=1) {
  pair M=(A+B)/2;
  pair v=unit(B-A);
  pair w=(-v.y,v.x);
  for(int k=0;k<n;++k) {
    real d=(k-(n-1)/2.0)*0.12;
    draw(M+d*v-0.10*w--M+d*v+0.10*w, mainpen);
  }
}

void rightmark(pair O, pair u, pair v, real s=0.22) {
  pair eu=unit(u);
  pair ev=unit(v);
  draw(O+s*eu--O+s*(eu+ev)--O+s*ev, mainpen);
}

pair A=(-4,0), C=(0,0), B=(4,0), D=(6.4,0);
pair E=(0,4), F=(6.4,4);

// External baseline and first construction stages.
draw(A--D, mainpen);
draw(C--E, mainpen);
draw(C--D--F--E--cycle, mainpen);
draw(A--E, auxpen);
draw(E--B, auxpen);

// Given/copied equal segments and perpendicular at C.
segtick(A,C,1); segtick(C,B,1); segtick(C,E,1);
rightmark(C,A-C,E-C);

// Parallelogram opposite sides, shown only after F exists.
segtick(C,D,2); segtick(E,F,2);

// Points.
dotlabel("A",A,SW); dotlabel("C",C,S); dotlabel("B",B,S);
dotlabel("D",D,SE); dotlabel("E",E,NW); dotlabel("F",F,NE);

label("$A-C-B-D$",(1.1,-0.58),S);
label("$CDFE$ parallelogram",(3.2,4.45),N);
