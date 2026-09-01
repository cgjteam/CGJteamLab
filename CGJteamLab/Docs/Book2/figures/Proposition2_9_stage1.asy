import graph;
settings.outformat="pdf";
size(12.5cm,0);
defaultpen(fontsize(10pt));

pen mainpen=black+0.9bp;
pen auxpen=black+0.55bp;

void dotlabel(string s, pair P, pair dir=NE) { dot(P,black); label("$"+s+"$",P,dir); }
void segtick(pair A, pair B, int n=1) {
  pair M=(A+B)/2; pair v=unit(B-A); pair w=(-v.y,v.x);
  for(int k=0;k<n;++k) {
    real d=(k-(n-1)/2.0)*0.12;
    draw(M+d*v-0.10*w--M+d*v+0.10*w,mainpen);
  }
}
void rightmark(pair O, pair u, pair v, real s=0.22) {
  pair eu=unit(u), ev=unit(v);
  draw(O+s*eu--O+s*(eu+ev)--O+s*ev,mainpen);
}

pair A=(-4,0), C=(0,0), D=(1.45,0), B=(4,0), E=(0,4);

draw(A--B,mainpen);
draw(C--E,mainpen);
draw(E--A,auxpen);
draw(E--B,mainpen);

segtick(A,C,1); segtick(C,B,1); segtick(C,E,1);
rightmark(C,A-C,E-C);

dotlabel("A",A,SW); dotlabel("C",C,S); dotlabel("D",D,S); dotlabel("B",B,SE); dotlabel("E",E,N);
label("$A-C-D-B$",(0,-0.58),S);
label("$AC\cong CB\cong CE$",(0,4.55),N);
