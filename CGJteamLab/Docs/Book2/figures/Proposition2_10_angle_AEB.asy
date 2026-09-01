import graph;
settings.outformat="pdf";
size(11.5cm,0);
defaultpen(fontsize(10pt));

pen mainpen=black+0.9bp;
pen auxpen=black+0.55bp;
pen lightpen=gray(0.58)+0.55bp;

void dotlabel(string s, pair P, pair dir=NE) { dot(P,black); label("$"+s+"$",P,dir); }
void segtick(pair A, pair B) {
  pair M=(A+B)/2; pair v=unit(B-A); pair w=(-v.y,v.x);
  draw(M-0.11*w--M+0.11*w,mainpen);
}
void rightmark(pair O, pair u, pair v, real s=0.23, pen p=mainpen) {
  pair eu=unit(u), ev=unit(v);
  draw(O+s*eu--O+s*(eu+ev)--O+s*ev,p);
}
void anglearc(pair O, pair P, pair Q, real r, pen p=lightpen) {
  real a1=degrees(atan2((P-O).y,(P-O).x));
  real a2=degrees(atan2((Q-O).y,(Q-O).x));
  while(a2<a1) a2+=360;
  if(a2-a1>180) { real t=a1; a1=a2; a2=t+360; }
  draw(arc(O,r,a1,a2),p);
}

pair A=(-4,0), C=(0,0), B=(4,0), E=(0,4);

draw(A--B,mainpen);
draw(C--E,mainpen);
draw(E--A,mainpen);
draw(E--B,mainpen);

segtick(A,C); segtick(C,B); segtick(C,E);
rightmark(C,A-C,E-C);

// Equal half-right components at E.
anglearc(E,A,C,0.62);
anglearc(E,C,B,0.62);
// The completed right angle AEB.
rightmark(E,A-E,B-E,0.32,auxpen);

dotlabel("A",A,SW); dotlabel("C",C,S); dotlabel("B",B,SE); dotlabel("E",E,N);
label("I.5 + I.32",(0,4.65),N);
label("$\angle AEC\cong\angle BEC$",(0,3.0),S);
label("$\angle AEB$ right",(0,2.45),S);
