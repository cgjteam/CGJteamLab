import graph;
settings.outformat="pdf";
size(13cm,0);
defaultpen(fontsize(10pt));

pen mainpen=black+0.9bp;
pen auxpen=black+0.55bp;
pen lightpen=gray(0.58)+0.55bp;

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
void anglearc(pair O, pair P, pair Q, real r) {
  real a1=degrees(atan2((P-O).y,(P-O).x));
  real a2=degrees(atan2((Q-O).y,(Q-O).x));
  while(a2<a1) a2+=360;
  if(a2-a1>180) { real t=a1; a1=a2; a2=t+360; }
  draw(arc(O,r,a1,a2),lightpen);
}

pair C=(0,0), B=(4,0), D=(6.4,0), E=(0,4), F=(6.4,4), G=(6.4,-2.4);

// Keep only the portion of the global construction needed for the two I.6 conclusions.
draw(C--D,auxpen);
draw(C--E,auxpen);
draw(E--F,auxpen);
draw(E--G,mainpen);
draw(F--G,mainpen);
draw(B--D,mainpen);
draw(B--G,mainpen);

rightmark(D,B-D,G-D);
rightmark(F,E-F,G-F);

// First I.6 bridge: triangle DBG.
anglearc(B,D,G,0.42);
anglearc(G,D,B,0.42);
segtick(D,B,1); segtick(D,G,1);

// Second I.6 bridge and I.34 transport to CD.
anglearc(E,F,G,0.48);
anglearc(G,E,F,0.58);
segtick(E,F,2); segtick(F,G,2); segtick(C,D,2);

dotlabel("C",C,SW); dotlabel("B",B,SW); dotlabel("D",D,SE);
dotlabel("E",E,NW); dotlabel("F",F,NE); dotlabel("G",G,SE);

label("$DB\cong DG$",(5.15,-1.35),SW);
label("$GF\cong EF\cong CD$",(3.2,4.55),N);
label("triangle $DBG$",(5.0,-0.55),SW);
label("triangle $FEG$",(4.5,2.95),NE);
