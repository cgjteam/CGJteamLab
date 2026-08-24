import graph;

size(16cm,0);
defaultpen(fontsize(8.8pt));

pen mainpen = linewidth(0.9);
pen auxpen = linewidth(0.75) + dashed;
pen carrierpen = gray(0.45) + linewidth(0.45);
pen markpen = linewidth(0.8);
pen pale1 = gray(0.88) + linewidth(0.5);
pen pale2 = gray(0.76) + linewidth(0.5);

void pt(string s, pair P, pair d) {
  dot(P);
  label("$"+s+"$", P, d);
}

void parallelMark(pair P, pair Q, int n=1) {
  pair M=interp(P,Q,0.58);
  pair u=unit(Q-P);
  pair v=(-u.y,u.x);
  for(int k=0;k<n;++k) {
    real t=(k-(n-1)/2.0)*0.16;
    draw(M+t*u-0.10*u-0.08*v -- M+t*u -- M+t*u+0.10*u-0.08*v, markpen);
  }
}

// ------------------------------------------------------------------
// Panel (a): classical I.41 configuration.
// ------------------------------------------------------------------
pair O1=(0,0);
pair B1=O1+(0.0,0.0), C1=O1+(4.0,0.0);
pair A1=O1+(0.8,2.35), D1=O1+(4.8,2.35), E1=O1+(3.15,2.35);

draw(O1+(-0.35,0)--O1+(5.15,0),carrierpen);
draw(O1+(0.35,2.35)--O1+(5.15,2.35),carrierpen);
draw(A1--B1--C1--D1--cycle,mainpen);
draw(E1--B1--C1--cycle,mainpen);
draw(A1--C1,auxpen);
parallelMark(A1,D1,1);
parallelMark(B1,C1,1);

pt("A",A1,NW); pt("D",D1,NE); pt("E",E1,N);
pt("B",B1,SW); pt("C",C1,SE);
label("(a) same base and the same parallels", O1+(2.4,2.88));
label("$AE\parallel BC$", O1+(2.4,-0.55));

// ------------------------------------------------------------------
// Panel (b): the content relations used by the Lean proof.
// ------------------------------------------------------------------
pair O2=(7.0,0);
pair B2=O2+(0.0,0.0), C2=O2+(4.0,0.0);
pair A2=O2+(0.8,2.35), D2=O2+(4.8,2.35), E2=O2+(3.15,2.35);

fill(A2--B2--C2--cycle,gray(0.90));
fill(A2--C2--D2--cycle,gray(0.78));
draw(O2+(-0.35,0)--O2+(5.15,0),carrierpen);
draw(O2+(0.35,2.35)--O2+(5.15,2.35),carrierpen);
draw(A2--B2--C2--D2--cycle,mainpen);
draw(E2--B2--C2--cycle,mainpen);
draw(A2--C2,linewidth(0.85));
parallelMark(A2,D2,1);
parallelMark(B2,C2,1);

pt("A",A2,NW); pt("D",D2,NE); pt("E",E2,N);
pt("B",B2,SW); pt("C",C2,SE);
label("(b) I.34 + I.37 in the scissors calculus", O2+(2.4,2.88));
label("$ABC\sim ACD,\qquad ABC\approx EBC$", O2+(2.4,-0.50));
label("$ABCD\sim ABC+ABC\approx EBC+EBC$", O2+(2.4,-1.02));
