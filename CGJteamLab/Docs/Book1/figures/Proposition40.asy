import graph;

size(16cm,0);
defaultpen(fontsize(8.6pt));

pen mainpen = linewidth(0.9);
pen auxpen = linewidth(0.72) + dashed;
pen carrierpen = gray(0.45) + linewidth(0.45);
pen markpen = linewidth(0.8);
pen pale = gray(0.82) + linewidth(0.55);

void pt(string s, pair P, pair d) {
  dot(P);
  label("$"+s+"$",P,d);
}

void slash(pair P, pair Q, int n=1) {
  pair M=(P+Q)/2;
  pair u=unit(Q-P);
  pair v=(-u.y,u.x);
  for(int k=0;k<n;++k) {
    real t=(k-(n-1)/2.0)*0.14;
    draw(M+t*u-0.10*v -- M+t*u+0.10*v, markpen);
  }
}

void parallelMark(pair P, pair Q, int n=1) {
  pair M=interp(P,Q,0.56);
  pair u=unit(Q-P);
  pair v=(-u.y,u.x);
  for(int k=0;k<n;++k) {
    real t=(k-(n-1)/2.0)*0.16;
    draw(M+t*u-0.10*u-0.08*v -- M+t*u -- M+t*u+0.10*u-0.08*v, markpen);
  }
}

// ------------------------------------------------------------------
// Panel (a): public ordered configuration of I.40.
// ------------------------------------------------------------------
pair O1=(0,4.6);
pair B1=O1+(0.0,0.0), C1=O1+(1.55,0.0), E1=O1+(3.15,0.0), F1=O1+(4.70,0.0);
pair A1=O1+(0.75,2.15), D1=O1+(3.95,2.15);

draw(O1+(-0.35,0)--O1+(5.05,0),carrierpen);
draw(A1--B1--C1--cycle,mainpen);
draw(D1--E1--F1--cycle,mainpen);
slash(B1,C1,2); slash(E1,F1,2);
pt("A",A1,NW); pt("D",D1,NE);
pt("B",B1,SW); pt("C",C1,S); pt("E",E1,S); pt("F",F1,SE);
label("(a) equal content on equal ordered bases", O1+(2.35,2.65));
label("$ABC\approx DEF,\quad BC\cong EF$", O1+(2.35,-0.55));

// ------------------------------------------------------------------
// Panel (b): reusable I.38 copy construction.
// GEF is congruent to ABC and AG is parallel to the base carrier.
// ------------------------------------------------------------------
pair O2=(6.3,4.6);
pair B2=O2+(0.0,0.0), C2=O2+(1.55,0.0), E2=O2+(3.15,0.0), F2=O2+(4.70,0.0);
pair A2=O2+(0.75,2.15), G2=O2+(3.90,2.15), D2=O2+(4.35,2.15);

draw(O2+(-0.35,0)--O2+(5.05,0),carrierpen);
draw(A2--B2--E2--G2--cycle,pale);
draw(A2--B2--C2--cycle,mainpen);
draw(G2--E2--F2--cycle,mainpen);
draw(D2--E2--F2--cycle,pale);
draw(A2--G2,auxpen);
slash(B2,C2,2); slash(E2,F2,2);
parallelMark(A2,G2,1); parallelMark(B2,F2,1);
pt("A",A2,NW); pt("G",G2,N); pt("D",D2,NE);
pt("B",B2,SW); pt("C",C2,S); pt("E",E2,S); pt("F",F2,SE);
label("(b) I.38 copy reduces to the base $EF$", O2+(2.35,2.65));
label("$BAC\cong EGF,\quad AG\parallel BC$", O2+(2.35,-0.55));

// ------------------------------------------------------------------
// Panel (c): apply I.39 on EF, then identify the two top carriers.
// ------------------------------------------------------------------
pair O3=(2.9,0.0);
pair B3=O3+(0.0,0.0), C3=O3+(1.55,0.0), E3=O3+(3.15,0.0), F3=O3+(4.70,0.0);
pair A3=O3+(0.75,2.20), G3=O3+(3.90,2.20), D3=O3+(4.55,2.20);

draw(O3+(-0.35,0)--O3+(5.05,0),carrierpen);
draw(O3+(0.35,2.20)--O3+(4.95,2.20),carrierpen);
draw(G3--E3--F3--cycle,mainpen);
draw(D3--E3--F3--cycle,mainpen);
draw(A3--G3,auxpen);
parallelMark(A3,D3,1); parallelMark(B3,F3,1);
pt("A",A3,NW); pt("G",G3,N); pt("D",D3,NE);
pt("B",B3,SW); pt("C",C3,S); pt("E",E3,S); pt("F",F3,SE);
label("(c) I.39 + parallel uniqueness", O3+(2.35,2.70));
label("$G,D\in top,\ AG\cap base=\emptyset\ \Longrightarrow\ A,G,D\in top$", O3+(2.35,-0.58));
