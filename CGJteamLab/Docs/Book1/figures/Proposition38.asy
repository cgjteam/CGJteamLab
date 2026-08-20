import graph;

size(15cm,0);
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
// Panel (a): public classical configuration.
// ------------------------------------------------------------------
pair O1=(0,5.4);
pair B1=O1+(0,0), C1=O1+(2.0,0), E1=O1+(3.4,0), F1=O1+(5.4,0);
pair A1=O1+(0.75,2.0), D1=O1+(4.75,2.0);
draw(O1+(-0.35,0)--O1+(5.8,0),carrierpen);
draw(O1+(0.35,2.0)--O1+(5.2,2.0),carrierpen);
draw(A1--B1--C1--cycle,mainpen);
draw(D1--E1--F1--cycle,mainpen);
slash(B1,C1,2); slash(E1,F1,2);
parallelMark(A1,D1,1); parallelMark(B1,F1,1);
pt("A",A1,NW); pt("D",D1,NE);
pt("B",B1,SW); pt("C",C1,S); pt("E",E1,S); pt("F",F1,SE);
label("(a) given configuration", O1+(2.7,2.55));
label("$BC\cong EF$, $AD\parallel BC$", O1+(2.7,-0.55));

// ------------------------------------------------------------------
// Panel (b): copied triangle at EF.
// G is the final laid-off point; G0 names the constructed ray.
// ------------------------------------------------------------------
pair O2=(7.0,5.4);
pair B2=O2+(0,0), C2=O2+(2.0,0), E2=O2+(3.4,0), F2=O2+(5.4,0);
pair A2=O2+(0.75,2.0);
pair G2=O2+(4.15,2.0);
pair G02=E2+0.68*(G2-E2);
draw(O2+(-0.35,0)--O2+(5.8,0),carrierpen);
draw(A2--B2--C2--cycle,mainpen);
draw(G2--E2--F2--cycle,mainpen);
draw(E2--G2,auxpen);
slash(B2,C2,2); slash(E2,F2,2);
slash(A2,B2,1); slash(E2,G2,1);
pt("A",A2,NW); pt("B",B2,SW); pt("C",C2,S); pt("E",E2,S); pt("F",F2,SE);
pt("G",G2,NE); dot(G02); label("$G_0$",G02,W);
label("(b) congruent copy", O2+(2.7,2.55));
label("$BAC\cong EGF$", O2+(2.7,-0.55));

// ------------------------------------------------------------------
// Panel (c): the hidden oriented construction proving AGEB is a
// parallelogram.  X and Y are extension witnesses used by I.28.
// ------------------------------------------------------------------
pair O3=(0,0);
pair B3=O3+(0.5,0.65), E3=O3+(4.0,0.65);
pair A3=O3+(1.15,2.7), G3=O3+(4.65,2.7);
pair X3=B3+(B3-A3)*0.68;
pair Y3=E3+(E3-G3)*0.68;
pair F3=O3+(5.35,0.65);
draw(O3+(-0.1,0.65)--O3+(5.7,0.65),carrierpen);
draw(A3--B3--X3,auxpen);
draw(G3--E3--Y3,auxpen);
draw(A3--G3--E3--B3--cycle,mainpen);
draw(E3--F3,pale);
parallelMark(A3,B3,2); parallelMark(G3,E3,2);
parallelMark(A3,G3,1); parallelMark(B3,E3,1);
pt("A",A3,NW); pt("G",G3,NE); pt("B",B3,W); pt("E",E3,S);
pt("X",X3,SW); pt("Y",Y3,SE); pt("F",F3,E);
label("(c) $AGEB$ parallelogram", O3+(2.8,3.25));

// ------------------------------------------------------------------
// Panel (d): nondegenerate branch after top-carrier identification.
// The boundary branch G=D is handled separately in Lean.
// ------------------------------------------------------------------
pair O4=(7.0,0);
pair E4=O4+(1.0,0.55), F4=O4+(3.2,0.55);
pair A4=O4+(0.0,2.65), G4=O4+(1.65,2.65), D4=O4+(3.95,2.65);
draw(O4+(-0.35,2.65)--O4+(4.35,2.65),carrierpen);
draw(O4+(0.65,0.55)--O4+(3.55,0.55),carrierpen);
draw(G4--E4--F4--cycle,mainpen);
draw(D4--E4--F4--cycle,mainpen);
parallelMark(G4,D4,1); parallelMark(E4,F4,1);
pt("A",A4,NW); pt("G",G4,N); pt("D",D4,NE); pt("E",E4,SW); pt("F",F4,SE);
label("(d) reduction to I.37", O4+(2.0,3.20));
label("$GD\parallel EF$", O4+(2.0,0.00));
