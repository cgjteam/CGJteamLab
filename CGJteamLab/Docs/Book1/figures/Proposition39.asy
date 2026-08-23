import graph;

size(16cm,0);

pen mainpen = linewidth(0.9);
pen auxpen = linewidth(0.75) + dashed;
pen carrierpen = linewidth(0.45);
pen markpen = linewidth(0.75);

void pt(string s, pair P, pair d) {
  dot(P);
  label("$"+s+"$", P, d);
}

void parallelMark(pair P, pair Q, int n=1) {
  pair M=(P+Q)/2;
  pair v=unit(Q-P);
  pair w=(-v.y,v.x);
  for(int k=0; k<n; ++k) {
    pair X=M+(k-(n-1)/2.0)*0.22*v;
    draw(X-0.10*v-0.07*w -- X+0.10*v+0.07*w, markpen);
  }
}

// ------------------------------------------------------------------
// Panel (a): public configuration.
// ------------------------------------------------------------------
pair O1=(0,0);
pair B1=O1+(0,0), C1=O1+(4.0,0);
pair A1=O1+(1.0,2.35), D1=O1+(2.65,1.55);

draw(O1+(-0.35,0)--O1+(4.35,0),carrierpen);
draw(A1--B1--C1--cycle,mainpen);
draw(D1--B1--C1--cycle,mainpen);

pt("A",A1,NW); pt("D",D1,NE);
pt("B",B1,SW); pt("C",C1,SE);

label("(a) given equal-content triangles", O1+(2.0,2.85));
label("$ABC\approx DBC$", O1+(2.0,-0.55));

// ------------------------------------------------------------------
// Panel (b): B-E-D.  The parallel through A meets segment BD at E.
// ------------------------------------------------------------------
pair O2=(5.8,0);
pair B2=O2+(0,0), C2=O2+(4.0,0);
pair A2=O2+(0.72,2.0);
pair E2=O2+(1.80,2.0);
pair D2=O2+(2.70,3.0);

draw(O2+(-0.35,0)--O2+(4.35,0),carrierpen);
draw(O2+(0.35,2.0)--O2+(3.15,2.0),auxpen);
draw(A2--B2--C2--cycle,mainpen);
draw(D2--B2--C2--cycle,mainpen);
draw(E2--C2,linewidth(0.75));

pt("A",A2,NW); pt("E",E2,W); pt("D",D2,NE);
pt("B",B2,SW); pt("C",C2,SE);

label("(b) $B-E-D$", O2+(2.0,3.45));
label("$EBC$ proper part of $DBC$", O2+(2.0,-0.55));

// ------------------------------------------------------------------
// Panel (c): B-D-E.  The parallel through A meets extension of BD.
// ------------------------------------------------------------------
pair O3=(11.6,0);
pair B3=O3+(0,0), C3=O3+(4.0,0);
pair A3=O3+(0.72,2.0);
pair D3=O3+(1.80,1.35);
pair E3=O3+(2.6666667,2.0);

draw(O3+(-0.35,0)--O3+(4.35,0),carrierpen);
draw(O3+(0.35,2.0)--O3+(3.15,2.0),auxpen);
draw(A3--B3--C3--cycle,mainpen);
draw(E3--B3--C3--cycle,mainpen);
draw(D3--C3,linewidth(0.75));

pt("A",A3,NW); pt("D",D3,W); pt("E",E3,NE);
pt("B",B3,SW); pt("C",C3,SE);

label("(c) $B-D-E$", O3+(2.0,2.85));
label("$DBC$ proper part of $EBC$", O3+(2.0,-0.55));
