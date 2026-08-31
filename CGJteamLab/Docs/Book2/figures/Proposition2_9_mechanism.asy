import graph;
size(650,0);
defaultpen(fontsize(10pt));

pen mainpen=black+0.9bp;
pen auxpen=black+0.55bp;
pen lightpen=gray(0.58)+0.45bp;

void dotlabel(string s, pair P, pair dir=NE) {
  dot(P, black);
  label("$"+s+"$", P, dir);
}

void tick(pair A, pair B, int n=1) {
  pair M=(A+B)/2;
  pair v=unit(B-A);
  pair w=(-v.y,v.x);
  for(int k=0;k<n;++k) {
    real d=(k-(n-1)/2.0)*0.12;
    draw(M+d*v-0.10*w--M+d*v+0.10*w, mainpen);
  }
}

void rightmark(pair O, pair u, pair v, real s=0.20) {
  pair eu=unit(u);
  pair ev=unit(v);
  draw(O+s*eu--O+s*(eu+ev)--O+s*ev, mainpen);
}

// A-C-D-B, with C midpoint of AB and D the unequal cut on CB.
pair A=(-4,0);
pair C=(0,0);
pair D=(1.45,0);
pair B=(4,0);
pair E=(0,4);

// E-F-B and D-F parallel CE.
real t=(D.x-E.x)/(B.x-E.x);
pair F=E+t*(B-E);
pair G=(0,F.y);

// Main carriers and joins.
draw(A--B, mainpen);
draw(C--E, mainpen);
draw(E--B, mainpen);
draw(D--F, mainpen);
draw(F--G, mainpen);
draw(A--F, mainpen);
draw(A--E, auxpen);

// DFGC parallelogram emphasis.
draw(C--D, mainpen);
draw(G--C, lightpen);

// Equal-half marks AC, CB, CE.
tick(A,C,1);
tick(C,B,1);
tick(C,E,1);

// Equalities recovered by the angle argument.
tick(G,E,2);
tick(G,F,2);
tick(C,D,2);
tick(D,F,3);
tick(D,B,3);

// Right-angle marks used by the four Pythagorean blocks.
rightmark(C,A-C,E-C);
rightmark(D,A-D,F-D);
rightmark(G,E-G,F-G);
rightmark(E,A-E,F-E);

// Points.
dotlabel("A",A,SW);
dotlabel("C",C,S);
dotlabel("D",D,S);
dotlabel("B",B,SE);
dotlabel("E",E,NW);
dotlabel("F",F,NE);
dotlabel("G",G,W);

label("$A-C-D-B$",(0,-0.48),S);
