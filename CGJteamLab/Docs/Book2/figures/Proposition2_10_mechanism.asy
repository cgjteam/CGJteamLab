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

// Source order A-C-B-D.
pair A=(-4,0);
pair C=(0,0);
pair B=(4,0);
pair D=(6.4,0);
pair E=(0,4);

// CDFE is a parallelogram with CD horizontal and CE vertical.
pair F=(D.x,E.y);

// G is the intersection of EB produced beyond B with FD produced beyond D.
// With E=(0,4), B=(4,0), the line EB is y=4-x.
pair G=(D.x,4-D.x);

// Main carriers and joins.
draw(A--D, mainpen);
draw(C--E, mainpen);
draw(E--G, mainpen);
draw(F--G, mainpen);
draw(E--F, mainpen);
draw(A--G, mainpen);
draw(A--E, auxpen);

// Parallelogram emphasis.
draw(C--D, mainpen);
draw(D--F, mainpen);

// Equal-half marks AC, CB, CE.
tick(A,C,1);
tick(C,B,1);
tick(C,E,1);

// EF = FG = CD.
tick(E,F,2);
tick(F,G,2);
tick(C,D,2);

// DB = DG.
tick(D,B,3);
tick(D,G,3);

// Right-angle marks for the four I.47 triangles.
rightmark(C,A-C,E-C);
rightmark(F,E-F,G-F);
rightmark(E,A-E,G-E);
rightmark(D,A-D,G-D);

// Points.
dotlabel("A",A,SW);
dotlabel("C",C,S);
dotlabel("B",B,S);
dotlabel("D",D,SE);
dotlabel("E",E,NW);
dotlabel("F",F,NE);
dotlabel("G",G,SE);

label("$A-C-B-D$",(1.2,-0.55),S);
