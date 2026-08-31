import graph;
size(650,0);
defaultpen(fontsize(10pt));

pen mainpen=black+0.9bp;
pen auxpen=black+0.55bp;
pen lightpen=gray(0.62)+0.45bp;

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

void rightmark(pair O, pair u, pair v, real s=0.22) {
  pair eu=unit(u);
  pair ev=unit(v);
  draw(O+s*eu--O+s*(eu+ev)--O+s*ev, mainpen);
}

// Square ABCD on AB.
pair A=(0,0);
pair B=(5,0);
pair C=(5,5);
pair D=(0,5);

// E is midpoint of DA.
pair E=(0,2.5);

// F is on the extension through A with EF = EB.
real r=length(B-E);
pair F=(0,E.y-r);

// H is on AB with AH = AF.
pair H=(length(F-A),0);

// Main square and construction lines.
draw(A--B--C--D--A, mainpen);
draw(D--F, mainpen);
draw(E--B, mainpen);

// Light construction arc centered at E, through F and B.
// The full circle is omitted so that the principal configuration remains dominant.
draw(arc(E,r,-90,-26.565051), lightpen);

// Final cut point on AB.
draw(H+(0,-0.16)--H+(0,0.16), mainpen);

// Equalities.
tick(D,E,1);
tick(E,A,1);
tick(E,F,2);
tick(E,B,2);
tick(A,F,3);
tick(A,H,3);

// Right angle EAB.
rightmark(A,E-A,B-A);

// Points.
dotlabel("A",A,SW);
dotlabel("B",B,SE);
dotlabel("C",C,NE);
dotlabel("D",D,NW);
dotlabel("E",E,W);
dotlabel("F",F,SW);
dotlabel("H",H,S);

