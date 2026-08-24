import graph;

size(12.5cm,0);
defaultpen(fontsize(9.5pt));

pen mainpen = linewidth(1.0);
pen carrierpen = gray(0.65) + linewidth(0.55);
pen markpen = linewidth(0.8);

void pt(string s, pair P, pair d) {
  dot(P);
  label("$"+s+"$", P, d);
}

void parallelMark(pair P, pair Q, int n=1) {
  pair M=(P+Q)/2;
  pair v=unit(Q-P);
  pair w=(-v.y,v.x);
  for(int k=0; k<n; ++k) {
    pair X=M+(k-(n-1)/2.0)*0.20*v;
    draw(X-0.10*v-0.07*w -- X+0.10*v+0.07*w, markpen);
  }
}

void rightmark(pair O, pair U, pair V) {
  pair u=unit(U-O);
  pair v=unit(V-O);
  real s=0.30;
  draw(O+s*u -- O+s*u+s*v -- O+s*v, markpen);
}

// Right-angle case of the reusable parallelogram configuration.
// F-B-C and AD || BF.
pair A=(0,0);
pair B=(4.8,0);
pair D=(0,3.4);
pair C=(4.8,3.4);
pair F=(4.8,-2.0);
pair E=(2.35,0);

// Parallelogram and produced side.
draw(A--B--C--D--cycle, mainpen);
draw(F--C, carrierpen);

// Transversal AB with the normalization point E.
draw(A--B, mainpen);

parallelMark(A,D,1);
parallelMark(F,C,1);

rightmark(A,B,D);
rightmark(B,A,C);

pt("A",A,SW);
pt("B",B,SE);
pt("C",C,NE);
pt("D",D,NW);
pt("F",F,SE);
pt("E",E,S);

label("$F-B-C$", (5.15,0.70), E);
label("$AD\parallel BF$", (2.4,2.55));
label("$\angle DAB\cong\angle FBA$", (2.4,-1.42));
label("$AB$ transversal", (2.4,0.42));
