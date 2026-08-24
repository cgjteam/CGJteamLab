import graph;

size(13.5cm,0);
defaultpen(fontsize(9.5pt));

pen mainpen = linewidth(1.0);
pen auxpen = gray(0.45) + linewidth(0.65) + dashed;
pen lightpen = gray(0.68) + linewidth(0.5);
pen markpen = linewidth(0.8);

void pt(string s, pair P, pair d) {
  dot(P);
  label("$"+s+"$", P, d);
}

void slash(pair P, pair Q, int n=1) {
  pair M=(P+Q)/2;
  pair v=unit(Q-P);
  pair w=(-v.y,v.x);
  for(int k=0; k<n; ++k) {
    pair X=M+(k-(n-1)/2.0)*0.18*v;
    draw(X-0.09*v-0.08*w -- X+0.09*v+0.08*w, markpen);
  }
}

void rightmark(pair O, pair U, pair V) {
  pair u=unit(U-O);
  pair v=unit(V-O);
  real s=0.34;
  draw(O+s*u -- O+s*u+s*v -- O+s*v, markpen);
}

// Representative realization of the final square and the endpoint helper.
pair A=(0,0);
pair B=(5.0,0);
pair D=(0,5.0);
pair C=(5.0,5.0);

// Extension witness B-A-F and perpendicular direction X.
pair F=(-1.55,0);
pair X=(0,2.35);

// Final square.
draw(A--B--C--D--cycle, mainpen);

// Auxiliary endpoint construction.
draw(F--B, lightpen);
draw(A--X, auxpen);

// Congruent sides used at the start of the proof.
slash(A,B,1);
slash(A,D,1);

// Right-angle marker at A.
rightmark(A,B,D);

pt("A",A,SW);
pt("B",B,SE);
pt("C",C,NE);
pt("D",D,NW);
pt("F",F,SW);
pt("X",X,E);

label("$B-A-F$", (-0.78,-0.48));
label("$D$ on ray $AX$", (0.34,3.55), E);
label("$AD\cong AB$", (2.25,2.72));
label("final square $ABCD$", (2.55,5.50));
