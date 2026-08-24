import graph;

size(13.5cm,0);
defaultpen(fontsize(9.5pt));

pen mainpen = linewidth(1.0);
pen innerpen = linewidth(0.85);
pen diagpen = gray(0.45) + linewidth(0.65) + dashed;
pen oldfill = gray(0.90) + opacity(0.42);
pen newfill = gray(0.72) + opacity(0.30);

void pt(string s, pair P, pair d) {
  dot(P);
  label("$"+s+"$", P, d);
}

// Exact affine model of the paste configuration used in Proposition45.lean.
pair T=(0,0);
pair U=(3,0);
pair V=(3.8,2.0);
pair S=(0.8,2.0);
pair M=(1.96,-2.6);
pair L=(-1.04,-2.6);
pair X=(1.3043478261,0);

fill(S--T--U--V--cycle, oldfill);
fill(T--U--M--L--cycle, newfill);

draw(S--L--M--V--cycle, mainpen);
draw(S--T--U--V--cycle, innerpen);
draw(T--U--M--L--cycle, innerpen);

// Crossing used by the scissors refinement.
draw(S--M, diagpen);
draw(T--U, linewidth(1.0));

pt("S",S,NW);
pt("T",T,SW);
pt("U",U,SE);
pt("V",V,NE);
pt("L",L,SW);
pt("M",M,SE);
pt("X",X,N);

label("$S-T-L$", (-0.78,-0.55), W);
label("$V-U-M$", (3.00,-1.15), E);
label("old $STUV$", (1.55,1.20));
label("adjacent $TUML$", (0.75,-1.45));
label("outer $SLMV$", (4.35,-0.25), E);
