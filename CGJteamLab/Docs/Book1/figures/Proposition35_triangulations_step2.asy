import graph;

size(360,0);
defaultpen(fontsize(10.5pt));

void pt(string s, pair P, pair d) {
  dot(P);
  label("$"+s+"$", P, d);
}

pair A=(-1.0,1.8);
pair B=(0,0);
pair C=(3.0,0);
pair D=(2.0,1.8);
pair M=intersectionpoint(A--C,B--D);

void frame() {
  draw(A--B--C--D--cycle, black+0.95pt);
  pt("A",A,NW);
  pt("B",B,SW);
  pt("C",C,SE);
  pt("D",D,NE);
  pt("M",M,S);
}

fill(A--B--M--cycle, gray(0.88));
fill(B--C--M--cycle, gray(0.72));
fill(C--D--M--cycle, gray(0.88));
fill(D--A--M--cycle, gray(0.72));
draw(A--C, black+0.95pt);
draw(B--D, black+0.95pt);
frame();
label("$ABM + BMC + CMD + DMA$", (1.0,2.38));
