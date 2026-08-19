import graph;

size(440,0);
defaultpen(fontsize(10.5pt));

pair B=(0,0), C=(3,0), A=(-1,2), D=(2,2), E=(3.8,2), F=(6.8,2);
pair G=intersectionpoint(E--B,D--C);

void pt(string s, pair P, pair d) {
  dot(P);
  label("$"+s+"$",P,d);
}

void baseDrawing() {
  draw(A--F, gray+0.6pt);
  draw(B--C, gray+0.6pt);
  draw(A--B, black+0.8pt);
  draw(D--C, black+0.8pt);
  draw(E--B, black+0.8pt);
  draw(F--C, black+0.8pt);

  pt("A",A,NW); pt("B",B,SW); pt("C",C,SE);
  pt("D",D,N); pt("E",E,N); pt("F",F,NE); pt("G",G,S);
}

fill(E--A--B--cycle, gray(0.86));
fill(G--B--C--cycle, gray(0.58));
baseDrawing();
label("$EAB + GBC$", (2.9,2.62));
