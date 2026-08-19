import graph;

size(420,0);
defaultpen(fontsize(9pt));

void pt(string s, pair P, pair d) {
  dot(P);
  label("$"+s+"$", P, d);
}

void panel(pair O, bool diagAC, string title) {
  pair A=O+(-1.0,1.8);
  pair B=O+(0,0);
  pair C=O+(3.0,0);
  pair D=O+(2.0,1.8);
  pair M=intersectionpoint(A--C,B--D);

  fill(A--B--C--D--cycle, lightgray+opacity(0.18));
  draw(A--B--C--D--cycle, black+0.9pt);
  if (diagAC) {
    draw(A--C, black+0.9pt);
  } else {
    draw(B--D, black+0.9pt);
  }

  pt("A",A,NW);
  pt("B",B,SW);
  pt("C",C,SE);
  pt("D",D,NE);
  pt("M",M,S);
  label(title,O+(1.0,2.35));
}

panel((0,0),true,"$ABC+ACD$");
panel((6.0,0),false,"$ABD+BCD$");
draw((4.05,0.9)--(5.15,0.9), black+0.8pt, Arrow);
label("scissors-equivalent",(4.6,1.18));
label("same parallelogram, different diagonal",(4.6,-0.65));
