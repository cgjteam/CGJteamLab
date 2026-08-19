import graph;

size(500,0);
defaultpen(fontsize(8.5pt));

pair B0=(0,0), C0=(3,0), A0=(-1,2), D0=(2,2), E0=(3.8,2), F0=(6.8,2);
pair G0=intersectionpoint(E0--B0,D0--C0);

void pt(string s, pair P, pair d) {
  dot(P);
  label("$"+s+"$",P,d);
}

void baseDrawing(pair O) {
  pair A=O+A0, B=O+B0, C=O+C0, D=O+D0, E=O+E0, F=O+F0, G=O+G0;
  draw(A--F, gray+0.55pt);
  draw(B--C, gray+0.55pt);
  draw(A--B, black+0.7pt);
  draw(D--C, black+0.7pt);
  draw(E--B, black+0.7pt);
  draw(F--C, black+0.7pt);
  pt("A",A,NW); pt("B",B,SW); pt("C",C,SE);
  pt("D",D,N); pt("E",E,N); pt("F",F,NE); pt("G",G,S);
}

void leftAug(pair O) {
  pair A=O+A0, B=O+B0, C=O+C0, D=O+D0, E=O+E0, G=O+G0;
  fill(A--B--C--D--cycle, gray(0.86));
  fill(D--G--E--cycle, gray(0.58));
  baseDrawing(O);
  label("$ABCD + DGE$",O+(2.8,2.55));
}

void leftRefined(pair O) {
  pair A=O+A0, B=O+B0, C=O+C0, E=O+E0, G=O+G0;
  fill(E--A--B--cycle, gray(0.86));
  fill(G--B--C--cycle, gray(0.58));
  baseDrawing(O);
  label("$EAB + GBC$",O+(2.8,2.55));
}

void rightRefined(pair O) {
  pair B=O+B0, C=O+C0, D=O+D0, F=O+F0, G=O+G0;
  fill(F--D--C--cycle, gray(0.86));
  fill(G--B--C--cycle, gray(0.58));
  baseDrawing(O);
  label("$FDC + GBC$",O+(2.8,2.55));
}

void rightAug(pair O) {
  pair B=O+B0, C=O+C0, D=O+D0, E=O+E0, F=O+F0, G=O+G0;
  fill(E--B--C--F--cycle, gray(0.86));
  fill(D--G--E--cycle, gray(0.58));
  baseDrawing(O);
  label("$EBCF + DGE$",O+(2.8,2.55));
}

leftAug((0,4.0));
leftRefined((9.2,4.0));
rightAug((0,0));
rightRefined((9.2,0));

draw((7.55,4.95)--(8.55,4.95), black+0.8pt, Arrow);
label("split / regroup",(8.05,5.25));
draw((7.55,0.95)--(8.55,0.95), black+0.8pt, Arrow);
label("split / regroup",(8.05,1.25));
draw((12.0,3.65)--(12.0,2.35), black+0.8pt, Arrow);
label("replace congruent outer triangle",(14.4,3.0));
