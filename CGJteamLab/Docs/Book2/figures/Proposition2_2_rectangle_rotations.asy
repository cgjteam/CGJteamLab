// Proposition2_2_rectangle_rotations.asy
// Euclid Book II, Proposition 2: two cyclic representative swaps.
// ASCII-only Asymptote source.
settings.outformat = "pdf";
size(15cm,0);

pen mainpen = black + linewidth(0.85);
pen firstpen = black + linewidth(1.15);
pen secondpen = gray(0.45) + linewidth(0.85);
pen arrowpen = gray(0.45) + linewidth(0.7);

void rect(pair O, string p0, string p1, string p2, string p3,
          string firstside, string secondside) {
  pair A=O+(0,0), B=O+(2.8,0), C=O+(2.8,1.75), D=O+(0,1.75);
  draw(A--B--C--D--cycle, mainpen);
  draw(A--B, firstpen);
  draw(B--C, secondpen);
  dot(A); dot(B); dot(C); dot(D);
  label(p0,A,SW); label(p1,B,SE); label(p2,C,NE); label(p3,D,NW);
  label(firstside,(A+B)/2,S);
  label(secondside,(B+C)/2,E);
}

// First representative: Rect(BC,BM) -> Rect(BM,BC).
pair O1=(0,3.1);
pair O2=(6.7,3.1);
rect(O1,"$V_0$","$V_1$","$V_2$","$V_3$","$BC$","$BM$");
rect(O2,"$V_1$","$V_2$","$V_3$","$V_0$","$BM$","$BC$");
draw((3.35,4.0)--(6.05,4.0), arrowpen, Arrow(TeXHead));
label("cyclic swap",(4.70,4.35));
label("Rect(BC, BM)",(1.4,5.45));
label("Rect(BM, BC)",(8.1,5.45));

// Second representative: Rect(BC,MC) -> Rect(MC,BC).
pair P1=(0,0);
pair P2=(6.7,0);
rect(P1,"$W_0$","$W_1$","$W_2$","$W_3$","$BC$","$MC$");
rect(P2,"$W_1$","$W_2$","$W_3$","$W_0$","$MC$","$BC$");
draw((3.35,0.90)--(6.05,0.90), arrowpen, Arrow(TeXHead));
label("cyclic swap",(4.70,1.25));
label("Rect(BC, MC)",(1.4,2.35));
label("Rect(MC, BC)",(8.1,2.35));
