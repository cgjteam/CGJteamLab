import graph;
import math;

size(13.5cm,0);
defaultpen(fontsize(9.5pt));

pen mainpen = linewidth(0.9);
pen auxpen = gray(0.45) + linewidth(0.65);
pen lightpen = gray(0.72) + linewidth(0.45);
pen fillpen = gray(0.90) + opacity(0.50);

void pt(string s, pair P, pair d) {
  dot(P);
  label("$"+s+"$", P, d);
}

// Original parallelogram STUV.
pair S=(0.2,2.0);
pair T=(3.2,2.0);
pair U=(4.2,0.0);
pair V=(1.2,0.0);

// Prescribed base A-B, with E beyond B, and the rigid copy BEFG.
pair A=(6.0,0.0);
pair B=(8.5,0.0);
pair E=(11.5,0.0);
pair G=(7.5,2.0);
pair F=(10.5,2.0);

filldraw(S--T--U--V--cycle, fillpen, mainpen);
filldraw(B--E--F--G--cycle, fillpen, mainpen);
draw(A--E+(0.55,0), auxpen);

pt("S",S,NW);
pt("T",T,NE);
pt("U",U,SE);
pt("V",V,SW);
pt("A",A,SW);
pt("B",B,S);
pt("E",E,S);
pt("F",F,NE);
pt("G",G,NW);

// Matching side marks: TS with BE, and TU with BG.
pair mTS=(S+T)/2;
pair mBE=(B+E)/2;
draw(mTS+(-0.05,-0.11)--mTS+(0.05,0.11), mainpen);
draw(mBE+(-0.05,-0.11)--mBE+(0.05,0.11), mainpen);

pair mTU=(T+U)/2;
pair mBG=(B+G)/2;
draw(mTU+(-0.10,-0.02)--mTU+(0.10,0.02), mainpen);
draw(mTU+(-0.10,0.10)--mTU+(0.10,0.14), mainpen);
draw(mBG+(-0.10,-0.02)--mBG+(0.10,0.02), mainpen);
draw(mBG+(-0.10,0.10)--mBG+(0.10,0.14), mainpen);

// Congruent angle arcs at T and B.
real aTS=degrees(atan2(S.y-T.y,S.x-T.x));
real aTU=degrees(atan2(U.y-T.y,U.x-T.x));
draw(arc(T,0.42,aTS,aTU+360), mainpen);
real aBE=degrees(atan2(E.y-B.y,E.x-B.x));
real aBG=degrees(atan2(G.y-B.y,G.x-B.x));
draw(arc(B,0.42,aBE,aBG), mainpen);

label("original $STUV$", (2.2,2.65));
label("rigidly placed $BEFG$", (9.8,2.65));
label("$A-B-E$", (8.75,-0.55));
label("$BE\cong TS,\quad BG\cong TU$", (8.75,3.35));
label("$\angle EBG\cong\angle STU$", (2.5,-0.72));
