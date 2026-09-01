// Proposition2_12_order_contradiction.asy
// Euclid Book II, Proposition 12.
// Wrong-position branch used to force the perpendicular foot beyond A.
// ASCII-only Asymptote source.

settings.outformat = "pdf";
size(13cm,0);
defaultpen(fontsize(10pt));

pen mainpen = black + 0.9bp;
pen auxpen = black + 0.60bp;
pen lightpen = gray(0.62) + 0.45bp;

void dotlabel(string s, pair P, pair dir=NE) {
  dot(P, black);
  label("$"+s+"$", P, dir);
}

void rightmark(pair O, pair u, pair v, real s=0.24) {
  pair eu = unit(u);
  pair ev = unit(v);
  draw(O+s*eu--O+s*(eu+ev)--O+s*ev, mainpen);
}

// Contradictory positional branch: D and C are assumed on the same ray from A.
// E extends AD beyond D.  Only A-D-E is encoded as betweenness; the relative
// placement of C and E on the same ray is not used by the proof.
pair A=(0,0);
pair D=(2.20,0);
pair C=(4.15,0);
pair E=(6.25,0);
pair B=(2.20,3.15);

// Triangle BAD, the common ray AC, and the extension through D to E.
draw(A--E, mainpen);
draw(B--A, mainpen);
draw(B--D, mainpen);

// Right exterior angle BDE.
rightmark(D,B-D,E-D);

// Light arcs only identify the interior angle BAD and exterior angle BDE.
real aBAD1=degrees(atan2((D-A).y,(D-A).x));
real aBAD2=degrees(atan2((B-A).y,(B-A).x));
draw(arc(A,0.55,aBAD1,aBAD2), lightpen);

real aBDE1=degrees(atan2((E-D).y,(E-D).x));
real aBDE2=degrees(atan2((B-D).y,(B-D).x));
draw(arc(D,0.78,aBDE1,aBDE2), lightpen);

// Points.
dotlabel("A",A,SW);
dotlabel("D",D,S);
dotlabel("C",C,S);
dotlabel("E",E,SE);
dotlabel("B",B,NW);

label("$\mathrm{SameRay}(A,D,C)$", (3.75,-0.55), S);
label("$A-D-E$", (4.35,0.38), N);
label("I.16", (2.95,1.55), E);
