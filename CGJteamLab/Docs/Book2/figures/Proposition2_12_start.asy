// Proposition2_12_start.asy
// Euclid Book II, Proposition 12.
// Classical starting configuration.
// ASCII-only Asymptote source.

settings.outformat = "pdf";
size(13cm,0);
defaultpen(fontsize(10pt));

pen mainpen = black + 0.9bp;
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

// D-A-C are collinear, and BD is perpendicular to the carrier AC.
pair D=(0,0);
pair A=(2.15,0);
pair C=(6.20,0);
pair B=(0,3.45);

// Main triangle and produced side.
draw(D--C, mainpen);
draw(B--A--C, mainpen);
draw(B--D, mainpen);

// Right angle at D.
rightmark(D,A-D,B-D);

// Qualitative obtuse-angle arc only; no numerical angle measure is used.
real a1=degrees(atan2((B-A).y,(B-A).x));
real a2=degrees(atan2((C-A).y,(C-A).x));
draw(arc(A,0.70,a2,a1), lightpen);

// Points.
dotlabel("D",D,SW);
dotlabel("A",A,S);
dotlabel("C",C,SE);
dotlabel("B",B,NW);

label("$D-A-C$", (4.15,-0.45), S);
label("$BD\perp AC$", (-0.60,1.55), W);
