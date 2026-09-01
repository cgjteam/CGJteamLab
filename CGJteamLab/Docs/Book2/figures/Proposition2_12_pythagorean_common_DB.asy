// Proposition2_12_pythagorean_common_DB.asy
// Euclid Book II, Proposition 12.
// Two right triangles sharing DB and one square representative on DB.
// ASCII-only Asymptote source.

settings.outformat = "pdf";
size(14cm,0);
defaultpen(fontsize(10pt));

pen mainpen = black + 0.9bp;
pen auxpen = black + 0.60bp;
pen lightpen = gray(0.62) + 0.55bp;

void dotlabel(string s, pair P, pair dir=NE) {
  dot(P, black);
  label("$"+s+"$", P, dir);
}

void rightmark(pair O, pair u, pair v, real s=0.24) {
  pair eu = unit(u);
  pair ev = unit(v);
  draw(O+s*eu--O+s*(eu+ev)--O+s*ev, mainpen);
}

pair D=(0,0);
pair A=(2.15,0);
pair C=(6.10,0);
pair B=(0,3.25);

// The two right triangles DAB and DCB.
draw(D--C, mainpen);
draw(B--D, mainpen);
draw(B--A, mainpen);
draw(B--C, mainpen);
rightmark(D,A-D,B-D);

// A single visible square on DB, emphasizing the common Pythagorean summand.
pair U=(-3.25,0);
pair V=(-3.25,3.25);
draw(D--B--V--U--cycle, lightpen);
label("$\mathrm{Sq}(DB)$", (-1.63,1.62));

// Points.
dotlabel("D",D,SE);
dotlabel("A",A,S);
dotlabel("C",C,SE);
dotlabel("B",B,NE);

label("$\triangle DAB$", (1.05,1.15));
label("$\triangle DCB$", (3.65,1.95));
label("$D-A-C$", (4.15,-0.48), S);
