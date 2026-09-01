import graph;
settings.outformat = "pdf";
size(470,0);
defaultpen(fontsize(9pt)+black);

pen mainpen = black+0.9bp;
pen auxpen = black+0.65bp;
pen lightpen = gray(0.62)+0.55bp;

void dotlabel(string s, pair P, pair dir=NE) {
  dot(P, black);
  label("$"+s+"$", P, dir);
}

void rightmark(pair O, pair u, pair v, real s=0.24) {
  pair eu=unit(u);
  pair ev=unit(v);
  draw(O+s*eu--O+s*(eu+ev)--O+s*ev, mainpen);
}

// Square ABCD with E the midpoint of DA.
// The side EA is extended beyond A to X for the I.16 argument.
pair A=(0,0), B=(4.8,0), C=(4.8,4.0), D=(0,4.0);
pair E=(0,2.0), X=(0,-2.0);

// Square and the right triangle EAB.
draw(A--B--C--D--cycle, mainpen);
draw(E--B, mainpen);
draw(E--X, auxpen);
rightmark(A,E-A,B-A,0.27);

// Midpoint marks on DE and EA.
draw((-0.12,3.0)--(0.12,3.0), auxpen);
draw((-0.12,1.0)--(0.12,1.0), auxpen);

// Light arcs indicating the two angles compared by I.16.
draw(arc(B,0.55,150,180), lightpen);
draw(arc(A,0.72,270,360), lightpen);

dotlabel("D",D,NW);
dotlabel("E",E,W);
dotlabel("A",A,SW);
dotlabel("X",X,SW);
dotlabel("B",B,SE);
dotlabel("C",C,NE);

label("$D-E-A-X$", (-0.65,1.0), W);
label("I.16", (2.85,-0.65));
