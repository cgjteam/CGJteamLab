import graph;
settings.outformat = "pdf";
size(500,0);
defaultpen(fontsize(9pt)+black);

pen mainpen = black+0.85bp;
pen cutpen = black+1.05bp;
pen dashpen = dashed+black+0.60bp;
pen lightpen = gray(0.58)+0.55bp;

void dotlabel(string s, pair P, pair dir=NE) {
  dot(P, black);
  label("$"+s+"$", P, dir);
}

// Generic rectangle cut used internally by II.11.
// B-M-C is transported to D-L-E; the cut ML meets diagonal DC at N.
pair B=(0,4), M=(2.25,4), C=(6.2,4);
pair D=(0,0), L=(2.25,0), E=(6.2,0);
pair N=(2.25,4*2.25/6.2);

draw(B--C--E--D--cycle, mainpen);
draw(M--L, cutpen);
draw(D--C, dashpen);

// Lightly emphasize the two configured cut pieces.
draw(B--M, lightpen);
draw(D--L, lightpen);
draw(M--C, lightpen);
draw(L--E, lightpen);

dotlabel("B",B,NW);
dotlabel("M",M,N);
dotlabel("C",C,NE);
dotlabel("D",D,SW);
dotlabel("L",L,S);
dotlabel("E",E,SE);
dotlabel("N",N,NE);

label("$B-M-C$", (3.1,4.48), N);
label("$D-L-E$", (3.1,-0.46), S);
label("$D-N-C$", (4.3,2.15), SE);
label("$M-N-L$", (2.65,1.82), E);
