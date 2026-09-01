import graph;
settings.outformat = "pdf";
size(680,0);
defaultpen(fontsize(8.5pt)+black);

pen mainpen = black+0.8bp;
pen auxpen = black+0.65bp;
pen dashpen = dashed+black+0.55bp;
pen lightpen = gray(0.72)+0.45bp;
pen fillpen = gray(0.93);

void dotlabel(string s, pair P, pair dir=NE) {
  dot(P, black);
  label("$"+s+"$", P, dir);
}

// ------------------------------------------------------------------
// Left panel: II.6 specialized to D-E-A-F.
// This is the standard II.6 gnomon with the substitution
// (A,C,B,D) -> (D,E,A,F).
// ------------------------------------------------------------------
pair shL=(0,0);
pair D=shL+(0,4), E=shL+(2,4), A=shL+(4,4), F=shL+(6,4);
pair U=shL+(2,0), V=shL+(4,0), W=shL+(6,0);
pair K=shL+(0,2), L=shL+(2,2), H=shL+(4,2), M=shL+(6,2);

fill(E--F--M--L--cycle, fillpen);
fill(H--M--W--V--cycle, fillpen);

draw(E--F--W--U--cycle, mainpen);
draw(D--F, mainpen);
draw(U--F, auxpen);
draw(A--V, auxpen);
draw(K--M, auxpen);
draw(D--K, auxpen);
draw(L--H--V--U--cycle, dashpen);

dotlabel("D",D,N); dotlabel("E",E,N); dotlabel("A",A,N); dotlabel("F",F,N);
dot(U); dot(V); dot(W); dot(K); dot(L); dot(H); dot(M);

label("$\mathrm{Sq}(AE)$", (3.0,1.15));
label("$\mathrm{Rect}(DF,AF)$", (5.0,2.85));
label("$\mathrm{Sq}(EF)$", (4.0,-0.55), S);
label("II.6", (3.0,5.05), N);

// Equal-half marks for DE and EA.
draw((1,3.90)--(1,4.10), auxpen);
draw((3,3.90)--(3,4.10), auxpen);

// ------------------------------------------------------------------
// Right panel: I.47 on the right triangle EAB.
// Three squares are erected outward from the triangle.
// ------------------------------------------------------------------
pair shR=(9.0,0.35);
pair A2=shR+(0,0), B2=shR+(3.3,0), E2=shR+(0,2.5);

draw(E2--A2--B2--cycle, mainpen);

// Square on AE, outward to the left.
pair qAE=(-2.5,0);
draw(A2--E2--(E2+qAE)--(A2+qAE)--cycle, auxpen);
label("$\mathrm{Sq}(AE)$", A2+(-1.25,1.25));

// Square on AB, outward downward.
pair qAB=(0,-3.3);
draw(A2--B2--(B2+qAB)--(A2+qAB)--cycle, auxpen);
label("$\mathrm{Sq}(AB)$", A2+(1.65,-1.65));

// Square on EB, outward away from A.
pair dEB=B2-E2;
pair nEB=unit((dEB.y,-dEB.x));
real lenEB=length(dEB);
pair qEB=lenEB*nEB;
draw(E2--B2--(B2+qEB)--(E2+qEB)--cycle, auxpen);
label("$\mathrm{Sq}(EB)$", (E2+B2+qEB)/2);

dotlabel("E",E2,NW); dotlabel("A",A2,SW); dotlabel("B",B2,SE);
label("I.47", shR+(0.35,4.70), N);
label("$EF\cong EB$", shR+(1.25,-4.15), S);
