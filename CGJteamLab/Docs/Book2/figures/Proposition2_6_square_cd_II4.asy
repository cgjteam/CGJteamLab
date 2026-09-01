settings.outformat = "pdf";
size(11.5cm,0);
defaultpen(fontsize(10pt));

pen mainpen = black + 0.9bp;
pen cutpen = black + 0.8bp;
pen fillA = gray(0.94);
pen fillB = gray(0.89);
pen fillC = gray(0.97);

void dotlabel(string s, pair P, pair dir=NE) {
  dot(P, black);
  label("$"+s+"$", P, dir);
}

real a=2.35; // diagrammatic CB
real b=2.85; // diagrammatic BD
real s=a+b;
pair C=(0,0), B=(a,0), D=(s,0);
pair C1=(0,s), D1=(s,s);
pair V=(a,s), H=(0,a), X=(a,a), R=(s,a);

filldraw(C--B--X--H--cycle, fillA, mainpen); // Sq(BC)
filldraw(B--D--R--X--cycle, fillB, mainpen); // Rect(CB,BD)
filldraw(H--X--V--C1--cycle, fillB, mainpen); // Rect(CB,BD)
filldraw(X--R--D1--V--cycle, fillC, mainpen); // Sq(BD)

draw(B--V, cutpen);
draw(H--R, cutpen);

dotlabel("C",C,SE);
dotlabel("B",B,S);
dotlabel("D",D,SW);

label("$S_{BC}$", (C+X)/2);
label("$R$", (B+R)/2);
label("$R$", (H+V)/2);
label("$S_{BD}$", (X+D1)/2);

label("$\mathrm{Sq}(CD)$", (C1+D1)/2+(0,0.45), N);
label("II.4 on $C-B-D$", (C+D)/2+(0,-0.9), S);
