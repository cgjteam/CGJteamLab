settings.outformat = "pdf";
size(13cm,0);
defaultpen(fontsize(10pt));

pen mainpen = black + 0.9bp;
pen cutpen = black + 0.75bp;
pen lightpen = gray(0.60) + 0.55bp;
pen fillA = gray(0.94);
pen fillB = gray(0.89);
pen fillC = gray(0.97);

void dotlabel(string s, pair P, pair dir=NE) {
  dot(P, black);
  label("$"+s+"$", P, dir);
}

void tick(pair A, pair B, int n=1) {
  pair M=(A+B)/2;
  pair v=unit(B-A);
  pair w=(-v.y,v.x);
  for (int k=0; k<n; ++k) {
    real d=(k-(n-1)/2.0)*0.11;
    draw(M+d*v-0.09*w--M+d*v+0.09*w, mainpen);
  }
}

// A-C-B-D with AC ~= CB. The rectangle height is represented by BD.
pair A=(0,0), C=(2.25,0), B=(4.50,0), D=(7.20,0);
real h=2.70;
pair A1=A+(0,h), C1=C+(0,h), B1=B+(0,h), D1=D+(0,h);

filldraw(A--C--C1--A1--cycle, fillA, mainpen);
filldraw(C--B--B1--C1--cycle, fillB, mainpen);
filldraw(B--D--D1--B1--cycle, fillC, mainpen);

draw(C--C1, cutpen);
draw(B--B1, cutpen);

tick(A,C,1);
tick(C,B,1);

dotlabel("A",A,SE);
dotlabel("C",C,S);
dotlabel("B",B,S);
dotlabel("D",D,SW);

label("$R_{AC}$", (A+C1)/2);
label("$R_{CB}$", (C+B1)/2);
label("$S_{BD}$", (B+D1)/2);

label("$AC\cong CB$", (C+B)/2+(0,-0.55), S);
label("$\mathrm{Rect}(AD,BD)$", (A1+D1)/2+(0,0.45), N);
label("II.3 at $B$, then II.1 at $C$", (A+D)/2+(0,-1.0), S);
