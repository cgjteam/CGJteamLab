// Proposition2_7_II4_normal_form.asy
// II.4 normal form consumed by Proposition II.7.
// ASCII-only source.

settings.outformat = "pdf";
size(11.8cm,0);
defaultpen(fontsize(10pt));

pen mainpen = black+0.9bp;
pen cutpen = black+0.65bp;
pen fillS = gray(0.94);
pen fillX = gray(0.86);
pen fillT = gray(0.97);

// A-C-B along the lower side of W.  Qualitative dimensions only.
real a=2.5;
real b=3.8;
real w=a+b;
pair A=(0,0), C=(a,0), B=(w,0);
pair D=(0,w), P=(a,w), E=(w,w);
pair Q=(a,a), L=(0,a), R=(w,a);

fill(A--C--Q--L--cycle, fillS);
fill(C--B--R--Q--cycle, fillX);
fill(L--Q--P--D--cycle, fillX);
fill(Q--R--E--P--cycle, fillT);

draw(A--B--E--D--cycle, mainpen);
draw(C--P, cutpen);
draw(L--R, cutpen);

for(pair P0 : new pair[] {A,C,B}) dot(P0, black);
label("$A$",A,S);
label("$C$",C,S);
label("$B$",B,S);

label("$S$", (A+Q)/2);
label("$X$", (C+R)/2);
label("$X$", (L+P)/2);
label("$T$", (Q+E)/2);
label("$W=\mathrm{Sq}(AB)$", (D+E)/2, N);
label("$W\sim_{\rm sc}(X+S)+(X+T)$", (w/2,-0.72), S);
